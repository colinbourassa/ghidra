/* ###
 * IP: GHIDRA
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 * 
 *      http://www.apache.org/licenses/LICENSE-2.0
 * 
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package ghidra.app.util.bin.format.aout;

import java.io.IOException;
import java.io.InputStream;
import java.util.*;

import ghidra.app.util.Option;
import ghidra.app.util.bin.BinaryReader;
import ghidra.app.util.bin.ByteProvider;
import ghidra.app.util.bin.format.aout.UnixAoutHeader.ExecutableType;
import ghidra.app.util.importer.MessageLog;
import ghidra.app.util.opinion.AbstractProgramWrapperLoader;
import ghidra.app.util.opinion.LoadSpec;
import ghidra.framework.store.LockException;
import ghidra.program.flatapi.FlatProgramAPI;
import ghidra.program.model.address.Address;
import ghidra.program.model.address.AddressOverflowException;
import ghidra.program.model.address.AddressSpace;
import ghidra.program.model.lang.LanguageCompilerSpecPair;
import ghidra.program.model.listing.Function;
import ghidra.program.model.listing.Program;
import ghidra.program.model.mem.MemoryAccessException;
import ghidra.program.model.mem.MemoryBlock;
import ghidra.program.model.mem.MemoryConflictException;
import ghidra.program.model.symbol.Namespace;
import ghidra.program.model.symbol.RefType;
import ghidra.program.model.symbol.SourceType;
import ghidra.program.model.symbol.Symbol;
import ghidra.util.exception.CancelledException;
import ghidra.util.exception.DuplicateNameException;
import ghidra.util.exception.InvalidInputException;
import ghidra.util.task.TaskMonitor;

/**
 * A {@link Loader} for processing UNIX-style A.out executables
 *
 * This style was also used by UNIX-like systems such as SunOS, BSD, and
 * VxWorks, as well as some early distributions of Linux. Although there
 * do exist implementations of A.out with 64-bit and GNU extensions, this
 * loader does not currently support them.
 *
 * @see <a href="https://wiki.osdev.org/A.out">OSDev.org A.out</a>
 * @see <a href="https://man.freebsd.org/cgi/man.cgi?a.out(5)">FreeBSD manpage</a>
 */
public class UnixAoutLoader extends AbstractProgramWrapperLoader {

	@Override
	public String getName() {
		return "UNIX A.out executable";
	}
	
	@Override
	public boolean supportsLoadIntoProgram() {
		return true;
	}

	@Override
	public Collection<LoadSpec> findSupportedLoadSpecs(ByteProvider provider) throws IOException {
		List<LoadSpec> loadSpecs = new ArrayList<>();

		// Attempt to parse the header as both little- and big-endian.
		// It is likely that only one of these will produce sensible values.
		UnixAoutHeader hdrBE = new UnixAoutHeader(provider, false);
		UnixAoutHeader hdrLE = new UnixAoutHeader(provider, true);
		boolean beValid = false;
		
		if (hdrBE.isValid()) {
			final String lang = hdrBE.getLanguageSpec();
			final String comp = hdrBE.getCompilerSpec();
			loadSpecs.add(new LoadSpec(this, 0, new LanguageCompilerSpecPair(lang, comp), true));
			beValid = true;
		}
		if (hdrLE.isValid()) {
			final String lang = hdrLE.getLanguageSpec();
			final String comp = hdrLE.getCompilerSpec();
			loadSpecs.add(new LoadSpec(this, 0, new LanguageCompilerSpecPair(lang, comp), !beValid));			
		}
		
		return loadSpecs;
	}

	@Override
	protected void load(ByteProvider provider, LoadSpec loadSpec, List<Option> options,
			Program program, TaskMonitor monitor, MessageLog log)
			throws CancelledException, IOException {

		FlatProgramAPI api = new FlatProgramAPI(program, monitor);
		final boolean bigEndian = program.getLanguage().isBigEndian();
		UnixAoutHeader header = new UnixAoutHeader(provider, !bigEndian);
		final String filename = provider.getFile().getName();

		final long textSize = header.getTextSize();
		final long dataSize = header.getDataSize();
		long bssSize = header.getBssSize();
		final boolean isOverlay = (header.getExecutableType() == ExecutableType.OMAGIC);
		
		Namespace namespace = null;
		try {
			namespace = api.createNamespace(program.getGlobalNamespace(), filename);
		} catch (DuplicateNameException | InvalidInputException e1) {
			e1.printStackTrace();
		}
		
		MemoryBlock textBlock = null;
		MemoryBlock dataBlock = null;
		MemoryBlock bssBlock = null;
		AddressSpace textAddrSpace = null;
		AddressSpace dataAddrSpace = null;
		AddressSpace bssAddrSpace = null;

		// Create the .text segment based on its reported starting address and size
		if (textSize > 0) {
			Address textAddr = program.getAddressFactory().getDefaultAddressSpace().getAddress(header.getTextAddr());
			try {
				InputStream textStream = provider.getInputStream(header.getTextOffset());
				textBlock = program.getMemory().createInitializedBlock(
					filename + ".text", textAddr, textStream, textSize, monitor, isOverlay);
				textAddrSpace = textBlock.getStart().getAddressSpace();
				textBlock.setRead(true);
				textBlock.setWrite(false);
				textBlock.setExecute(true);
			} catch (LockException | IllegalArgumentException | MemoryConflictException | AddressOverflowException e) {
				e.printStackTrace();
			}
		}
		
		// Create the .data segment based on its reported starting address and size		
		if (dataSize > 0) {
			Address dataAddr = program.getAddressFactory().getDefaultAddressSpace().getAddress(header.getDataAddr());
			try {
				InputStream dataStream = provider.getInputStream(header.getDataOffset());
				dataBlock = program.getMemory().createInitializedBlock(
					filename + ".data", dataAddr, dataStream, dataSize, monitor, isOverlay);
				dataAddrSpace = dataBlock.getStart().getAddressSpace();
				dataBlock.setRead(true);
				dataBlock.setWrite(true);
				dataBlock.setExecute(false);
			} catch (LockException | IllegalArgumentException | MemoryConflictException | AddressOverflowException e) {
				e.printStackTrace();
			}
		}

		BinaryReader reader = new BinaryReader(provider, !bigEndian);

		Vector<UnixAoutSymbolTableEntry> symTab =
			getSymbolTable(reader, header.getSymOffset(), header.getSymSize(), header.getStrOffset());

		Vector<UnixAoutRelocationTableEntry> textRelocTab =
			getRelocationTable(reader, header.getTextRelocOffset(), header.getTextRelocSize());

		Vector<UnixAoutRelocationTableEntry> dataRelocTab =
			getRelocationTable(reader, header.getDataRelocOffset(), header.getDataRelocSize());

		Hashtable<String,Long> possibleBssSymbols = new Hashtable<String,Long>();
		Hashtable<Address,String> localFunctions = new Hashtable<Address,String>();

		// Process the symbol table by applying labels to identify any symbols whose addresses are given		
		for (Integer i = 0; i < symTab.size(); i++) {
			UnixAoutSymbolTableEntry symTabEntry = symTab.elementAt(i);
			try {
				if (symTabEntry.value != 0) {
					if (symTabEntry.type == UnixAoutSymbolTableEntry.SymbolType.N_TEXT) {
						if (symTabEntry.isExt) {
							// Save the entry point to this function in a list. Disassembly should wait until
							// after we've processed the relocation tables.
							Address funcAddr = textAddrSpace.getAddress(symTabEntry.value);
							localFunctions.put(funcAddr, symTabEntry.name);
						}
					} else if (symTabEntry.type == UnixAoutSymbolTableEntry.SymbolType.N_DATA) {
						api.createLabel(dataAddrSpace.getAddress(symTabEntry.value), symTabEntry.name,
							namespace, true, SourceType.IMPORTED);
						
					} else if (symTabEntry.type == UnixAoutSymbolTableEntry.SymbolType.N_BSS) {
						api.createLabel(bssAddrSpace.getAddress(symTabEntry.value), symTabEntry.name,
							namespace, true, SourceType.IMPORTED);
						
					} else if (symTabEntry.type == UnixAoutSymbolTableEntry.SymbolType.N_UNDF) {
						// This is a special case given by the A.out spec: if the linker cannot find this
						// symbol in any of the other binary files, then the fact that it is marked as
						// N_UNDF but has a non-zero value means that its value should be interpreted as
						// a size, and the linker should reserve space in .bss for it.
						possibleBssSymbols.put(symTabEntry.name, symTabEntry.value);
					}
				}
			} catch (Exception e) {
				e.printStackTrace();
			}
		}

		// Add up the sizes of all the symbols that are supposed to be allocated
		// in .bss, and ensure that our .bss segment size can accommodate them.
		// Until we search the global symbol table for the symbols in the
		// 'possibleBssSymbols' list (which will happen as we walk the relocation
		// table, below), we won't know whether these symbols exist in another
		// binary file that was previously loaded, or, instead, if we'll need to
		// mimic the linker behavior and assign them space in .bss.
		Long requiredBssSize = (long) 0;
		for (Long symbolSize : possibleBssSymbols.values()) {
			requiredBssSize += symbolSize;				
		}
		
		if (requiredBssSize > bssSize) {
			bssSize = requiredBssSize;
		}

		if (bssSize > 0) {
			try {
				bssBlock = api.createMemoryBlock(filename + ".bss",
					api.toAddr(header.getBssAddr()), null, bssSize, isOverlay);
				bssAddrSpace = bssBlock.getStart().getAddressSpace();
			} catch (Exception e) {
				e.printStackTrace();
			}
		}

		// Keep track of the next available location in .bss
		long bssLocation = header.getBssAddr();
		
		///////////////////////////////////////
		// Process the .text relocation table
        ///////////////////////////////////////
		for (Integer i = 0; i < textRelocTab.size(); i++) {

		    UnixAoutRelocationTableEntry relocationEntry = textRelocTab.elementAt(i);
		    if (relocationEntry.symbolNum < symTab.size()) {

		        UnixAoutSymbolTableEntry symbolEntry = symTab.elementAt((int)relocationEntry.symbolNum);
		        AddressSpace addrSpace = textBlock.getStart().getAddressSpace();
		        Address relocAddr = addrSpace.getAddress(relocationEntry.address + header.getTextAddr());

		        // If this symbol's N_EXT flag is clear, then we didn't mark it as a function when
		        // we were processing the symbol table (above). This is because special symbols like
		        // "gcc2_compiled", "___gnu_compiled_c", and names of object files are in the symbol
		        // table for this segment, but do not point to disassemblable code. However, since
		        // there is now a reference from the relocation table, we should be able to
		        // disassemble at its address. Save the address for disassembly later.
		        if (!symbolEntry.isExt) {
		            Address funcAddr = textAddrSpace.getAddress(symbolEntry.value);
		            localFunctions.put(funcAddr, symbolEntry.name);
		        }

		        if (relocationEntry.extern && textBlock.contains(relocAddr)) {

		            List<Function> funcs = api.getCurrentProgram().getListing().getGlobalFunctions(symbolEntry.name);
		            List<Symbol> symbolsGlobal = api.getSymbols(symbolEntry.name, null);
		            List<Symbol> symbolsLocal = api.getSymbols(symbolEntry.name, namespace);

		            if (funcs.size() > 0) {
		                Address funcAddr = funcs.get(0).getEntryPoint();
		                fixAddress(textBlock, relocAddr, funcAddr,
		                        relocationEntry.pcRelativeAddressing, bigEndian, relocationEntry.pointerLength);

		            } else if (symbolsGlobal.size() > 0) {
		                Address globalSymbolAddr = symbolsGlobal.get(0).getAddress();
		                fixAddress(textBlock, relocAddr, globalSymbolAddr,
		                        relocationEntry.pcRelativeAddressing, bigEndian, relocationEntry.pointerLength);

		            } else if (symbolsLocal.size() > 0) {
		                Address localSymbolAddr = symbolsLocal.get(0).getAddress();
		                fixAddress(textBlock, relocAddr, localSymbolAddr,
		                        relocationEntry.pcRelativeAddressing, bigEndian, relocationEntry.pointerLength);

		            } else if (possibleBssSymbols.containsKey(symbolEntry.name)) {
		                try {
		                    Address bssSymbolAddress = bssBlock.getStart().getAddressSpace().getAddress(bssLocation);
		                    long bssSymbolSize = possibleBssSymbols.get(symbolEntry.name);
		                    api.createLabel(bssSymbolAddress,
		                            symbolEntry.name, namespace, true, SourceType.IMPORTED);
		                    fixAddress(textBlock, relocAddr, bssSymbolAddress,
		                            relocationEntry.pcRelativeAddressing, bigEndian, relocationEntry.pointerLength);
		                    program.getReferenceManager().addMemoryReference(
		                            relocAddr, bssSymbolAddress, RefType.DATA, SourceType.IMPORTED, 0);
		                    bssLocation += bssSymbolSize;

		                } catch (Exception e) {
		                    e.printStackTrace();
		                }
		            } else {
		                log.appendMsg("Symbol '" + symbolEntry.name +
		                        "' was not found and was not a candidate for allocation in .bss.");
		            }
		        }
		    } else {
		        log.appendMsg("Symbol number " + relocationEntry.symbolNum +
		                " is beyond symbol table length of " + symTab.size());
		    }
		}
		
		///////////////////////////////////////
		// Process the .data relocation table
        ///////////////////////////////////////
		for (Integer i = 0; i < dataRelocTab.size(); i++) {

		    UnixAoutRelocationTableEntry relocationEntry = dataRelocTab.elementAt(i);
		    if (relocationEntry.symbolNum < symTab.size()) {

		        UnixAoutSymbolTableEntry symbolEntry = symTab.elementAt((int)relocationEntry.symbolNum);
		        AddressSpace addrSpace = dataBlock.getStart().getAddressSpace();
		        Address relocAddr = addrSpace.getAddress(relocationEntry.address + header.getDataAddr());

		        if (dataBlock.contains(relocAddr)) {

		            List<Function> funcs = api.getCurrentProgram().getListing().getGlobalFunctions(symbolEntry.name);
		            List<Symbol> symbolsGlobal = api.getSymbols(symbolEntry.name, null);
		            List<Symbol> symbolsLocal = api.getSymbols(symbolEntry.name, namespace);

		            if (funcs.size() > 0) {
		                Address funcAddr = funcs.get(0).getEntryPoint();
		                fixAddress(dataBlock, relocAddr, funcAddr,
		                        relocationEntry.pcRelativeAddressing, bigEndian, relocationEntry.pointerLength);

		            } else if (symbolsGlobal.size() > 0) {
		                Address globalSymbolAddr = symbolsGlobal.get(0).getAddress();
		                fixAddress(dataBlock, relocAddr, globalSymbolAddr,
		                        relocationEntry.pcRelativeAddressing, bigEndian, relocationEntry.pointerLength);

		            } else if (symbolsLocal.size() > 0) {
		                Address localSymbolAddr = symbolsLocal.get(0).getAddress();
		                fixAddress(dataBlock, relocAddr, localSymbolAddr,
		                        relocationEntry.pcRelativeAddressing, bigEndian, relocationEntry.pointerLength);

		            } else if (possibleBssSymbols.containsKey(symbolEntry.name)) {
		                try {
		                    Address bssSymbolAddress = bssBlock.getStart().getAddressSpace().getAddress(bssLocation);
		                    api.createLabel(bssSymbolAddress,
		                            symbolEntry.name, namespace, true, SourceType.IMPORTED);
		                    fixAddress(dataBlock, relocAddr, bssSymbolAddress,
		                            relocationEntry.pcRelativeAddressing, bigEndian, relocationEntry.pointerLength);
		                    program.getReferenceManager().addMemoryReference(
		                            relocAddr, bssSymbolAddress, RefType.DATA, SourceType.IMPORTED, 0);
		                    bssLocation += possibleBssSymbols.get(symbolEntry.name);

		                } catch (Exception e) {
		                    e.printStackTrace();
		                }
		            } else {
		                log.appendMsg("Symbol '" + symbolEntry.name +
		                        "' was not found and was not a candidate for allocation in .bss.");
		            }
		        }
		    } else {
	              log.appendMsg("Symbol number " + relocationEntry.symbolNum +
	                        " is beyond symbol table length of " + symTab.size());
		    }
		}

		// Now that all relocation addresses have been rewritten, it's safe to start disassembly
		// at all the known function entry points.
		for (Address funcAddr : localFunctions.keySet()) {
			api.disassemble(funcAddr);
			api.createFunction(funcAddr, localFunctions.get(funcAddr));
		}
		
		if ((header.getExecutableType() != UnixAoutHeader.ExecutableType.OMAGIC) &&
		    (header.getExecutableType() != UnixAoutHeader.ExecutableType.CMAGIC)) {
		    api.disassemble(textAddrSpace.getAddress(header.getEntryPoint()));
		}
	}
	
	/**
	 * Rewrites the pointer at the specified location to instead point to the
	 * provided address.
	 * @param block Memory block in which the pointer to be rewritten exists.
	 * @param pointerLocation Address at which the pointer to be rewritten is stored.
	 * @param newAddress Address that is to be written as the new pointer target.
	 * @param isPcRelative Indicates whether the address is program counter relative,
	 *  in which case the pointer will be written with the delta between the pointer
	 *  location and the new destination address. Otherwise it will be written with
	 *  the absolute address.
	 * @param isBigEndian True if the program (and therefore the byte order of the
	 *  pointer) is big endian. False if little endian.
	 * @param pointerSize 1, 2, and 4-byte pointers are supported.
	 */
	private void fixAddress(MemoryBlock block, Address pointerLocation, Address newAddress,
			boolean isPcRelative, boolean isBigEndian, int pointerSize) {

		final long value = isPcRelative ?
				(newAddress.getOffset() - pointerLocation.getOffset()) : newAddress.getOffset();

		byte[] valueBytes = new byte[pointerSize];

		for (int i = 0; i < pointerSize; i++) {
			int shiftCount = isBigEndian ? (24 - (i * 8)) : (i * 8);
			valueBytes[i] = (byte)((value >> shiftCount) & 0xff);
		}
		try {
			block.putBytes(pointerLocation, valueBytes);
		} catch (MemoryAccessException e) {
			e.printStackTrace();
		}
	}
	
	/**
	 * Reads a single relocation table for either text or data relocations, depending
	 * on the offset/length provided.
	 * @param reader Source of file data
	 * @param offset File byte offset to the start of the relocation table
	 * @param len Length of the relocation table in bytes
	 * @return Vector of relocation table entries
	 */
	private Vector<UnixAoutRelocationTableEntry> getRelocationTable(BinaryReader reader, long offset, long len) {
		Vector<UnixAoutRelocationTableEntry> relocTable = new Vector<UnixAoutRelocationTableEntry>();
		reader.setPointerIndex(offset);

		try {
			while (reader.getPointerIndex() < (offset + len)) {
				long address = reader.readNextUnsignedInt();
				long flags = reader.readNextUnsignedInt();
				relocTable.add(new UnixAoutRelocationTableEntry(address, flags, reader.isBigEndian()));
			}
		} catch (IOException e) {
			e.printStackTrace();
		}

		return relocTable;
	}

	/**
	 * Reads all the symbol table entries from the file, returning their representation.
	 * @param reader Source of file data
	 * @param offset File byte offset to the start of the symbol table
	 * @param len Length of the symbol table in bytes
	 * @param strTabBaseOffset File byte offset to the start of the string table (containing symbol names)
	 * @return Vector of symbol table entries
	 */
	private Vector<UnixAoutSymbolTableEntry> getSymbolTable(BinaryReader reader, long offset, long len, long strTabBaseOffset) {
		Vector<UnixAoutSymbolTableEntry> symtab = new Vector<UnixAoutSymbolTableEntry>();
		reader.setPointerIndex(offset);

		try {
			// read each symbol table entry
			while (reader.getPointerIndex() < (offset + len)) {
				long strOffset = reader.readNextUnsignedInt();
				byte typeByte = reader.readNextByte();
				byte otherByte = reader.readNextByte();
				short desc = reader.readNextShort();
				long value = reader.readNextUnsignedInt();
				symtab.add(new UnixAoutSymbolTableEntry(strOffset, typeByte, otherByte, desc, value));
			}

			// lookup and set each string table symbol name
			for (Integer i = 0; i < symtab.size(); i++) {
				String symstr = reader.readAsciiString(strTabBaseOffset + symtab.get(i).nameStringOffset);
				symtab.get(i).name = symstr;
			}

		} catch (IOException e) {
			e.printStackTrace();
		}

		return symtab;
	}
}
