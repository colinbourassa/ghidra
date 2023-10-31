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
package ghidra.app.util.opinion;

import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import ghidra.app.util.bin.ByteProvider;
import ghidra.app.util.bin.format.unixaout.UnixAoutHeader;
import ghidra.app.util.bin.format.unixaout.UnixAoutRelocation;
import ghidra.app.util.bin.format.unixaout.UnixAoutRelocationTable;
import ghidra.app.util.bin.format.unixaout.UnixAoutStringTable;
import ghidra.app.util.bin.format.unixaout.UnixAoutSymbol;
import ghidra.app.util.bin.format.unixaout.UnixAoutSymbolTable;
import ghidra.app.util.importer.MessageLog;
import ghidra.framework.store.LockException;
import ghidra.program.database.function.OverlappingFunctionException;
import ghidra.program.database.mem.FileBytes;
import ghidra.program.model.address.Address;
import ghidra.program.model.address.AddressOverflowException;
import ghidra.program.model.address.AddressSet;
import ghidra.program.model.address.AddressSpace;
import ghidra.program.model.listing.FunctionManager;
import ghidra.program.model.listing.Program;
import ghidra.program.model.mem.Memory;
import ghidra.program.model.mem.MemoryAccessException;
import ghidra.program.model.mem.MemoryBlock;
import ghidra.program.model.mem.MemoryConflictException;
import ghidra.program.model.reloc.Relocation.Status;
import ghidra.program.model.reloc.RelocationTable;
import ghidra.program.model.symbol.SourceType;
import ghidra.program.model.symbol.Symbol;
import ghidra.program.model.symbol.SymbolIterator;
import ghidra.program.model.symbol.SymbolTable;
import ghidra.program.model.util.CodeUnitInsertionException;
import ghidra.util.DataConverter;
import ghidra.util.MonitoredInputStream;
import ghidra.util.exception.CancelledException;
import ghidra.util.exception.DuplicateNameException;
import ghidra.util.exception.InvalidInputException;
import ghidra.util.task.TaskMonitor;

public class UnixAoutProgramLoader {
	private final static String BLOCK_SOURCE_NAME = "Unix Aout Loader";
	private final static String EXTERNAL_BLOCK_COMMENT = "NOTE: This block is artificial and is used to make relocations work correctly";
	private final int EXTERNAL_BLOCK_MIN_SIZE = 0x10000; // 64K

	public final static String dot_text = ".text";
	public final static String dot_data = ".data";
	public final static String dot_bss = ".bss";
	public final static String dot_rel_text = ".rel.text";
	public final static String dot_rel_data = ".rel.data";
	public final static String dot_strtab = ".strtab";
	public final static String dot_symtab = ".symtab";

	private final Program program;
	private final TaskMonitor monitor;
	private final MessageLog log;
	private final UnixAoutHeader header;

	private boolean prefixSectionNamesWithFileName;

	private FileBytes fileBytes;

	private MemoryBlock blockHeader;
	private MemoryBlock blockText;
	private MemoryBlock blockData;
	private MemoryBlock blockBss;
	private MemoryBlock blockExternal;
	private MemoryBlock blockStrtab;
	private MemoryBlock blockSymtab;
	private MemoryBlock blockRelText;
	private MemoryBlock blockRelData;

	private Address nextExternalAddress;

	private UnixAoutRelocationTable relText;
	private UnixAoutRelocationTable relData;
	private UnixAoutSymbolTable symtab;
	private UnixAoutStringTable strtab;

	private Map<String, Long> possibleBssSymbols = new HashMap<>();
	private int extraBssSize = 0;
	private int undefinedSymbolCount = 0;

	public UnixAoutProgramLoader(Program program, UnixAoutHeader header, TaskMonitor monitor, MessageLog log) {
		this.program = program;
		this.monitor = monitor;
		this.log = log;
		this.header = header;
	}

	public void loadAout(boolean prefixSectionNamesWithFileName) throws IOException, CancelledException {
		this.prefixSectionNamesWithFileName = prefixSectionNamesWithFileName;

		log.appendMsg(String.format("----- Loading %s -----", header.getReader().getByteProvider().getAbsolutePath()));
		log.appendMsg(String.format("Found a.out type %s.", header.getExecutableType().name()));

		final ByteProvider byteProvider = header.getReader().getByteProvider();

		try {
			buildTables(byteProvider);
			preprocessSymbolTable();
			loadSections(byteProvider);
			loadSymbols();
			applyRelocations(blockText, relText);
			applyRelocations(blockData, relData);
			markupSections();
		} catch (AddressOverflowException | InvalidInputException | CodeUnitInsertionException | DuplicateNameException
				| MemoryAccessException | LockException | IllegalArgumentException | MemoryConflictException e) {
			throw new RuntimeException(e);
		}
	}

	private void buildTables(ByteProvider byteProvider) throws IOException {
		if (header.getStrSize() > 0) {
			strtab = new UnixAoutStringTable(header.getReader(), header.getStrOffset(), header.getStrSize());
		}
		if (header.getSymSize() > 0) {
			symtab = new UnixAoutSymbolTable(header.getReader(), header.getSymOffset(), header.getSymSize(),
					strtab, log);
		}
		if (header.getTextRelocSize() > 0) {
			relText = new UnixAoutRelocationTable(header.getReader(), header.getTextRelocOffset(),
					header.getTextRelocSize(), symtab);
		}
		if (header.getDataRelocSize() > 0) {
			relData = new UnixAoutRelocationTable(header.getReader(), header.getDataRelocOffset(),
					header.getDataRelocSize(), symtab);
		}
	}

	private void preprocessSymbolTable() {
		if (symtab == null) {
			return;
		}

		boolean foundStabs = false;
		for (UnixAoutSymbol symbol : symtab) {
			switch (symbol.type) {
				case N_UNDF:
					if (symbol.value > 0) {
						// This is a special case given by the A.out spec: if the linker cannot find
						// this symbol in any of the other binary files, then the fact that it is
						// marked as N_UNDF but has a non-zero value means that its value should be
						// interpreted as a size, and the linker should reserve space in .bss for it.
						possibleBssSymbols.put(symbol.name, symbol.value);
					} else {
						undefinedSymbolCount++;
					}
					break;
				case N_STAB:
					if (!foundStabs) {
						foundStabs = true;
						log.appendMsg(dot_symtab, "File contains STABS.");
					}
					break;
				default:
					break;
			}
		}

		for (Long value : possibleBssSymbols.values()) {
			extraBssSize += value;
		}

		if (extraBssSize > 0) {
			log.appendMsg(dot_bss, String.format("Added %d bytes for N_UNDF symbols.", extraBssSize));
		}
	}

	private void loadSections(ByteProvider byteProvider) throws AddressOverflowException, IOException,
			CancelledException, LockException, IllegalArgumentException, MemoryConflictException {
		monitor.setMessage("Loading FileBytes...");

		try (InputStream fileIn = byteProvider.getInputStream(0);
				MonitoredInputStream mis = new MonitoredInputStream(fileIn, monitor)) {
			// Indicate that cleanup is not neccessary for cancelled import operation.
			mis.setCleanupOnCancel(false);
			fileBytes = program.getMemory().createFileBytes(byteProvider.getName(), 0, byteProvider.length(), mis,
					monitor);
		}

		final Memory memory = program.getMemory();
		final SymbolTable symbolTable = program.getSymbolTable();
		final AddressSpace defaultAddressSpace = program.getAddressFactory().getDefaultAddressSpace();
		final Address otherAddress = AddressSpace.OTHER_SPACE.getMinAddress();
		Address address;
		Address nextFreeAddress = defaultAddressSpace.getAddress(0);

		if (header.getTextOffset() != 0 || header.getTextSize() < 32) {
			blockHeader = memory.createInitializedBlock(getSectionName("_aoutHeader"), otherAddress, fileBytes, 0, 32,
					true);
		}
		if (header.getTextSize() > 0) {
			address = defaultAddressSpace.getAddress(header.getTextAddr());
			nextFreeAddress = address.add(header.getTextSize());
			blockText = memory.createInitializedBlock(getSectionName(dot_text), address, fileBytes,
					header.getTextOffset(), header.getTextSize(), false);
			blockText.setPermissions(true, true, true);
			blockText.setSourceName(BLOCK_SOURCE_NAME);
		}
		if (header.getDataSize() > 0) {
			address = defaultAddressSpace.getAddress(header.getDataAddr());
			nextFreeAddress = address.add(header.getDataSize());
			blockData = memory.createInitializedBlock(getSectionName(dot_data), address, fileBytes,
					header.getDataOffset(), header.getDataSize(), false);
			blockData.setPermissions(true, true, false);
			blockData.setSourceName(BLOCK_SOURCE_NAME);
		}
		if ((header.getBssSize() + extraBssSize) > 0) {
			address = defaultAddressSpace.getAddress(header.getBssAddr());
			nextFreeAddress = address.add(header.getBssSize() + extraBssSize);
			blockBss = memory.createUninitializedBlock(getSectionName(dot_bss), address,
					header.getBssSize() + extraBssSize, false);
			blockBss.setPermissions(true, true, false);
			blockBss.setSourceName(BLOCK_SOURCE_NAME);
		}
		if (undefinedSymbolCount > 0) {
			blockExternal = memory.getBlock(MemoryBlock.EXTERNAL_BLOCK_NAME);

			if (blockExternal == null) {
				int externalSectionSize = undefinedSymbolCount * 4;
				if (externalSectionSize < EXTERNAL_BLOCK_MIN_SIZE) {
					externalSectionSize = EXTERNAL_BLOCK_MIN_SIZE;
				}
				blockExternal = memory.createUninitializedBlock(MemoryBlock.EXTERNAL_BLOCK_NAME, nextFreeAddress,
						externalSectionSize, true);
				blockExternal.setComment(EXTERNAL_BLOCK_COMMENT);
				blockExternal.setSourceName(BLOCK_SOURCE_NAME);
				nextExternalAddress = blockExternal.getStart();
			} else {
				nextExternalAddress = blockExternal.getStart();

				SymbolIterator it = symbolTable.getExternalSymbols();
				while (it.hasNext()) {
					Symbol externalSymbol = it.next();
					Address externalSymbolAddress = externalSymbol.getAddress();

					if (externalSymbolAddress.compareTo(nextExternalAddress) < 0) {
						nextExternalAddress	= externalSymbolAddress.add(4);
					}
				}
			}
		}
		if (header.getStrSize() > 0) {
			blockStrtab = memory.createInitializedBlock(getSectionName(dot_strtab), otherAddress, fileBytes,
					header.getStrOffset(), header.getStrSize(), true);
			blockStrtab.setSourceName(BLOCK_SOURCE_NAME);
		}
		if (header.getSymSize() > 0) {
			blockSymtab = memory.createInitializedBlock(getSectionName(dot_symtab), otherAddress, fileBytes,
					header.getSymOffset(), header.getSymSize(), true);
			blockSymtab.setSourceName(BLOCK_SOURCE_NAME);
		}
		if (header.getTextRelocSize() > 0) {
			blockRelText = memory.createInitializedBlock(getSectionName(dot_rel_text), otherAddress, fileBytes,
					header.getTextRelocOffset(), header.getTextRelocSize(), true);
			blockRelText.setSourceName(BLOCK_SOURCE_NAME);
		}
		if (header.getDataRelocSize() > 0) {
			blockRelData = memory.createInitializedBlock(getSectionName(dot_rel_data), otherAddress, fileBytes,
					header.getDataRelocOffset(), header.getDataRelocSize(), true);
			blockRelData.setSourceName(BLOCK_SOURCE_NAME);
		}
	}

	private void loadSymbols() throws InvalidInputException {
		monitor.setMessage("Loading symbols...");

		if (symtab == null) {
			return;
		}

		final SymbolTable symbolTable = program.getSymbolTable();
		final FunctionManager functionManager = program.getFunctionManager();
		final Memory memory = program.getMemory();
		final MemoryBlock blockText = memory.getBlock(getSectionName(dot_text));
		final MemoryBlock blockData = memory.getBlock(getSectionName(dot_data));
		final MemoryBlock blockBss = memory.getBlock(getSectionName(dot_bss));
		final MemoryBlock externalBlock = memory.getBlock(MemoryBlock.EXTERNAL_BLOCK_NAME);

		int extraBssOffset = 0;
		List<String> aliases = new ArrayList<>();

		for (UnixAoutSymbol symbol : symtab) {
			Address address = null;
			MemoryBlock block = null;

			switch (symbol.type) {
				case N_TEXT:
					address = blockText != null ? blockText.getStart().add(symbol.value) : null;
					block = blockText;
					break;
				case N_DATA:
					address = blockData != null ? blockData.getStart().add(symbol.value) : null;
					block = blockData;
					break;
				case N_BSS:
					address = blockBss != null ? blockBss.getStart().add(symbol.value) : null;
					block = blockBss;
					break;
				case N_UNDF:
					if (symbol.value > 0) {
						address = blockBss.getEnd().add(extraBssOffset);
						block = blockBss;
						extraBssOffset += symbol.value;
					} else {
						address = nextExternalAddress;
						block = externalBlock;
						symbolTable.addExternalEntryPoint(address);
						nextExternalAddress = nextExternalAddress.add(4);
					}
					break;
				case N_INDR:
					aliases.add(symbol.name);
					break;
				case N_ABS:
				case N_FN:
				case N_STAB:
				case UNKNOWN:
					aliases.clear();
					break;
			}

			if (address == null || block == null) {
				continue;
			}

			switch (symbol.kind) {
				case AUX_FUNC:
					try {
						functionManager.createFunction(symbol.name, address, new AddressSet(address),
								SourceType.IMPORTED);
					} catch (OverlappingFunctionException e) {
						log.appendMsg(block.getName(), String.format(
								"Failed to create function %s @ %s, creating symbol instead.", symbol.name, address));
						symbolTable.createLabel(address, symbol.name, SourceType.IMPORTED);
					}
					break;
				default:
					Symbol label = symbolTable.createLabel(address, symbol.name, SourceType.IMPORTED);
					if (symbol.isExt) {
						label.setPrimary();
					}
					break;
			}

			for (String alias : aliases) {
				symbolTable.createLabel(address, alias, SourceType.IMPORTED);
			}

			aliases.clear();
		}
	}

	private void applyRelocations(MemoryBlock targetBlock, UnixAoutRelocationTable relTable)
			throws MemoryAccessException {
		if (targetBlock == null || relTable == null) {
			return;
		}

		monitor.setMessage(String.format("Applying relocations for section %s...", targetBlock.getName()));

		final DataConverter dc = DataConverter.getInstance(program.getLanguage().isBigEndian());
		final SymbolTable symbolTable = program.getSymbolTable();
		final RelocationTable relocationTable = program.getRelocationTable();

		int idx = 0;
		for (UnixAoutRelocation relocation : relTable) {
			int type = ((int) relocation.flags) & 0xFF;
			Address targetAddress = targetBlock.getStart().add(relocation.address);

			byte originalBytes[] = new byte[relocation.pointerLength];
			targetBlock.getBytes(targetAddress, originalBytes);
			long addend = dc.getValue(originalBytes, 0, relocation.pointerLength);

			Long value = null;
			Status status = Status.FAILURE;

			if (relocation.baseRelative || relocation.jmpTable || relocation.relative || relocation.copy) {
				status = Status.UNSUPPORTED;
			} else {
				if (relocation.extern == true && relocation.symbolNum < symtab.size()) {
					SymbolIterator symbolIterator = symbolTable.getSymbols(symtab.get(relocation.symbolNum).name);
					if (symbolIterator.hasNext()) {
						value = symbolIterator.next().getAddress().getOffset();
					}
				} else if (relocation.extern == false) {
					switch (relocation.symbolNum) {
						case 4:
							value = blockText.getStart().getOffset();
							break;
						case 6:
							value = blockData.getStart().getOffset();
							break;
						case 8:
							value = blockBss.getStart().getOffset();
							break;
					}
				}
			}

			if (value != null) {
				if (relocation.pcRelativeAddressing) {
					// Addend is relative to start of target section.
					value -= targetBlock.getStart().getOffset();
				}

				// Apply relocation.
				byte newBytes[] = new byte[relocation.pointerLength];
				dc.putValue(value + addend, relocation.pointerLength, newBytes, 0);
				targetBlock.putBytes(targetAddress, newBytes);

				status = Status.APPLIED;
			}

			if (status != Status.APPLIED) {
				log.appendMsg(targetBlock.getName(),
						String.format("Failed to apply relocation entry %d with type 0x%02x @ %s.", idx,
								relocation.flags, targetAddress));
			}

			relocationTable.add(targetAddress, status, type, new long[] { relocation.symbolNum }, originalBytes,
					relocation.getSymbolName(symtab));
			idx++;
		}
	}

	private void markupSections()
			throws InvalidInputException, CodeUnitInsertionException, DuplicateNameException, IOException {
		final AddressSpace defaultAddressSpace = program.getAddressFactory().getDefaultAddressSpace();
		final FunctionManager functionManager = program.getFunctionManager();
		final SymbolTable symbolTable = program.getSymbolTable();

		monitor.setMessage("Marking up header...");

		// Markup header.
		Address headerAddress = null;
		if (blockHeader != null) {
			headerAddress = blockHeader.getStart();
		} else if (blockText != null && header.getTextOffset() == 0 && header.getTextSize() >= 32) {
			headerAddress = blockText.getStart();
		}
		if (headerAddress != null) {
			header.markup(program, headerAddress);
		}

		// Markup entrypoint.
		if (header.getEntryPoint() != 0) {
			Address address = defaultAddressSpace.getAddress(header.getEntryPoint());
			try {
				functionManager.createFunction("entry", address, new AddressSet(address), SourceType.IMPORTED);
			} catch (OverlappingFunctionException e) {
				log.appendMsg(dot_text, "Failed to create entrypoint function @ %s, creating symbol instead.");
				symbolTable.createLabel(address, "entry", SourceType.IMPORTED);
			}
		}

		monitor.setMessage("Marking up relocation tables...");

		if (blockRelText != null) {
			relText.markup(program, blockRelText);
		}

		if (blockRelData != null) {
			relData.markup(program, blockRelData);
		}

		monitor.setMessage("Marking up symbol table...");

		if (blockSymtab != null) {
			symtab.markup(program, blockSymtab);
		}

		monitor.setMessage("Marking up string table...");

		if (blockStrtab != null) {
			strtab.markup(program, blockStrtab);
		}
	}

	private String getSectionName(String section) {
		if (prefixSectionNamesWithFileName) {
			String fileName = header.getReader().getByteProvider().getFSRL().getName();
			return fileName + ":" + section;
		}

		return section;
	}

	public static boolean mustPrefixSectionNames(Program program) {
		final Memory memory = program.getMemory();
		return memory.getBlock(dot_text) != null || memory.getBlock(dot_data) != null
				|| memory.getBlock(dot_bss) != null || memory.getBlock(dot_rel_text) != null
				|| memory.getBlock(dot_rel_data) != null || memory.getBlock(dot_strtab) != null
				|| memory.getBlock(dot_symtab) != null;
	}
}
