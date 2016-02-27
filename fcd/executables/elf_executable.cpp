//
// elf_executable.cpp
// Copyright (C) 2015 Félix Cloutier.
// All Rights Reserved.
//
// This file is part of fcd. fcd as a whole is licensed under the terms
// of the GNU GPLv3 license, but specific parts (such as this one) are
// dual-licensed under the terms of a BSD-like license as well. You
// may use, modify and distribute this part of fcd under the terms of
// either license, at your choice. See the LICENSE file in this directory
// for details.
//

#include "elf_executable.h"
#include "executable_errors.h"
#include "llvm_warnings.h"

SILENCE_LLVM_WARNINGS_BEGIN()
#include <llvm/Support/raw_ostream.h>
SILENCE_LLVM_WARNINGS_END()

#include <array>
#include <cstdint>
#include <deque>
#include <unordered_map>

using namespace llvm;
using namespace std;

namespace
{
	template<typename T>
	struct ptr_range
	{
		const T* a;
		const T* z;
		
		inline ptr_range() : a(nullptr), z(nullptr)
		{
		}
		
		inline ptr_range(const T* a, const T* z)
		: a(a), z(z)
		{
		}
		
		const T* begin() const { return a; }
		const T* end() const { return z; }
	};

	template<typename T>
	const T* bounded_cast(const uint8_t* begin, const uint8_t* end, size_t offset)
	{
		unsigned long long max;
		if (__builtin_uaddll_overflow(offset, sizeof(T), &max) || end < begin || end - begin < max)
		{
			return nullptr;
		}
		
		return reinterpret_cast<const T*>(&begin[offset]);
	}

	template<typename T>
	ptr_range<T> bounded_cast(const uint8_t* begin, const uint8_t* end, size_t offset, size_t count)
	{
		unsigned long long max;
		if (__builtin_umulll_overflow(count, sizeof(T), &max) || __builtin_uaddll_overflow(offset, max, &max) || end < begin || end - begin < max)
		{
			return ptr_range<T>();
		}
		
		return ptr_range<T>(reinterpret_cast<const T*>(&begin[offset]), reinterpret_cast<const T*>(&begin[max]));
	}

	struct Elf32Types
	{
		static constexpr size_t bits = 32;
		typedef uint16_t Half;
		typedef uint32_t Word;
		typedef int32_t Sword;
		typedef uint64_t Xword;
		typedef int64_t Sxword;
		typedef uint32_t Addr;
		typedef uint32_t Off;
		typedef uint16_t SectionIndex;
		typedef uint32_t SymbolIndex;
	};

	struct Elf64Types
	{
		static constexpr size_t bits = 64;
		typedef uint16_t Half;
		typedef uint32_t Word;
		typedef int32_t Sword;
		typedef uint64_t Xword;
		typedef int64_t Sxword;
		typedef uint64_t Addr;
		typedef uint64_t Off;
		typedef uint16_t SectionIndex;
		typedef uint32_t SymbolIndex;
	};

	enum ElfIdentification
	{
		EI_CLASS = 4,
		EI_DATA = 5,
		EI_NIDENT = 16,
	};

	enum ElfDataType
	{
		ELFDATANONE = 0,
		ELFDATA2LSB = 1,
		ELFDATA2MSB = 2,
	};

	enum ElfPhdrType
	{
		PT_LOAD = 1,
		PT_DYNAMIC = 2,
	};

	enum ElfShdrType
	{
		SHT_PROGBITS = 1,
		SHT_SYMTAB = 2,
		SHT_STRTAB = 3,
		SHT_DYNSYM = 11,
	};

	enum ElfSymbolType
	{
		STT_FUNC = 2,
	};

	enum ElfDynamicTag
	{
		DT_PLTRELSZ = 2,
		DT_STRTAB = 5,
		DT_SYMTAB = 6,
		DT_RELA = 7,
		DT_INIT = 12,
		DT_FINI = 13,
		DT_REL = 17,
		DT_PLTREL = 20,
		DT_JMPREL = 23,
		DT_INIT_ARRAY = 25,
		DT_FINI_ARRAY = 26,
		DT_INIT_ARRAYSZ = 27,
		DT_FINI_ARRAYSZ = 28,
		DT_PREINIT_ARRAY = 32,
		DT_PREINIT_ARRAYSZ = 33,
		DT_MAX = 34,
	};

	struct Segment
	{
		uint64_t vbegin;
		uint64_t vend;
		const uint8_t* fbegin;
	};

	template<typename Types>
	class ElfExecutable final : public Executable
	{
		typedef typename Types::Half half;
		typedef typename Types::Word word;
		typedef typename Types::Sword sword;
		typedef typename Types::Xword xword;
		typedef typename Types::Sxword sxword;
		typedef typename Types::Addr addr;
		typedef typename Types::Off off;
		typedef typename Types::SectionIndex seind;
		typedef typename Types::SymbolIndex syind;
		
		// structures
		struct Elf_Ehdr
		{
			uint8_t ident[EI_NIDENT];
			half type;
			half machine;
			word version;
			addr entry;
			off phoff;
			off shoff;
			word flags;
			half ehsize;
			half phentsize;
			half phnum;
			half shentsize;
			half shnum;
			half shstrndx;
		};
		
		// specialized below
		struct Elf_Phdr;
		struct Elf_Shdr;
		struct Elf_Sym;
		struct Elf_Dynamic;
		struct Elf_Rel;
		struct Elf_Rela;
		
		vector<Segment> segments;
		unordered_map<uint64_t, string> stubTargets;
		
	public:
		static ErrorOr<unique_ptr<ElfExecutable<Types>>> parse(const uint8_t* begin, const uint8_t* end);
		
		ElfExecutable(const uint8_t* begin, const uint8_t* end)
		: Executable(begin, end)
		{
		}
		
		virtual string getExecutableType() const override
		{
			union {
				short s;
				char c[2];
			} endianCheck = { .s = 0x0201 };
			
			char type[] = "ELF nn nE";
			snprintf(type, sizeof type, "ELF %02zu %cE", Types::bits, endianCheck.c[0] == 0x02 ? 'B' : 'L');
			return type;
		}
		
		virtual const uint8_t* map(uint64_t address) const override
		{
			for (auto iter = segments.rbegin(); iter != segments.rend(); iter++)
			{
				if (address >= iter->vbegin && address < iter->vend)
				{
					return iter->fbegin + (address - iter->vbegin);
				}
			}
			return nullptr;
		}
		
		virtual const string* doGetStubTarget(uint64_t address) const override
		{
			auto iter = stubTargets.find(address);
			if (iter != stubTargets.end())
			{
				return &iter->second;
			}
			return nullptr;
		}
	};

	template<>
	struct ElfExecutable<Elf32Types>::Elf_Phdr
	{
		word type;
		off offset;
		addr vaddr;
		addr paddr;
		word filesz;
		word memsz;
		word flags;
		word align;
	};

	template<>
	struct ElfExecutable<Elf64Types>::Elf_Phdr
	{
		word type;
		word flags;
		off offset;
		addr vaddr;
		addr paddr;
		xword filesz;
		xword memsz;
		xword align;
	};

	template<>
	struct ElfExecutable<Elf32Types>::Elf_Shdr
	{
		word name;
		word type;
		word flags;
		addr addr;
		off offset;
		word size;
		word link;
		word info;
		word addralign;
		word entsize;
	};

	template<>
	struct ElfExecutable<Elf64Types>::Elf_Shdr
	{
		word name;
		word type;
		xword flags;
		addr addr;
		off offset;
		xword size;
		word link;
		word info;
		xword addralign;
		xword entsize;
	};

	template<>
	struct ElfExecutable<Elf32Types>::Elf_Sym
	{
		word name;
		addr value;
		word size;
		unsigned char info;
		unsigned char other;
		half shndx;
	};

	template<>
	struct ElfExecutable<Elf64Types>::Elf_Sym
	{
		word name;
		unsigned char info;
		unsigned char other;
		half shndx;
		addr value;
		xword size;
	};

	template<>
	struct ElfExecutable<Elf32Types>::Elf_Dynamic
	{
		sword tag;
		union {
			word value;
			addr address;
		};
	};

	template<>
	struct ElfExecutable<Elf64Types>::Elf_Dynamic
	{
		sxword tag;
		union {
			xword value;
			addr address;
		};
	};

	template<>
	struct ElfExecutable<Elf32Types>::Elf_Rel
	{
		addr offset;
		word info;

		inline uint32_t symbol() const { return info >> 8; }
		inline uint8_t type() const { return info & 0xff; }
	};

	template<>
	struct ElfExecutable<Elf64Types>::Elf_Rel
	{
		addr offset;
		xword info;

		inline uint32_t symbol() const { return info >> 32; }
		inline uint32_t type() const { return info & 0xffffffff; }
	};

	template<>
	struct ElfExecutable<Elf32Types>::Elf_Rela : public ElfExecutable<Elf32Types>::Elf_Rel
	{
		sword addend;
	};

	template<>
	struct ElfExecutable<Elf64Types>::Elf_Rela : public ElfExecutable<Elf64Types>::Elf_Rel
	{
		sxword addend;
	};
	
	struct EntryPointArrayInfo
	{
		ElfDynamicTag locationTag;
		ElfDynamicTag sizeTag;
		string name;
	};

	template<typename Types>
	ErrorOr<unique_ptr<ElfExecutable<Types>>> ElfExecutable<Types>::parse(const uint8_t* begin, const uint8_t* end)
	{
		using namespace std;
		auto executable = make_unique<ElfExecutable<Types>>(begin, end);
		
		deque<const Elf_Phdr*> dynamics;
		deque<const Elf_Shdr*> sections;
		deque<const Elf_Shdr*> symtabs;
		
		// Walk header, identify PT_LOAD and PT_DYNAMIC segments, sections, and symbol tables.
		bool loadAtZero = false;
		if (auto eh = bounded_cast<Elf_Ehdr>(begin, end, 0))
		{
			if (eh->phentsize == sizeof (Elf_Phdr))
			{
				for (const auto& ph : bounded_cast<Elf_Phdr>(begin, end, eh->phoff, eh->phnum))
				{
					if (ph.type == PT_LOAD)
					{
						unsigned long long endAddress;
						if (!__builtin_uaddll_overflow(ph.vaddr, ph.memsz, &endAddress))
						{
							auto fileLoc = bounded_cast<uint8_t>(begin, end, ph.offset, ph.filesz);
							if (fileLoc.begin() != nullptr)
							{
								Segment seg = { .vbegin = ph.vaddr, .vend = endAddress };
								seg.vbegin = ph.vaddr;
								seg.vend = endAddress;
								seg.fbegin = fileLoc.begin();
								executable->segments.push_back(seg);
								loadAtZero |= seg.vbegin == 0;
							}
						}
					}
					else if (ph.type == PT_DYNAMIC)
					{
						dynamics.push_back(&ph);
					}
				}
			}
			
			if (eh->shentsize == sizeof (Elf_Shdr))
			{
				for (const auto& sh : bounded_cast<Elf_Shdr>(begin, end, eh->shoff, eh->shnum))
				{
					sections.push_back(&sh);
					if (sh.type == SHT_SYMTAB)
					{
						symtabs.push_back(&sh);
					}
				}
			}
			
			if (eh->entry != 0 || loadAtZero)
			{
				executable->getSymbol(eh->entry).virtualAddress = eh->entry;
			}
		}
		
		// Walk dynamic segments.
		array<const Elf_Dynamic*, DT_MAX> dynEnt;
		dynEnt.fill(nullptr);
		
		for (const auto* dynHeader : dynamics)
		{
			size_t numEnts = dynHeader->filesz / sizeof (Elf_Dynamic);
			for (const auto& dyn : bounded_cast<Elf_Dynamic>(begin, end, dynHeader->offset, numEnts))
			{
				if (dyn.tag < DT_MAX)
				{
					dynEnt[dyn.tag] = &dyn;
				}
			}
		}
		
		EntryPointArrayInfo arrayInfo[] = {
			{DT_PREINIT_ARRAY, DT_PREINIT_ARRAYSZ, "preinit_"},
			{DT_INIT_ARRAY, DT_INIT_ARRAYSZ, "init_"},
			{DT_FINI_ARRAY, DT_FINI_ARRAYSZ, "fini_"},
		};
		for (const auto& arrayData : arrayInfo)
		{
			auto arrayLocation = dynEnt[arrayData.locationTag];
			auto arraySize = dynEnt[arrayData.sizeTag];
			if (arrayLocation != nullptr && arraySize != nullptr)
			{
				size_t counter = 0;
				const string& prefix = arrayData.name;
				for (addr entry : bounded_cast<addr>(begin, end, arrayLocation->address, arraySize->address))
				{
					auto& symInfo = executable->getSymbol(entry);
					symInfo.virtualAddress = entry;
					raw_string_ostream(symInfo.name) << prefix << counter;
					counter++;
				}
			}
		}
		
		pair<ElfDynamicTag, string> initFini[] = {
			{DT_INIT, "init"},
			{DT_FINI, "fini"}
		};
		for (const auto& pair : initFini)
		{
			auto location = dynEnt[pair.first];
			if (location != nullptr)
			{
				auto& symInfo = executable->getSymbol(location->address);
				symInfo.virtualAddress = location->address;
				symInfo.name = pair.second;
			}
		}
		
		// Check relocations to put a name on relocated entries.
		// I usually do explicit checks against nullptr for pointers but there are quite a few to check here.
		if (dynEnt[DT_JMPREL] && dynEnt[DT_PLTRELSZ] && dynEnt[DT_PLTREL] && dynEnt[DT_STRTAB] && dynEnt[DT_SYMTAB])
		{
			const uint8_t* relocBase = executable->map(dynEnt[DT_JMPREL]->address);
			const uint8_t* symtab = executable->map(dynEnt[DT_SYMTAB]->address);
			const uint8_t* strtab = executable->map(dynEnt[DT_STRTAB]->address);
			ElfDynamicTag relType = static_cast<ElfDynamicTag>(dynEnt[DT_PLTREL]->value);
			if (relocBase && symtab && strtab && (relType == DT_REL || relType == DT_RELA))
			{
				uint64_t relocSize = relType == DT_REL ? sizeof (Elf_Rel) : sizeof (Elf_Rela);
				uint64_t relocMax = dynEnt[DT_PLTRELSZ]->value;
				
				// Fortunately, Elf_Rela is merely an extension of Elf_Rel and we can treat both as Elf_Rel as long as
				// we correctly increment the pointer.
				for (uint64_t relocIter = 0; relocIter < relocMax; relocIter += relocSize)
				{
					if (const auto* reloc = bounded_cast<Elf_Rel>(relocBase, end, relocIter))
					if (const auto* symbol = bounded_cast<Elf_Sym>(symtab, end, sizeof (Elf_Sym) * reloc->symbol()))
					if (const char* nameBegin = bounded_cast<char>(strtab, end, symbol->name))
					{
						const char* nameEnd = nameBegin + strnlen(nameBegin, end - (const uint8_t*)nameBegin);
						executable->stubTargets[reloc->offset] = string(nameBegin, nameEnd);
					}
				}
			}
		}
		
		// Walk symbol tables and identify function symbols.
		// This can override dynamic segment info, and it's fine.
		for (const auto* sth : symtabs)
		{
			if (sth->entsize != 0 && sth->entsize != sizeof (Elf_Sym))
			{
				continue;
			}
			
			const uint8_t* strtab = nullptr;
			if (sth->link != 0 && sth->link < sections.size())
			{
				auto strtabHeader = sections[sth->link];
				if (strtabHeader->type == SHT_STRTAB)
				{
					strtab = bounded_cast<uint8_t>(begin, end, strtabHeader->offset);
				}
			}
			
			size_t numEnts = sth->size / sizeof (Elf_Sym);
			for (const auto& sym : bounded_cast<Elf_Sym>(begin, end, sth->offset, numEnts))
			{
				// Exclude non-function symbols.
				if ((sym.info & 0xf) != STT_FUNC)
				{
					continue;
				}
				
				const char* nameBegin = nullptr;
				if (sym.name != 0)
				{
					nameBegin = bounded_cast<char>(strtab, end, sym.name);
				}
				
				const char* nameEnd = nameBegin;
				if (nameBegin != nullptr)
				{
					nameEnd = nameBegin + strnlen(nameBegin, reinterpret_cast<const char*>(end) - nameBegin);
				}
				
				auto& symInfo = executable->getSymbol(sym.value);
				symInfo.virtualAddress = sym.value;
				symInfo.name = string(nameBegin, nameEnd);
			}
		}
		
		// Figure out file offset for symbols, remove those that don't have one.
		for (auto entryPoint : executable->getVisibleEntryPoints())
		{
			if (auto address = executable->map(entryPoint))
			{
				executable->getSymbol(entryPoint).memory = address;
			}
			else
			{
				executable->eraseSymbol(entryPoint);
			}
		}
		
		return move(executable);
	}
}

ErrorOr<unique_ptr<Executable>> parseElfExecutable(const uint8_t* begin, const uint8_t* end)
{
	if (auto endianByte = bounded_cast<uint8_t>(begin, end, EI_DATA))
	{
		// We currently don't support non-native endianness (yet). At least return null if the ELF's endianness does not
		// match the host endianness instead of just crashing later or something.
		uint16_t hostEndianTest = (ELFDATA2MSB << 8) | ELFDATA2LSB;
		uint8_t hostEndian = *reinterpret_cast<uint8_t*>(&hostEndianTest);
		
		if (*endianByte != hostEndian)
		{
			return make_error_code(ExecutableParsingError::Elf_EndianMismatch);
		}
		
		if (auto classByte = bounded_cast<uint8_t>(begin, end, EI_CLASS))
		{
			switch (*classByte)
			{
				case 1: return ElfExecutable<Elf32Types>::parse(begin, end);
				case 2: return ElfExecutable<Elf64Types>::parse(begin, end);
				default: break;
			}
		}
	}
	
	return make_error_code(ExecutableParsingError::Elf_Corrupted);
}
