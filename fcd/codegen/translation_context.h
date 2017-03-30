//
// translation_context.h
// Copyright (C) 2015 Félix Cloutier.
// All Rights Reserved.
//
// This file is distributed under the University of Illinois Open Source
// license. See LICENSE.md for details.
//

#ifndef fcd__translation_context_h
#define fcd__translation_context_h

#include "capstone_wrapper.h"
#include "code_generator.h"
#include "executable.h"
#include "targetinfo.h"
#include "translation_maps.h"
#include "x86_regs.h"

#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/LegacyPassManager.h>
#include <llvm/IR/LLVMContext.h>

#include <memory>
#include <unordered_map>
#include <unordered_set>

class CodeGenerator;

class TranslationContext
{
	llvm::LLVMContext& context;
	Executable& executable;
	std::unique_ptr<capstone> cs;
	std::unique_ptr<CodeGenerator> irgen;
	std::unique_ptr<llvm::Module> module;
	std::unique_ptr<AddressToFunction> functionMap;
	
	llvm::FunctionType* resultFnTy;
	llvm::GlobalVariable* configVariable;
	
	llvm::CastInst& getPointer(llvm::Value* intptr, size_t size);
	std::string nameOf(uint64_t address) const;
	
public:
	TranslationContext(llvm::LLVMContext& context, Executable& executable, const x86_config& config, const std::string& module_name = "");
	~TranslationContext();
	
	void setFunctionName(uint64_t address, const std::string& name);
	llvm::Function* createFunction(uint64_t base_address);
	std::unordered_set<uint64_t> getDiscoveredEntryPoints() const;
	
	inline llvm::Module* operator->() { return &get(); }
	llvm::Module& get() { return *module; }
	std::unique_ptr<llvm::Module> take();
};

#endif /* defined(fcd__translation_context_h) */
