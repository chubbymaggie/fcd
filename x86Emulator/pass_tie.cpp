//
//  pass_tie.cpp
//  x86Emulator
//
//  Created by Félix on 2015-07-29.
//  Copyright © 2015 Félix Cloutier. All rights reserved.
//

#include "pass_tie.h"
#include <limits>

using namespace std;
using namespace llvm;

namespace
{
	using namespace tie;
	
	const AnyType any;
	const tie::NoneType none;
	const IntegralType boolean(IntegralType::Numeric, 1);
	const CodePointerType basicBlockPointer(CodePointerType::BasicBlock);
	const CodePointerType functionPointer(CodePointerType::Function);
	
	unsigned roundUpToPowerOfTwo(unsigned value)
	{
		assert(value != 0);
		unsigned mask = 0xffffffffu >> __builtin_clz(value);
		mask >>= 1; // two steps because shifting by 32 at once would be UB
		unsigned sum = value + mask;
		return sum & ~(sum >> 1) & ~mask;
	}
}

#pragma mark - Type implementation
namespace tie
{
	bool IntegralType::operator<(const IntegralType& that) const
	{
		if (tag < that.tag)
		{
			return true;
		}
		
		if (tag > that.tag)
		{
			return false;
		}
		
		return bitCount < that.bitCount;
	}
	
	void IntegralType::print(llvm::raw_ostream &os) const
	{
		if (bitCount == 1)
		{
			os << "bool";
			return;
		}
		
		switch (tag)
		{
			case Register: os << "reg"; break;
			case Numeric: os << "num"; break;
			case Signed: os << "int"; break;
			case Unsigned: os << "uint"; break;
			default:
				assert(false);
				os << "unk";
		}
		os << bitCount << "_t";
	}
	
	void DataPointerType::print(llvm::raw_ostream &os) const
	{
		assert(!isa<CodePointerType>(pointee));
		pointee.print(os);
		os << '*';
	}
	
	bool CodePointerType::operator<(const CodePointerType &that) const
	{
		return tag < that.tag;
	}
	
	void CodePointerType::print(llvm::raw_ostream &os) const
	{
		os << (tag == BasicBlock ? "basicblock" : "function");
		os << "_ptr_t";
	}
	
#pragma mark - InferenceContext
	InferenceContext::InferenceContext(const TargetInfo& target, MemorySSA& mssa)
	: target(target), mssa(mssa)
	{
	}
	
#pragma mark - InferenceContext InstVisitor implementation
	void InferenceContext::visitConstant(Constant &constant)
	{
		if (auto integralConstant = dyn_cast<ConstantInt>(&constant))
		{
			const APInt& value = integralConstant->getValue();
			constrain<SpecializesConstraint>(&constant, &getNum(value.getActiveBits()));
			constrain<GeneralizesConstraint>(&constant, &getNum(value.getBitWidth()));
		}
		else
		{
			assert(false);
		}
	}
	
	void InferenceContext::visitICmpInst(llvm::ICmpInst &inst)
	{
		constrain<SpecializesConstraint>(&inst, &getBoolean());
		
		const TypeBase* minSize = nullptr;
		const TypeBase* maxSize = nullptr;
		switch (inst.getPredicate())
		{
			case llvm::CmpInst::ICMP_UGE:
			case llvm::CmpInst::ICMP_UGT:
			case llvm::CmpInst::ICMP_ULE:
			case llvm::CmpInst::ICMP_ULT:
				minSize = &getUint(8);
				maxSize = &getUint(64);
				break;
				
			case llvm::CmpInst::ICMP_SGE:
			case llvm::CmpInst::ICMP_SGT:
			case llvm::CmpInst::ICMP_SLE:
			case llvm::CmpInst::ICMP_SLT:
				minSize = &getSint(8);
				maxSize = &getSint(64);
				break;
				
			default: // EQ, NEQ
				// nothing else to infer
				return;
		}
		
		for (unsigned i = 0; i < inst.getNumOperands(); i++)
		{
			constrain<SpecializesConstraint>(inst.getOperand(i), minSize);
			constrain<GeneralizesConstraint>(inst.getOperand(i), maxSize);
		}
	}
	
	void InferenceContext::visitAllocaInst(llvm::AllocaInst& inst)
	{
		constrain<SpecializesConstraint>(&inst, &getPointer());
	}
	
	void InferenceContext::visitLoadInst(llvm::LoadInst &inst)
	{
		assert(inst.getType()->isIntegerTy());
		unsigned bitCount = inst.getType()->getIntegerBitWidth();
		
		constrain<SpecializesConstraint>(inst.getPointerOperand(), &getPointer());
		constrain<GeneralizesConstraint>(&inst, getReg(bitCount));
		
		if (auto access = mssa.getMemoryAccess(&inst))
		if (auto def = access->getDefiningAccess())
		if (auto store = dyn_cast_or_null<StoreInst>(def->getMemoryInst()))
		{
			auto valueOperand = store->getValueOperand();
			constrain<IsEqualConstraint>(&inst, valueOperand);
		}
	}
	
	void InferenceContext::visitStoreInst(llvm::StoreInst &inst)
	{
		// This does not teach us anything. Memory locations can be reused for different types.
		// Instead, this creates a memory SSA defining access that we can make use of later to infer things.
	}
	
	void InferenceContext::visitGetElementPtrInst(llvm::GetElementPtrInst &inst)
	{
		// Probably used to access a weird register location
		assert(false);
	}
	
	void InferenceContext::visitPHINode(llvm::PHINode &inst)
	{
		for (unsigned i = 0; i < inst.getNumIncomingValues(); i++)
		{
			Value* incoming = inst.getIncomingValue(i);
			constrain<IsEqualConstraint>(&inst, incoming);
		}
	}
	
	void InferenceContext::visitSelectInst(llvm::SelectInst &inst)
	{
		constrain<SpecializesConstraint>(inst.getCondition(), &getBoolean());
		constrain<IsEqualConstraint>(inst.getTrueValue(), inst.getFalseValue());
		constrain<GeneralizesConstraint>(&inst, inst.getTrueValue());
	}
	
	void InferenceContext::visitCallInst(llvm::CallInst &inst)
	{
		// do something here
		assert(false);
	}
	
	void InferenceContext::visitBinaryOperator(llvm::BinaryOperator &inst)
	{
		auto opcode = inst.getOpcode();
		auto left = inst.getOperand(0);
		auto right = inst.getOperand(1);
		assert(false);
	}
	
	void InferenceContext::visitTerminatorInst(llvm::TerminatorInst &inst)
	{
		// do nothing
	}
	
	void InferenceContext::visitInstruction(llvm::Instruction &inst)
	{
		assert(false);
	}
	
#pragma mark - InferenceContext getters
	const IntegralType& InferenceContext::getBoolean()
	{
		return boolean;
	}
	
	const IntegralType& InferenceContext::getReg(unsigned width)
	{
		return *pool.allocate<IntegralType>(IntegralType::Register, width);
	}
	
	const IntegralType& InferenceContext::getNum(unsigned width)
	{
		return *pool.allocate<IntegralType>(IntegralType::Numeric, width);
	}
	
	const IntegralType& InferenceContext::getSint(unsigned width)
	{
		return *pool.allocate<IntegralType>(IntegralType::Signed, width);
	}
	
	const IntegralType& InferenceContext::getUint(unsigned width)
	{
		return *pool.allocate<IntegralType>(IntegralType::Unsigned, width);
	}
	
	const CodePointerType& InferenceContext::getFunctionPointer()
	{
		return functionPointer;
	}
	
	const CodePointerType& InferenceContext::getBasicBlockPointer()
	{
		return basicBlockPointer;
	}
	
	const AnyType& InferenceContext::getAny()
	{
		return any;
	}
	
	const NoneType& InferenceContext::getNone()
	{
		return none;
	}
	
	const IntegralType& InferenceContext::getPointer()
	{
		return *pool.allocate<IntegralType>(IntegralType::Pointer, target.getPointerWidth());
	}
	
	const DataPointerType& InferenceContext::getPointerTo(const tie::TypeBase &pointee)
	{
		return *pool.allocate<DataPointerType>(pointee);
	}
}
