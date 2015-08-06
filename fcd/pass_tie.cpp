//
//  pass_tie.cpp
//  x86Emulator
//
//  Created by Félix on 2015-07-29.
//  Copyright © 2015 Félix Cloutier. All rights reserved.
//

#include "pass_tie.h"

SILENCE_LLVM_WARNINGS_BEGIN()
#include <llvm/Support/raw_os_ostream.h>
SILENCE_LLVM_WARNINGS_END()

#include <iostream>
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

#pragma mark - Type Implementation
namespace tie
{
	void TypeBase::dump() const
	{
		raw_os_ostream rerr(cerr);
		print(rerr);
	}
	
	void TypeOrValue::dump() const
	{
		raw_os_ostream rerr(cerr);
		print(rerr);
	}
	
	void TypeOrValue::print(raw_ostream &os) const
	{
		if (value == nullptr)
		{
			os << "type<";
			type->print(os);
		}
		else
		{
			os << "value<";
			value->printAsOperand(os);
		}
		os << '>';
	}
	
	bool IntegralType::operator<(const IntegralType& that) const
	{
		assert(!"implement me");
	}
	
	void IntegralType::print(raw_ostream &os) const
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
			case Pointer: os << "anyptr"; break;
			default:
				assert(false);
				os << "unk";
		}
		os << bitCount << "_t";
	}
	
	void DataPointerType::print(raw_ostream &os) const
	{
		assert(!isa<CodePointerType>(pointee));
		pointee.print(os);
		os << '*';
	}
	
	bool CodePointerType::operator<(const CodePointerType &that) const
	{
		return tag < that.tag;
	}
	
	void CodePointerType::print(raw_ostream &os) const
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
			// Disjunction over whether the value is signed.
			// XXX: this could be a problem when the same constant is used multiple times.
			DisjunctionConstraint* disj = pool.allocate<DisjunctionConstraint>(pool);
			disj->constrain<SpecializesConstraint>(&constant, &getSint(value.getMinSignedBits()));
			disj->constrain<SpecializesConstraint>(&constant, &getUint(value.getActiveBits()));
			constraints.insert({&constant, disj});
			constrain<GeneralizesConstraint>(&constant, &getNum(value.getBitWidth()));
		}
		else if (auto expression = dyn_cast<ConstantExpr>(&constant))
		{
			Instruction* inst = expression->getAsInstruction();
			visit(*inst, &constant);
		}
		else
		{
			assert(isa<GlobalValue>(constant));
		}
	}
	
	void InferenceContext::visitICmpInst(ICmpInst &inst, Value* constraintKey)
	{
		constraintKey = constraintKey ? constraintKey : &inst;
		constrain<SpecializesConstraint>(constraintKey, &getBoolean());
		
		const TypeBase* minSize = nullptr;
		const TypeBase* maxSize = nullptr;
		switch (inst.getPredicate())
		{
			case CmpInst::ICMP_UGE:
			case CmpInst::ICMP_UGT:
			case CmpInst::ICMP_ULE:
			case CmpInst::ICMP_ULT:
				minSize = &getUint(8);
				maxSize = &getUint(64);
				break;
				
			case CmpInst::ICMP_SGE:
			case CmpInst::ICMP_SGT:
			case CmpInst::ICMP_SLE:
			case CmpInst::ICMP_SLT:
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
	
	void InferenceContext::visitAllocaInst(AllocaInst& inst, Value* constraintKey)
	{
		constraintKey = constraintKey ? constraintKey : &inst;
		constrain<SpecializesConstraint>(constraintKey, &getPointer());
	}
	
	void InferenceContext::visitLoadInst(LoadInst &inst, Value* constraintKey)
	{
		constraintKey = constraintKey ? constraintKey : &inst;
		assert(inst.getType()->isIntegerTy());
		unsigned bitCount = inst.getType()->getIntegerBitWidth();
		
		constrain<SpecializesConstraint>(inst.getPointerOperand(), &getPointer());
		constrain<GeneralizesConstraint>(constraintKey, &getReg(bitCount));
		
		if (auto access = mssa.getMemoryAccess(constraintKey))
		if (auto def = access->getDefiningAccess())
		if (auto store = dyn_cast_or_null<StoreInst>(def->getMemoryInst()))
		{
			auto valueOperand = store->getValueOperand();
			constrain<IsEqualConstraint>(constraintKey, valueOperand);
		}
	}
	
	void InferenceContext::visitStoreInst(StoreInst &inst, Value* constraintKey)
	{
		// This does not teach us anything. Memory locations can be reused for different types.
		// Instead, this creates a memory SSA defining access that we can make use of later to infer things.
	}
	
	void InferenceContext::visitGetElementPtrInst(GetElementPtrInst &inst, Value* constraintKey)
	{
		// Probably used to access a weird register location
		assert(false);
	}
	
	void InferenceContext::visitPHINode(PHINode &inst, Value* constraintKey)
	{
		constraintKey = constraintKey ? constraintKey : &inst;
		for (unsigned i = 0; i < inst.getNumIncomingValues(); i++)
		{
			Value* incoming = inst.getIncomingValue(i);
			constrain<IsEqualConstraint>(constraintKey, incoming);
		}
	}
	
	void InferenceContext::visitSelectInst(SelectInst &inst, Value* constraintKey)
	{
		constraintKey = constraintKey ? constraintKey : &inst;
		constrain<SpecializesConstraint>(inst.getCondition(), &getBoolean());
		constrain<IsEqualConstraint>(inst.getTrueValue(), inst.getFalseValue());
		constrain<GeneralizesConstraint>(constraintKey, inst.getTrueValue());
	}
	
	void InferenceContext::visitCallInst(CallInst &inst, Value* constraintKey)
	{
		// do something here
		//assert(false);
	}
	
	void InferenceContext::visitBinaryOperator(BinaryOperator &inst, Value* constraintKey)
	{
		constraintKey = constraintKey ? constraintKey : &inst;
		auto left = inst.getOperand(0);
		auto right = inst.getOperand(1);
		
		auto opcode = inst.getOpcode();
		// Division and modulus operations produce a result smaller or equal to the input.
		if (opcode == BinaryOperator::SDiv || opcode == BinaryOperator::SRem || opcode == BinaryOperator::LShr)
		{
			constrain<SpecializesConstraint>(constraintKey, &getUint());
			constrain<GeneralizesConstraint>(constraintKey, left);
			constrain<GeneralizesConstraint>(constraintKey, right);
		}
		else if (opcode == BinaryOperator::UDiv || opcode == BinaryOperator::URem || opcode == BinaryOperator::AShr)
		{
			constrain<SpecializesConstraint>(constraintKey, &getSint());
			constrain<GeneralizesConstraint>(constraintKey, left);
			constrain<GeneralizesConstraint>(constraintKey, right);
		}
		else if (opcode == BinaryOperator::And)
		{
			// A logical AND is sometimes used to truncate integers, even signed ones and sometimes even pointers, so
			// don't infer signedness.
			constrain<GeneralizesConstraint>(constraintKey, left);
			constrain<GeneralizesConstraint>(constraintKey, right);
		}
		else if (opcode == BinaryOperator::Add)
		{
			DisjunctionConstraint* disj = pool.allocate<DisjunctionConstraint>(pool);
			
			auto numeric = &getNum();
			auto pointer = &getPointer();
			// Case 1: both sides are integers
			ConjunctionConstraint* case1 = pool.allocate<ConjunctionConstraint>(pool);
			case1->constrain<SpecializesConstraint>(left, numeric);
			case1->constrain<SpecializesConstraint>(right, numeric);
			case1->constrain<SpecializesConstraint>(constraintKey, left);
			case1->constrain<SpecializesConstraint>(constraintKey, right);
			disj->constraints.push_back(case1);
			
			// Case 2: left side is a pointer, right side is an integer
			ConjunctionConstraint* case2 = pool.allocate<ConjunctionConstraint>(pool);
			case2->constrain<SpecializesConstraint>(left, pointer);
			case2->constrain<SpecializesConstraint>(right, numeric);
			case2->constrain<SpecializesConstraint>(constraintKey, pointer);
			disj->constraints.push_back(case2);
			
			// Case 3: left side is an integer, right side is a pointer
			ConjunctionConstraint* case3 = pool.allocate<ConjunctionConstraint>(pool);
			case3->constrain<SpecializesConstraint>(left, numeric);
			case3->constrain<SpecializesConstraint>(right, pointer);
			case3->constrain<SpecializesConstraint>(constraintKey, pointer);
			disj->constraints.push_back(case3);
			
			constraints.insert({constraintKey, disj});
		}
		// Subtracting pointers results in an integer.
		else if (opcode == BinaryOperator::Sub)
		{
			// Special case for two's complement
			auto constant = dyn_cast<ConstantInt>(left);
			if (constant != nullptr && constant->getLimitedValue() == 0)
			{
				constrain<SpecializesConstraint>(right, &getSint());
				constrain<IsEqualConstraint>(constraintKey, right);
			}
			else
			{
				auto numeric = &getNum();
				auto pointer = &getPointer();
				DisjunctionConstraint* disj = pool.allocate<DisjunctionConstraint>(pool);
				
				// Case 1: both sides are integers
				ConjunctionConstraint* case1 = pool.allocate<ConjunctionConstraint>(pool);
				case1->constrain<SpecializesConstraint>(left, numeric);
				case1->constrain<SpecializesConstraint>(right, numeric);
				case1->constrain<SpecializesConstraint>(constraintKey, left);
				case1->constrain<SpecializesConstraint>(constraintKey, right);
				disj->constraints.push_back(case1);
				
				// Case 2: left side is a pointer, right side is an integer
				ConjunctionConstraint* case2 = pool.allocate<ConjunctionConstraint>(pool);
				case2->constrain<SpecializesConstraint>(left, pointer);
				case2->constrain<SpecializesConstraint>(right, numeric);
				case2->constrain<SpecializesConstraint>(constraintKey, pointer);
				disj->constraints.push_back(case2);
				
				// Case 3: both sides are pointers
				ConjunctionConstraint* case3 = pool.allocate<ConjunctionConstraint>(pool);
				case3->constrain<SpecializesConstraint>(left, pointer);
				case3->constrain<SpecializesConstraint>(right, pointer);
				case3->constrain<SpecializesConstraint>(constraintKey, numeric);
				disj->constraints.push_back(case3);
				
				constraints.insert({constraintKey, disj});
			}
		}
		// Special case for negation
		else if (opcode == BinaryOperator::Xor)
		{
			auto constant = dyn_cast<ConstantInt>(right);
			if (constant == nullptr)
			{
				constant = dyn_cast<ConstantInt>(left);
			}
			
			if (constant != nullptr && constant->getValue() == constant->getType()->getMask())
			{
				auto nonConstant = constant == left ? right : left;
				constrain<SpecializesConstraint>(nonConstant, &getUint());
				constrain<IsEqualConstraint>(constraintKey, nonConstant);
			}
			else
			{
				constrain<SpecializesConstraint>(constraintKey, left);
				constrain<SpecializesConstraint>(constraintKey, right);
			}
		}
		// Everything else should produce an output at least as large as the input.
		else
		{
			constrain<SpecializesConstraint>(constraintKey, left);
			constrain<SpecializesConstraint>(constraintKey, right);
		}
	}
	
	void InferenceContext::visitCastInst(CastInst &inst, Value* constraintKey)
	{
		constraintKey = constraintKey ? constraintKey : &inst;
		// Try to imply that the value had had this type all along. If it doesn't work,
		// fall back to an actual cast.
		auto disj = pool.allocate<DisjunctionConstraint>(pool);
		
		auto type = inst.getType();
		auto casted = inst.getOperand(0);
		if (auto intType = dyn_cast<IntegerType>(type))
		{
			auto num = &getNum(intType->getIntegerBitWidth());
			auto conj = pool.allocate<ConjunctionConstraint>(pool);
			conj->constrain<SpecializesConstraint>(casted, num);
			conj->constrain<IsEqualConstraint>(constraintKey, casted);
			disj->constraints.push_back(conj);
			
			// fall back
			disj->constrain<SpecializesConstraint>(constraintKey, num);
		}
		else if (isa<PointerType>(type))
		{
			auto pointer = &getPointer();
			auto conj = pool.allocate<ConjunctionConstraint>(pool);
			conj->constrain<SpecializesConstraint>(casted, pointer);
			conj->constrain<IsEqualConstraint>(constraintKey, casted);
			disj->constraints.push_back(conj);
			
			// fall back
			disj->constrain<SpecializesConstraint>(constraintKey, pointer);
		}
		else
		{
			assert(!"Implement me");
		}
		
		disj->constrain<IsEqualConstraint>(constraintKey, casted);
		
		constraints.insert({constraintKey, disj});
		constraints.insert({casted, disj});
	}
	
	void InferenceContext::visitTerminatorInst(TerminatorInst &inst, Value* constraintKey)
	{
		// do nothing
	}
	
	void InferenceContext::visitInstruction(Instruction &inst, Value* constraintKey)
	{
		assert(false);
	}
	
	void InferenceContext::visit(Instruction& inst, Value* constraintKey)
	{
		constraintKey = constraintKey ? constraintKey : &inst;
		for (unsigned i = 0; i < inst.getNumOperands(); i++)
		{
			auto op = inst.getOperand(i);
			if (auto constant = dyn_cast<Constant>(op))
			{
				visitConstant(*constant);
			}
		}
		
		InstVisitor<InferenceContext>::visit(inst);
	}
	
	void InferenceContext::visit(Instruction& inst)
	{
		visit(inst, &inst);
	}
	
#pragma mark - InferenceContext misc.
	void InferenceContext::print(raw_ostream& os, ValueToConstraintMap::const_iterator begin, ValueToConstraintMap::const_iterator end) const
	{
		Value* lastKey = nullptr;
		for (auto iter = begin; iter != end; ++iter)
		{
			const auto& pair = *iter;
			if (lastKey != pair.first)
			{
				lastKey = pair.first;
				os << '\n';
				lastKey->print(os);
				os << '\n';
			}
			os << '\t';
			pair.second->print(os);
			os << '\n';
		}
	}
	
	void InferenceContext::dump() const
	{
		raw_os_ostream rerr(cerr);
		print(rerr, constraints.begin(), constraints.end());
	}
	
	void InferenceContext::dump(Value* key) const
	{
		raw_os_ostream rerr(cerr);
		auto range = constraints.equal_range(key);
		print(rerr, range.first, range.second);
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

#pragma mark - Pass Implementation
char TypeInference::ID = 0;

TypeInference::TypeInference() : CallGraphSCCPass(ID)
{
}

const char* TypeInference::getPassName() const
{
	return "Type Inference";
}

void TypeInference::getAnalysisUsage(AnalysisUsage &au) const
{
	au.addRequired<TargetInfo>();
	CallGraphSCCPass::getAnalysisUsage(au);
}

bool TypeInference::runOnSCC(CallGraphSCC &scc)
{
	assert(scc.isSingular());
	const auto& info = getAnalysis<TargetInfo>();
	
	for (auto& node : scc)
	{
		if (auto func = node->getFunction())
		if (!func->empty())
		{
			MemorySSA mssa(*func);
			InferenceContext ctx(info, mssa);
			ctx.visit(*func);
			ctx.dump();
		}
	}
	return false;
}

TypeInference* createTypeInferencePass()
{
	return new TypeInference;
}

INITIALIZE_PASS_BEGIN(TypeInference, "tie", "High-Level Type Inference", false, true)
INITIALIZE_PASS_DEPENDENCY(TargetInfo)
INITIALIZE_PASS_END(TypeInference, "tie", "High-Level Type Inference", false, true)
