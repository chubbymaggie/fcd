//
// pass_signext.cpp
// Copyright (C) 2017 Félix Cloutier.
// All Rights Reserved.
//
// This file is distributed under the University of Illinois Open Source
// license. See LICENSE.md for details.
//

#include "passes.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/PatternMatch.h>

using namespace llvm;
using namespace llvm::PatternMatch;
using namespace std;

namespace
{
	// Has to happen before instcombine
	struct SignExt : public FunctionPass
	{
		static char ID;
		
		SignExt() : FunctionPass(ID)
		{
		}
		
		virtual bool runOnFunction(Function& fn) override
		{
			bool changed = false;
			
			for (BasicBlock& bb : fn)
			{
				for (Instruction& inst : bb)
				{
					if (inst.getOpcode() == Instruction::Or)
					{
						auto& orInst = cast<BinaryOperator>(inst);
						changed |= handleOrInst(orInst);
					}
				}
			}
			
			return changed;
		}
		
		bool handleOrInst(BinaryOperator& orInst)
		{
			// (Sign extension sequence)
			// The form that we're trying to optimize is:
			//  %1 = /* i32 */
			//  %2 = ashr i32 %1, 31
			//  %3 = zext i32 %2 to i64
			//  %4 = shl nuw i64 %3, 32
			//  %5 = zext i32 %1 to i64
			//  %6 = or i64 %4, %5
			// Look for OR instructions and check if they match this pattern. If so, insert a sext instruction around
			// the OR and replace the OR's uses with it.
			
			BinaryOperator* shiftLeft = nullptr;	//  %4 = shl nuw i64 %3, 32
			ZExtInst* zExtOriginal = nullptr;		//  %5 = zext i32 %1 to i64
			if (!tryCastOrOperands(orInst, zExtOriginal, shiftLeft) && !tryCastOrOperands(orInst, shiftLeft, zExtOriginal))
			{
				return false;
			}
			
			if (auto zExtSign = dyn_cast<ZExtInst>(shiftLeft->getOperand(0)))
			if (auto shiftRight = dyn_cast<BinaryOperator>(zExtSign->getOperand(0)))
			if (shiftRight->getOpcode() == Instruction::AShr)
			if (auto shiftLeftAmountAP = dyn_cast<ConstantInt>(shiftLeft->getOperand(1)))
			if (auto shiftRightAmountAP = dyn_cast<ConstantInt>(shiftRight->getOperand(1)))
			{
				auto initialValue = shiftRight->getOperand(0);
				
				// This should be (bit length of original int) - 1.
				auto shiftRightAmount = shiftRightAmountAP->getLimitedValue();
				
				// This should be (extended length) - (original length).
				auto shiftLeftAmount = shiftLeftAmountAP->getLimitedValue();
				
				auto predictedInitialWidth = shiftRightAmount + 1;
				auto predictedFinalWidth = predictedInitialWidth + shiftLeftAmount;
				
				auto initialWidth = initialValue->getType()->getIntegerBitWidth();
				auto finalWidth = orInst.getType()->getIntegerBitWidth();
				
				if (predictedInitialWidth > initialWidth || predictedFinalWidth > finalWidth)
				{
					// Sign extension doesn't make sense.
					assert(false);
					return false;
				}
				
				// Insert trunc/ext as necessary to simplify pattern next to orInst.
				if (predictedInitialWidth < initialWidth)
				{
					auto truncatedType = Type::getIntNTy(orInst.getContext(), static_cast<unsigned>(predictedInitialWidth));
					initialValue = CastInst::Create(Instruction::Trunc, initialValue, truncatedType, "", &orInst);
				}
				
				auto extendedType = Type::getIntNTy(orInst.getContext(), static_cast<unsigned>(predictedFinalWidth));
				auto extended = CastInst::Create(Instruction::SExt, initialValue, extendedType, "", &orInst);
				if (predictedFinalWidth < finalWidth)
				{
					extended = CastInst::Create(Instruction::ZExt, extended, orInst.getType(), "", &orInst);
				}
				
				orInst.replaceAllUsesWith(extended);
				return true;
			}
			
			return false;
		}
		
		bool tryCastOrOperands(BinaryOperator& orInst, ZExtInst*& zExtOriginal, BinaryOperator*& shiftLeft) const
		{
			zExtOriginal = dyn_cast<ZExtInst>(orInst.getOperand(0));
			shiftLeft = dyn_cast<BinaryOperator>(orInst.getOperand(1));
			return zExtOriginal != nullptr && shiftLeft != nullptr && shiftLeft->getOpcode() == Instruction::Shl;
		}
		
		bool tryCastOrOperands(BinaryOperator& orInst, BinaryOperator*& shiftLeft, ZExtInst*& zExtOriginal) const
		{
			shiftLeft = dyn_cast<BinaryOperator>(orInst.getOperand(0));
			zExtOriginal = dyn_cast<ZExtInst>(orInst.getOperand(1));
			return zExtOriginal != nullptr && shiftLeft != nullptr && shiftLeft->getOpcode() == Instruction::Shl;
		}
	};
	
	char SignExt::ID = 0;
	
	RegisterPass<SignExt> signExt("signext", "Simplify sign extension sequences");
}

FunctionPass* createSignExtPass()
{
	return new SignExt;
}
