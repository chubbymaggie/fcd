//
//  pass_tie.hpp
//  x86Emulator
//
//  Created by Félix on 2015-07-29.
//  Copyright © 2015 Félix Cloutier. All rights reserved.
//

#ifndef pass_tie_cpp
#define pass_tie_cpp

#include "dumb_allocator.h"
#include "llvm_warnings.h"
#include "pass_targetinfo.h"

SILENCE_LLVM_WARNINGS_BEGIN()
#include <llvm/Analysis/CallGraphSCCPass.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/InstVisitor.h>
#include <llvm/Pass.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/Transforms/Utils/MemorySSA.h>
SILENCE_LLVM_WARNINGS_END()

#include <cassert>
#include <functional>
#include <type_traits>
#include <unordered_map>
#include <unordered_set>

namespace tie
{
	class TypeBase
	{
	public:
		enum Category
		{
			Any = 0x00,
			Integral = 0x10,
			DataPointer = 0x11,
			CodePointer = 0x12,
			None = 0xf0,
		};
		
	private:
		Category category;
		
	protected:
		TypeBase(Category category) : category(category)
		{
		}
		
	public:
		inline Category getCategory() const { return category; }
		
		void dump() const;
		virtual void print(llvm::raw_ostream& os) const = 0;
		virtual bool operator<(const TypeBase& that) const = 0;
	};
	
	template<typename T>
	class Type : public TypeBase
	{
	protected:
		Type() : TypeBase(T::category)
		{
		}
		
		virtual bool operator<(const T& that) const = 0;
		
	public:
		static bool classof(const TypeBase* that)
		{
			return that->getCategory() == T::category;
		}
		
		inline bool operator<(const TypeBase& that) const final
		{
			unsigned thisCat = this->getCategory();
			unsigned thatCat = that.getCategory();
			unsigned thisCatShifted = thisCat >> 4;
			unsigned thatCatShifted = thatCat >> 4;
			
			if (thisCatShifted < thatCatShifted)
			{
				return true;
			}
			
			if (thatCatShifted < thisCatShifted || thisCat != thatCat)
			{
				return false;
			}
			
			return operator<(llvm::cast<T>(that));
		}
	};
	
	template<TypeBase::Category Cat>
	class BoundType : public Type<BoundType<Cat>>
	{
	protected:
		virtual bool operator<(const BoundType<Cat>& that) const override
		{
			// BoundType is a singleton instance always equal to itself.
			return false;
		}
		
	public:
		static constexpr TypeBase::Category category = Cat;
		
		inline BoundType()
		{
		}
		
		virtual void print(llvm::raw_ostream& os) const override
		{
			os << "<unrepresentable>";
		}
	};
	
	using AnyType = BoundType<TypeBase::Any>;
	using NoneType = BoundType<TypeBase::None>;
	
	class IntegralType : public Type<IntegralType>
	{
	public:
		enum Tag
		{
			Register,
			Numeric,
			Signed,
			Unsigned,
			Pointer,
		};
		
		static constexpr Category category = Integral;
		
	private:
		Tag tag;
		uint16_t bitCount;
		
	protected:
		virtual bool operator<(const IntegralType& that) const override;
		
	public:
		inline IntegralType(Tag tag, uint16_t bitCount)
		: tag(tag), bitCount(bitCount)
		{
		}
		
		virtual void print(llvm::raw_ostream& os) const override;
	};
	
	// This class can't represent polymorphic relations. This may not be a problem given our scope,
	// but it's something that's worth keeping in mind.
	class DataPointerType : public Type<DataPointerType>
	{
	private:
		const TypeBase& pointee;
		
	protected:
		virtual bool operator<(const DataPointerType&) const override
		{
			// All data pointer types have equal ordering.
			return false;
		}
		
	public:
		static constexpr Category category = DataPointer;
		
		DataPointerType(const TypeBase& pointee) : pointee(pointee)
		{
		}
		
		inline const TypeBase& getPointee() const { return pointee; }
		
		virtual void print(llvm::raw_ostream& os) const override;
	};
	
	class CodePointerType : public Type<CodePointerType>
	{
	public:
		enum Tag
		{
			BasicBlock,
			Function,
		};
		
		static constexpr Category category = CodePointer;
		
	private:
		Tag tag;
		
	protected:
		virtual bool operator<(const CodePointerType& that) const override;
		
	public:
		CodePointerType(Tag tag) : tag(tag)
		{
		}
		
		virtual void print(llvm::raw_ostream& os) const override;
	};
	
	struct TypeOrValue
	{
		llvm::Value* value;
		const TypeBase* type;
		
		TypeOrValue(llvm::Value* value) : value(value), type(nullptr)
		{
		}
		
		TypeOrValue(const TypeBase* type) : value(nullptr), type(type)
		{
		}
		
		void print(llvm::raw_ostream& os) const;
		void dump() const;
	};
	
	struct Constraint
	{
		enum Type : char
		{
			Specializes = ':', // adds information ("inherits from", larger bit count)
			Generalizes = '!', // takes away information (smaller bit count)
			IsEqual = '=',
			
			Conjunction = '&',
			Disjunction = '|',
		};
		
		Type type;
		
		Constraint(Type type)
		: type(type)
		{
		}
		
		virtual void print(llvm::raw_ostream& os) const = 0;
		void dump();
	};
	
	template<Constraint::Type ConstraintType>
	struct CombinatorConstraint : public Constraint
	{
		static bool classof(const Constraint* that)
		{
			return that->type == ConstraintType;
		}
		
		DumbAllocator& pool;
		PooledDeque<Constraint*> constraints;
		
		CombinatorConstraint(DumbAllocator& pool)
		: Constraint(ConstraintType), pool(pool), constraints(pool)
		{
		}
		
		template<typename Constraint, typename... TArgs>
		Constraint* constrain(TArgs&&... args)
		{
			auto constraint = pool.allocate<Constraint>(args...);
			constraints.push_back(constraint);
			return constraint;
		}
		
		virtual void print(llvm::raw_ostream& os) const override
		{
			os << '(';
			auto iter = constraints.begin();
			if (iter != constraints.end())
			{
				(*iter)->print(os);
				for (++iter; iter != constraints.end(); ++iter)
				{
					os << ' ' << (char)ConstraintType << ' ';
					(*iter)->print(os);
				}
			}
			os << ')';
		}
	};
	
	using ConjunctionConstraint = CombinatorConstraint<Constraint::Conjunction>;
	using DisjunctionConstraint = CombinatorConstraint<Constraint::Disjunction>;
	
	template<Constraint::Type ConstraintType>
	struct BinaryConstraint : public Constraint
	{
		static bool classof(const Constraint* that)
		{
			return that->type == ConstraintType;
		}
		
		llvm::Value* left;
		TypeOrValue right;
		
		BinaryConstraint(llvm::Value* left, TypeOrValue right)
		: Constraint(ConstraintType), left(left), right(right)
		{
		}
		
		virtual void print(llvm::raw_ostream& os) const override
		{
			os << "value<";
			left->printAsOperand(os);
			os << "> " << (char)ConstraintType << ' ';
			right.print(os);
		}
	};
	
	using SpecializesConstraint = BinaryConstraint<Constraint::Specializes>;
	using GeneralizesConstraint = BinaryConstraint<Constraint::Specializes>;
	using IsEqualConstraint = BinaryConstraint<Constraint::IsEqual>;
	
	class InferenceContext : public llvm::InstVisitor<InferenceContext>
	{
		const TargetInfo& target;
		llvm::MemorySSA& mssa;
		DumbAllocator pool;
		std::unordered_set<llvm::Value*> visited;
		std::unordered_multimap<llvm::Value*, Constraint*> constraints;
		
		template<typename Constraint, typename... TArgs>
		Constraint* constrain(llvm::Value* value, TArgs&&... args)
		{
			auto constraint = pool.allocate<Constraint>(value, args...);
			addConstraintToValues(constraint, value, args...);
			return constraint;
		}
		
		template<typename... TArgs>
		void addConstraintToValues(Constraint* c, TypeOrValue tv, TArgs&&... values)
		{
			addConstraintToValues(c, tv);
			addConstraintToValues(c, values...);
		}
		
		void addConstraintToValues(Constraint* c, TypeOrValue tv)
		{
			if (auto value = tv.value)
			{
				constraints.insert({value, c});
			}
		}
		
	public:
		InferenceContext(const TargetInfo& target, llvm::MemorySSA& ssa);
		
		void dump() const;
		void dump(llvm::Value* key) const;
		
		static const AnyType& getAny();
		static const NoneType& getNone();
		const IntegralType& getBoolean();
		const IntegralType& getReg(unsigned width = 0);
		const IntegralType& getNum(unsigned width = 0);
		const IntegralType& getSint(unsigned width = 0);
		const IntegralType& getUint(unsigned width = 0);
		static const CodePointerType& getFunctionPointer();
		static const CodePointerType& getBasicBlockPointer();
		const IntegralType& getPointer();
		const DataPointerType& getPointerTo(const TypeBase& pointee);
		
		void visitICmpInst(llvm::ICmpInst& inst);
		void visitAllocaInst(llvm::AllocaInst& inst);
		void visitLoadInst(llvm::LoadInst& inst);
		void visitStoreInst(llvm::StoreInst& inst);
		void visitGetElementPtrInst(llvm::GetElementPtrInst& inst);
		void visitPHINode(llvm::PHINode& inst);
		void visitSelectInst(llvm::SelectInst& inst);
		void visitCallInst(llvm::CallInst& inst);
		
		void visitBinaryOperator(llvm::BinaryOperator& inst);
		void visitCastInst(llvm::CastInst& inst);
		void visitTerminatorInst(llvm::TerminatorInst& inst);
		void visitInstruction(llvm::Instruction& inst);
		void visitConstant(llvm::Constant& constant);
	};
}

class TypeInference : public llvm::CallGraphSCCPass
{
public:
	static char ID;
	
	TypeInference();
	
	virtual const char* getPassName() const override;
	virtual void getAnalysisUsage(llvm::AnalysisUsage& au) const override;
	virtual bool runOnSCC(llvm::CallGraphSCC& scc) override;
};

namespace llvm
{
	void initializeTypeInferencePass(PassRegistry& pr);
}

#endif /* pass_tie_cpp */
