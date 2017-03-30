//
// expression_user.h
// Copyright (C) 2015 Félix Cloutier.
// All Rights Reserved.
//
// This file is distributed under the University of Illinois Open Source
// license. See LICENSE.md for details.
//

#ifndef expression_user_hpp
#define expression_user_hpp

#include "expression_use.h"

struct ExpressionUseAllocInfo
{
	unsigned allocated;
	unsigned used;
	
	ExpressionUseAllocInfo()
	: allocated(0), used(0)
	{
	}
	
	ExpressionUseAllocInfo(const ExpressionUseAllocInfo&) = default;
	ExpressionUseAllocInfo(ExpressionUseAllocInfo&&) = default;
	
	ExpressionUseAllocInfo(unsigned n)
	: allocated(n), used(n)
	{
	}
	
	ExpressionUseAllocInfo(unsigned alloc, unsigned use)
	: allocated(alloc), used(use)
	{
	}
};

struct ExpressionUseArrayHead
{
	ExpressionUseAllocInfo allocInfo;
	ExpressionUse* array;
	
	ExpressionUseArrayHead()
	: array(nullptr)
	{
	}
};

// ExpressionUser objects are meant to be allocated by an AstContext object.
// Users 
class ExpressionUser
{
	template<bool B, typename T>
	using OptionallyConst = typename std::conditional<B, typename std::add_const<T>::type, typename std::remove_const<T>::type>::type;
	
public:
	enum UserType : unsigned
	{
		Temporary,
		
		// statements
		StatementMin,
		IfElse = StatementMin,
		Loop,
		Expr,
		Keyword,
		StatementMax,
		
		// expressions
		ExpressionMin = StatementMax,
		Token = ExpressionMin,
		UnaryOperator,
		NAryOperator,
		MemberAccess,
		PointerAccess,
		Call,
		Cast,
		Numeric,
		Ternary,
		Aggregate,
		Subscript,
		Assembly,
		Assignable,
		ExpressionMax,
	};
	
	template<bool IsConst>
	class UseIterator : public std::iterator<std::forward_iterator_tag, OptionallyConst<IsConst, ExpressionUse>>
	{
		const ExpressionUseAllocInfo* allocInfo;
		OptionallyConst<IsConst, ExpressionUse>* useListEnd;
		unsigned index;
		
		void goToNextNonEmptyBuffer();
		
	public:
		UseIterator(std::nullptr_t)
		: allocInfo(nullptr), useListEnd(nullptr), index(0)
		{
		}
		
		UseIterator(OptionallyConst<IsConst, ExpressionUser>* user)
		: allocInfo(&user->allocInfo), index(0)
		{
			useListEnd = reinterpret_cast<OptionallyConst<IsConst, ExpressionUse>*>(user);
			goToNextNonEmptyBuffer();
		}
		
		UseIterator(const UseIterator&) = default;
		UseIterator(UseIterator&&) = default;
		
		OptionallyConst<IsConst, ExpressionUse>& operator*() { return *operator->(); }
		OptionallyConst<IsConst, ExpressionUse>* operator->() { return useListEnd - index - 1; }
		
		template<bool B>
		bool operator==(const UseIterator<B>& that) const { return useListEnd == that.useListEnd && index == that.index; }
		
		template<bool B>
		bool operator!=(const UseIterator<B>& that) const { return !(*this == that); }
		
		UseIterator& operator++();
		UseIterator operator++(int)
		{
			UseIterator copy = *this;
			operator++();
			return copy;
		}
	};
	
	typedef UseIterator<false> iterator;
	typedef UseIterator<true> const_iterator;
	
private:
	ExpressionUseAllocInfo allocInfo;
	UserType userType;
	
	// force class to have a vtable (we cannot have a destructor, virtual or not)
	virtual void anchor();
	
protected:
	virtual void dropAllExpressionReferences();
	virtual void dropAllStatementReferences();
	
public:
	ExpressionUser(UserType type, unsigned allocatedUses, unsigned usedUses)
	: allocInfo(allocatedUses, usedUses), userType(type)
	{
	}
	
	ExpressionUser(UserType type, unsigned inlineUses)
	: ExpressionUser(type, inlineUses, inlineUses)
	{
	}
	
	UserType getUserType() const { return userType; }
	
	ExpressionUse& getOperandUse(unsigned index);
	const ExpressionUse& getOperandUse(unsigned index) const { return const_cast<ExpressionUser*>(this)->getOperandUse(index); }
	
	Expression* getOperand(unsigned index) { return getOperandUse(index).getUse(); }
	const Expression* getOperand(unsigned index) const { return getOperandUse(index).getUse(); }
	
	void setOperand(unsigned index, Expression* expression) { getOperandUse(index).setUse(expression); }
	
	unsigned operands_size() const;
	const_iterator operands_begin() const { return const_iterator(allocInfo.allocated == 0 ? nullptr : this); }
	const_iterator operands_cbegin() const { return operands_begin(); }
	const_iterator operands_end() const { return const_iterator(nullptr); }
	const_iterator operands_cend() const { return operands_end(); }
	iterator operands_begin() { return iterator(allocInfo.allocated == 0 ? nullptr : this); }
	iterator operands_end() { return iterator(nullptr); }
	llvm::iterator_range<iterator> operands() { return llvm::make_range(operands_begin(), operands_end()); }
	llvm::iterator_range<const_iterator> operands() const { return llvm::make_range(operands_begin(), operands_end()); }
	
	void dropAllReferences();
	
	void print(llvm::raw_ostream& os) const;
	void dump() const;
};

// Use this to hold a reference to expressions that must not be dropped yet. (This is kind of like a shared_ptr for
// expressions.) ExpressionReference is primarily meant to be used as a stack variable type.
class [[gnu::packed]] ExpressionReference
{
	ExpressionUseArrayHead useArrayHead;
	ExpressionUse singleUse;
	ExpressionUser user;
	
public:
	ExpressionReference(std::nullptr_t = nullptr);
	ExpressionReference(Expression* expr);
	ExpressionReference(const ExpressionReference& that);
	ExpressionReference(ExpressionReference&& that);
	
	~ExpressionReference();
	
	ExpressionReference& operator=(Expression* expr);
	ExpressionReference& operator=(const ExpressionReference& that);
	ExpressionReference& operator=(ExpressionReference&& that);
	
	Expression* get() const { return const_cast<ExpressionUser&>(user).getOperand(0); }
	
	void reset(Expression* expr = nullptr);
};

template<bool IsConst>
void ExpressionUser::UseIterator<IsConst>::goToNextNonEmptyBuffer()
{
	while (useListEnd != nullptr && index == allocInfo->used)
	{
		auto useListBegin = useListEnd - allocInfo->allocated;
		auto& arrayHead = reinterpret_cast<OptionallyConst<IsConst, ExpressionUseArrayHead>*>(useListBegin)[-1];
		useListEnd = &arrayHead.array[arrayHead.allocInfo.allocated];
		allocInfo = &arrayHead.allocInfo;
		index = 0;
	}
}

template<bool IsConst>
ExpressionUser::UseIterator<IsConst>& ExpressionUser::UseIterator<IsConst>::operator++()
{
	index++;
	goToNextNonEmptyBuffer();
	return *this;
}

#define OPERAND_GET_SET_T(name, type, index) \
	NOT_NULL(type) get##name() { return llvm::cast<type>(getOperand(index)); } \
	NOT_NULL(const type) get##name() const { return llvm::cast<type>(getOperand(index)); } \
	void set##name(NOT_NULL(type) op) { getOperandUse(index).setUse(op); }

#define OPERAND_GET_SET(name, index) OPERAND_GET_SET_T(name, Expression, index)

#endif /* expression_user_hpp */
