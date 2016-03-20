//
// expression_user.h
// Copyright (C) 2015 Félix Cloutier.
// All Rights Reserved.
//
// This file is part of fcd.
// 
// fcd is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
// 
// fcd is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
// 
// You should have received a copy of the GNU General Public License
// along with fcd.  If not, see <http://www.gnu.org/licenses/>.
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
		// statements
		StatementMin,
		Noop = StatementMin,
		Sequence,
		IfElse,
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
	
	// force class to have a vtable
	virtual void anchor();
	
protected:
	ExpressionUse& insertUseAtEnd();
	iterator erase(iterator iter); // protected because not every class will want to expose it
	
public:
	ExpressionUser(UserType type, unsigned allocatedUses, unsigned usedUses)
	: userType(type), allocInfo(allocatedUses, usedUses)
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
	iterator operands_begin() { return iterator(this); }
	iterator operands_end() { return iterator(nullptr); }
	llvm::iterator_range<iterator> operands() { return llvm::make_range(operands_begin(), operands_end()); }
	llvm::iterator_range<const_iterator> operands() const { return llvm::make_range(operands_begin(), operands_end()); }
	
	void print(llvm::raw_ostream& os) const;
	void dump() const;
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
