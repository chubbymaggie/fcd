//
// type_printer.cpp
// Copyright (C) 2015 Félix Cloutier.
// All Rights Reserved.
//
// This file is distributed under the University of Illinois Open Source
// license. See LICENSE.md for details.
//

#include "type_printer.h"

#include <llvm/Support/Casting.h>
#include <llvm/Support/ErrorHandling.h>

using namespace llvm;
using namespace std;

void CTypePrinter::printMiddleIfAny(raw_ostream& os, const string& middle)
{
	if (middle.size() > 0)
	{
		switch (middle[0])
		{
			case '*':
			case '[':
			case ']':
			case '(':
			case ')':
			case '{':
			case '}':
				break;
				
			default:
				os << ' ';
				break;
		}
		os << middle;
	}
}

void CTypePrinter::print(raw_ostream& os, const VoidExpressionType&, string middle)
{
	os << "void";
	printMiddleIfAny(os, middle);
}

void CTypePrinter::print(raw_ostream& os, const IntegerExpressionType& intTy, string middle)
{
	if (intTy.getBits() == 1)
	{
		os << "bool";
	}
	else
	{
		os << (intTy.isSigned() ? "" : "u") << "int" << intTy.getBits() << "_t";
	}
	printMiddleIfAny(os, middle);
}

void CTypePrinter::print(raw_ostream& os, const PointerExpressionType& pointerTy, string middle)
{
	string tempMiddle;
	raw_string_ostream midOs(tempMiddle);
	const auto& nestedType = pointerTy.getNestedType();
	bool wrapWithParentheses = isa<ArrayExpressionType>(nestedType) || isa<FunctionExpressionType>(nestedType);
	
	if (wrapWithParentheses) midOs << '(';
	midOs << '*';
	printMiddleIfAny(midOs, middle);
	if (wrapWithParentheses) midOs << ')';
	
	print(os, nestedType, move(midOs.str()));
}

void CTypePrinter::print(raw_ostream& os, const ArrayExpressionType& arrayTy, string middle)
{
	raw_string_ostream(middle) << '[' << arrayTy.size() << ']';
	print(os, arrayTy.getNestedType(), move(middle));
}

void CTypePrinter::print(raw_ostream& os, const StructExpressionType& structTy, string middle)
{
	if (structTy.getName().length() > 0)
	{
		os << "struct " << structTy.getName();
	}
	else
	{
		os << "struct {";
		if (structTy.size() > 0)
		{
			os << ' ';
			for (auto iter = structTy.begin(); iter != structTy.end(); ++iter)
			{
				print(os, iter->type, iter->name);
				os << "; ";
			}
		}
		os << "} ";
	}
	os << move(middle);
}

void CTypePrinter::print(raw_ostream& os, const FunctionExpressionType& funcTy, string middle)
{
	string result;
	raw_string_ostream rs(result);
	rs << middle << '(';
	
	auto iter = funcTy.begin();
	if (iter != funcTy.end())
	{
		print(rs, iter->type, iter->name);
		for (++iter; iter != funcTy.end(); ++iter)
		{
			rs << ", ";
			print(rs, iter->type, iter->name);
		}
	}
	
	rs << ')';
	print(os, funcTy.getReturnType(), move(rs.str()));
}

void CTypePrinter::declare(raw_ostream& os, const ExpressionType& type, const string& identifier)
{
	print(os, type, identifier);
}

void CTypePrinter::print(raw_ostream& os, const ExpressionType& type, string middle)
{
	switch (type.getType())
	{
		case ExpressionType::Void:
			return print(os, cast<VoidExpressionType>(type), move(middle));
		case ExpressionType::Integer:
			return print(os, cast<IntegerExpressionType>(type), move(middle));
		case ExpressionType::Pointer:
			return print(os, cast<PointerExpressionType>(type), move(middle));
		case ExpressionType::Array:
			return print(os, cast<ArrayExpressionType>(type), move(middle));
		case ExpressionType::Structure:
			return print(os, cast<StructExpressionType>(type), move(middle));
		case ExpressionType::Function:
			return print(os, cast<FunctionExpressionType>(type), move(middle));
		default:
			llvm_unreachable("unhandled expression type");
	}
}
