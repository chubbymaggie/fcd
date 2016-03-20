//
// pass_simplifyconditions.cpp
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

#include "pass_simplifyexpressions.h"
#include "visitor.h"

using namespace llvm;
using namespace std;

namespace
{
	inline UnaryOperatorExpression* match(Expression* expr, UnaryOperatorExpression::UnaryOperatorType type)
	{
		if (auto unary = dyn_cast_or_null<UnaryOperatorExpression>(expr))
		if (unary->getType() == type)
		{
			return unary;
		}
		
		return nullptr;
	}
	
	UnaryOperatorExpression* matchNegation(Expression* expr)
	{
		return match(expr, UnaryOperatorExpression::LogicalNegate);
	}
	
	pair<Expression*, bool> countNegationDepth(Expression& expr)
	{
		bool isNegated = false;
		Expression* canonical;
		for (canonical = &expr; auto negation = matchNegation(canonical); canonical = negation->getOperand())
		{
			isNegated = !isNegated;
		}
		return make_pair(canonical, isNegated);
	}
	
	class ExpressionSimplifierVisitor : public AstVisitor<ExpressionSimplifierVisitor, false>
	{
		AstContext& ctx;
		
		void collectExpressionTerms(NAryOperatorExpression& baseExpression, SmallPtrSetImpl<Expression*>& trueTerms, SmallPtrSetImpl<Expression*>& falseTerms)
		{
			for (ExpressionUse& use : baseExpression.operands())
			{
				auto expr = use.getUse();
				if (auto nary = dyn_cast<NAryOperatorExpression>(expr))
				{
					if (nary->getType() == baseExpression.getType())
					{
						collectExpressionTerms(*nary, trueTerms, falseTerms);
						continue;
					}
				}
				
				auto isNegated = countNegationDepth(*expr);
				(isNegated.second ? falseTerms : trueTerms).insert(isNegated.first);
			}
		}
		
		Expression* removeIdenticalTerms(NAryOperatorExpression& nary)
		{
			if (nary.getType() != NAryOperatorExpression::ShortCircuitOr && nary.getType() != NAryOperatorExpression::ShortCircuitAnd)
			{
				return &nary;
			}
			
			// This is allowed on both && and ||, since (a && a) == a and (a || a) == a.
			SmallPtrSet<Expression*, 16> trueTerms;
			SmallPtrSet<Expression*, 16> falseTerms;
			collectExpressionTerms(nary, trueTerms, falseTerms);
			
			auto trueExpression = ctx.expressionForTrue();
			SmallVector<Expression*, 16> expressions;
			for (Expression* falseTerm : falseTerms)
			{
				if (trueTerms.count(falseTerm) != 0)
				{
					// this will either be a totaulogy or a contradiction depending on the logical operator
					auto trueValue = ctx.expressionForTrue();
					return nary.getType() == NAryOperatorExpression::ShortCircuitOr ? trueValue : ctx.negate(trueValue);
				}
				
				if (falseTerm == trueExpression)
				{
					// contains a !true (== false)
					if (nary.getType() == NAryOperatorExpression::ShortCircuitAnd)
					{
						// Expression dominated
						return ctx.negate(falseTerm);
					}
					// do not insert then, since it has no effect
				}
				else
				{
					expressions.push_back(falseTerm);
				}
			}
			
			for (Expression* trueTerm : trueTerms)
			{
				if (trueTerm == trueExpression)
				{
					if (nary.getType() == NAryOperatorExpression::ShortCircuitOr)
					{
						return trueTerm;
					}
				}
				else
				{
					expressions.push_back(trueTerm);
				}
			}
			
			unsigned i = 0;
			auto result = ctx.nary(nary.getType(), static_cast<unsigned>(expressions.size()));
			for (Expression* expression : expressions)
			{
				result->setOperand(i, expression);
				++i;
			}
			return result;
		}
		
	public:
		ExpressionSimplifierVisitor(AstContext& ctx)
		: ctx(ctx)
		{
		}
		
		void visitUnaryOperator(UnaryOperatorExpression& unary)
		{
			visit(*unary.getOperand());
			auto operand = unary.getOperand(); // might have changed
			
			if (unary.getType() == UnaryOperatorExpression::LogicalNegate)
			{
				if (auto innerNegate = match(operand, UnaryOperatorExpression::LogicalNegate))
				{
					unary.replaceAllUsesWith(innerNegate->getOperand());
				}
				else if (auto innerNary = dyn_cast<NAryOperatorExpression>(operand))
				{
					auto op = innerNary->getType();
					if (innerNary->operands_size() == 2 && op >= NAryOperatorExpression::ComparisonMin && op <= NAryOperatorExpression::ComparisonMax)
					{
						auto flippedOp = static_cast<NAryOperatorExpression::NAryOperatorType>(op ^ 1);
						auto replacement = ctx.nary(flippedOp, innerNary->getOperand(0), innerNary->getOperand(1));
						unary.replaceAllUsesWith(replacement);
					}
				}
			}
			else if (unary.getType() == UnaryOperatorExpression::Dereference)
			{
				if (auto innerAddressOf = match(operand, UnaryOperatorExpression::AddressOf))
				{
					unary.replaceAllUsesWith(innerAddressOf->getOperand());
				}
			}
		}
		
		void visitNAryOperator(NAryOperatorExpression& nary)
		{
			// Negation distribution kills term collection, so do that first before visiting child nodes
			Expression* result = removeIdenticalTerms(nary);
			for (ExpressionUse& use : result->operands())
			{
				visit(*use.getUse());
			}
			nary.replaceAllUsesWith(result);
		}
		
		void visitMemberAccess(MemberAccessExpression& memberAccess)
		{
			visit(*memberAccess.getBaseExpression());
		}
		
		void visitTernary(TernaryExpression& ternary)
		{
			visit(*ternary.getCondition());
			visit(*ternary.getTrueValue());
			visit(*ternary.getFalseValue());
		}
		
		void visitCall(CallExpression& call)
		{
			visit(*call.getCallee());
			for (ExpressionUse& use : call.params())
			{
				visit(*use.getUse());
			}
		}
		
		void visitCast(CastExpression& cast)
		{
			visit(*cast.getCastValue());
		}
		
		void visitAggregate(AggregateExpression& agg)
		{
			for (ExpressionUse& use : agg.operands())
			{
				visit(*use.getUse());
			}
		}
		
		void visitSubscript(SubscriptExpression& subscript)
		{
			visit(*subscript.getPointer());
			visit(*subscript.getIndex());
			
			if (auto addressOf = match(subscript.getPointer(), UnaryOperatorExpression::AddressOf))
			if (auto constantIndex = dyn_cast<NumericExpression>(subscript.getIndex()))
			if (constantIndex->ui64 == 0)
			{
				subscript.replaceAllUsesWith(addressOf->getOperand());
			}
		}
		
		void visitNumeric(NumericExpression& numeric)
		{
		}
		
		void visitToken(TokenExpression& token)
		{
		}
		
		void visitAssembly(AssemblyExpression& assembly)
		{
		}
		
		void visitAssignable(AssignableExpression& assignable)
		{
		}
		
		void visitDefault(ExpressionUser& user)
		{
			llvm_unreachable("unimplemented expression simplification case");
		}
	};
	
	class StatementSimplifierVisitor : public AstVisitor<StatementSimplifierVisitor, false>
	{
		ExpressionSimplifierVisitor exprVisitor;
		
	public:
		StatementSimplifierVisitor(AstContext& ctx)
		: exprVisitor(ctx)
		{
		}
		
		void visitNoop(NoopStatement& noop)
		{
		}
		
		void visitSequence(SequenceStatement& sequence)
		{
			for (Statement* statement : sequence)
			{
				visit(*statement);
			}
		}
		
		void visitIfElse(IfElseStatement& ifElse)
		{
			exprVisitor.visit(*ifElse.getCondition());
			visit(*ifElse.getIfBody());
			if (auto elseBody = ifElse.getElseBody())
			{
				visit(*elseBody);
			}
		}
		
		void visitLoop(LoopStatement& loop)
		{
			exprVisitor.visit(*loop.getCondition());
			visit(*loop.getLoopBody());
		}
		
		void visitKeyword(KeywordStatement& keyword)
		{
			if (auto operand = keyword.getOperand())
			{
				exprVisitor.visit(*operand);
			}
		}
		
		void visitExpr(ExpressionStatement& expression)
		{
			if (auto expr = expression.getExpression())
			{
				exprVisitor.visit(*expr);
			}
		}
		
		void visitDefault(ExpressionUser& user)
		{
			llvm_unreachable("unimplemented expression simplification case");
		}
	};
}

void AstSimplifyExpressions::doRun(FunctionNode &fn)
{
	StatementSimplifierVisitor(fn.getContext()).visit(*fn.getBody());
}

const char* AstSimplifyExpressions::getName() const
{
	return "Simplify conditions";
}
