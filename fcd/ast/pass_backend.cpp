//
// pass_backend.cpp
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

#include "pass_backend.h"
#include "function.h"
#include "grapher.h"
#include "metadata.h"
#include "passes.h"

SILENCE_LLVM_WARNINGS_BEGIN()
#include <llvm/IR/Constants.h>
#include <llvm/ADT/DepthFirstIterator.h>
#include <llvm/ADT/PostOrderIterator.h>
#include <llvm/Analysis/RegionInfo.h>
#include <llvm/IR/Instructions.h>
#include <llvm/Support/raw_os_ostream.h>
SILENCE_LLVM_WARNINGS_END()

#include <algorithm>
#include <deque>
#include <unordered_set>
#include <vector>

using namespace llvm;
using namespace std;

#ifdef DEBUG
#pragma mark Debug
extern void print(raw_ostream& os, const SmallVector<Expression*, 4>& expressionList, const char* elemSep)
{
	os << '(';
	for (auto iter = expressionList.begin(); iter != expressionList.end(); iter++)
	{
		if (iter != expressionList.begin())
		{
			os << ' ' << elemSep << ' ';
		}
		(*iter)->print(os);
	}
	os << ')';
}

extern void dump(const SmallVector<Expression*, 4>& expressionList, const char* elemSep)
{
	raw_ostream& os = errs();
	print(os, expressionList, elemSep);
	os << '\n';
}

extern void dump(const SmallVector<SmallVector<Expression*, 4>, 4>& expressionList, const char* rowSep, const char* elemSep)
{
	raw_ostream& os = errs();
	for (auto iter = expressionList.begin(); iter != expressionList.end(); iter++)
	{
		if (iter != expressionList.begin())
		{
			os << ' ' << rowSep << ' ';
		}
		print(os, *iter, elemSep);
	}
	os << '\n';
}
#endif

namespace
{
#pragma mark - Reaching conditions, boolean logic
	template<typename TCollection>
	inline Expression* coalesce(AstContext& ctx, NAryOperatorExpression::NAryOperatorType type, const TCollection& coll)
	{
		if (coll.size() == 0)
		{
			return nullptr;
		}
		
		if (coll.size() == 1)
		{
			return coll[0];
		}
		
		auto nary = ctx.nary(type, static_cast<unsigned>(coll.size()));
		unsigned i = 0;
		for (Expression* exp : coll)
		{
			nary->setOperand(i, exp);
			++i;
		}
		return nary;
	}
	
	class ReachingConditions
	{
	public:
		unordered_map<Statement*, SmallVector<SmallVector<Expression*, 4>, 4>> conditions;
		
	private:
		AstGrapher& grapher;
		FunctionNode& output;
		
		void build(AstGraphNode* currentNode, SmallVector<Expression*, 4>& conditionStack, vector<AstGraphNode*>& visitStack)
		{
			// Ignore back edges.
			if (find(visitStack.begin(), visitStack.end(), currentNode) != visitStack.end())
			{
				return;
			}
			
			visitStack.push_back(currentNode);
			conditions[currentNode->node].push_back(conditionStack);
			if (currentNode->hasExit())
			{
				// Exit reached by sequentially following structured region. No additional condition here.
				build(grapher.getGraphNodeFromEntry(currentNode->getExit()), conditionStack, visitStack);
			}
			else
			{
				// Exit is unstructured. New conditions may apply.
				auto terminator = currentNode->getEntry()->getTerminator();
				if (auto branch = dyn_cast<BranchInst>(terminator))
				{
					if (branch->isConditional())
					{
						Expression* trueExpr = output.valueFor(*branch->getCondition());
						conditionStack.push_back(trueExpr);
						build(grapher.getGraphNodeFromEntry(branch->getSuccessor(0)), conditionStack, visitStack);
						conditionStack.pop_back();
						
						Expression* falseExpr = output.getContext().negate(trueExpr);
						conditionStack.push_back(falseExpr);
						build(grapher.getGraphNodeFromEntry(branch->getSuccessor(1)), conditionStack, visitStack);
						conditionStack.pop_back();
					}
					else
					{
						// Unconditional branch
						build(grapher.getGraphNodeFromEntry(branch->getSuccessor(0)), conditionStack, visitStack);
					}
				}
				else if (!isa<ReturnInst>(terminator) && !isa<UnreachableInst>(terminator))
				{
					llvm_unreachable("implement missing terminator type");
				}
			}
			visitStack.pop_back();
		}
		
	public:
		
		ReachingConditions(FunctionNode& output, AstGrapher& grapher)
		: grapher(grapher), output(output)
		{
		}
		
		void buildSumsOfProducts(AstGraphNode* regionStart, AstGraphNode* regionEnd)
		{
			SmallVector<Expression*, 4> expressionStack;
			vector<AstGraphNode*> visitStack { regionEnd };
			build(regionStart, expressionStack, visitStack);
		}
	};
	
	void expandToProductOfSums(
		SmallVector<Expression*, 4>& stack,
		SmallVector<SmallVector<Expression*, 4>, 4>& output,
		SmallVector<SmallVector<Expression*, 4>, 4>::const_iterator sumOfProductsIter,
		SmallVector<SmallVector<Expression*, 4>, 4>::const_iterator sumOfProductsEnd)
	{
		if (sumOfProductsIter == sumOfProductsEnd)
		{
			output.push_back(stack);
		}
		else
		{
			auto nextRow = sumOfProductsIter + 1;
			for (Expression* expr : *sumOfProductsIter)
			{
				stack.push_back(expr);
				expandToProductOfSums(stack, output, nextRow, sumOfProductsEnd);
				stack.pop_back();
			}
		}
	}
	
	SmallVector<SmallVector<Expression*, 4>, 4> simplifySumOfProducts(DumbAllocator& pool, SmallVector<SmallVector<Expression*, 4>, 4>& sumOfProducts)
	{
		if (sumOfProducts.size() == 0)
		{
			// return empty vector
			return sumOfProducts;
		}
		
		SmallVector<SmallVector<Expression*, 4>, 4> productOfSums;
		
		// This is a NP-complete problem, so we'll have to cut corners a little bit to make things acceptable.
		// The `expr` vector is in disjunctive normal form: each inner vector ANDs ("multiplies") all of its operands,
		// and each vector is ORed ("added"). In other words, we have a sum of products.
		// By the end, we want a product of sums, since this simplifies expression matching to nest if statements.
		// In this specific instance of the problem, we know that common terms will arise often (because of deeply
		// nested conditions), but contradictions probably never will.
		
		// Step 1: collect identical terms.
		if (sumOfProducts.size() > 1)
		{
			auto otherProductsBegin = sumOfProducts.begin();
			auto& firstProduct = *otherProductsBegin;
			otherProductsBegin++;
			
			auto termIter = firstProduct.begin();
			while (termIter != firstProduct.end())
			{
				SmallVector<SmallVector<Expression*, 4>::iterator, 4> termLocations;
				for (auto iter = otherProductsBegin; iter != sumOfProducts.end(); iter++)
				{
					auto termLocation = find_if(iter->begin(), iter->end(), [&](Expression* that)
					{
						return *that == **termIter;
					});
					
					if (termLocation == iter->end())
					{
						break;
					}
					termLocations.push_back(termLocation);
				}
				
				if (termLocations.size() == sumOfProducts.size() - 1)
				{
					// The term exists in every product. Isolate it.
					productOfSums.emplace_back();
					productOfSums.back().push_back(*termIter);
					size_t i = 0;
					for (auto iter = otherProductsBegin; iter != sumOfProducts.end(); iter++)
					{
						iter->erase(termLocations[i]);
						i++;
					}
					termIter = firstProduct.erase(termIter);
				}
				else
				{
					termIter++;
				}
			}
			
			// Erase empty products.
			auto possiblyEmptyIter = sumOfProducts.begin();
			while (possiblyEmptyIter != sumOfProducts.end())
			{
				if (possiblyEmptyIter->size() == 0)
				{
					possiblyEmptyIter = sumOfProducts.erase(possiblyEmptyIter);
				}
				else
				{
					possiblyEmptyIter++;
				}
			}
		}
		
		// Step 2: transform remaining items in sumOfProducts into a product of sums.
		auto& firstProduct = sumOfProducts.front();
		decltype(productOfSums)::value_type stack;
		for (Expression* expr : firstProduct)
		{
			stack.push_back(expr);
			expandToProductOfSums(stack, productOfSums, sumOfProducts.begin() + 1, sumOfProducts.end());
			stack.pop_back();
		}
		
		// Step 3: visit each sum and delete those in which we find a `A | ~A` tautology.
		auto sumIter = productOfSums.begin();
		while (sumIter != productOfSums.end())
		{
			auto& sum = *sumIter;
			auto iter = sum.begin();
			auto end = sum.end();
			while (iter != end)
			{
				Expression* e = *iter;
				auto negation = end;
				if (auto negated = dyn_cast<UnaryOperatorExpression>(e))
				{
					assert(negated->getType() == UnaryOperatorExpression::LogicalNegate);
					e = negated->getOperand();
					negation = find_if(iter + 1, end, [&](Expression* that)
					{
						return *that == *e;
					});
				}
				else
				{
					negation = find_if(iter + 1, end, [&](Expression* that)
					{
						if (auto negated = dyn_cast<UnaryOperatorExpression>(that))
						{
							assert(negated->getType() == UnaryOperatorExpression::LogicalNegate);
							return *negated->getOperand() == *e;
						}
						return false;
					});
				}
				
				if (negation != end)
				{
					// This sum is always true, clear it and stop looking.
					// Setting `end` to the beginning of the sum causes it to be cleared
					// and removed from the product of sums.
					end = sum.begin();
					break;
				}
				else
				{
					iter++;
				}
			}
			
			sum.erase(end, sum.end());
			
			// Delete empty sums.
			if (sum.size() == 0)
			{
				sumIter = productOfSums.erase(sumIter);
			}
			else
			{
				sumIter++;
			}
		}
		
		return productOfSums;
	}
	
#pragma mark - Graph stuff
	void postOrder(AstGrapher& grapher, vector<Statement*>& into, unordered_set<AstGraphNode*>& visited, AstGraphNode* current, AstGraphNode* exit)
	{
		if (visited.count(current) == 0)
		{
			visited.insert(current);
			if (current->hasExit())
			{
				postOrder(grapher, into, visited, grapher.getGraphNodeFromEntry(current->getExit()), exit);
			}
			else
			{
				for (auto succ : successors(current->getEntry()))
				{
					postOrder(grapher, into, visited, grapher.getGraphNodeFromEntry(succ), exit);
				}
			}
			into.push_back(current->node);
		}
	}
	
	vector<Statement*> reversePostOrder(AstGrapher& grapher, AstGraphNode* entry, AstGraphNode* exit)
	{
		vector<Statement*> result;
		unordered_set<AstGraphNode*> visited { exit };
		postOrder(grapher, result, visited, entry, exit);
		reverse(result.begin(), result.end());
		return result;
	}
	
#pragma mark - Region Structurization
	void addBreakStatements(FunctionNode& output, AstGrapher& grapher, DominatorTree& domTree, BasicBlock& entryNode, BasicBlock* exitNode)
	{
		if (exitNode == nullptr)
		{
			// Exit is the end of the function. There should already be return statements everywhere required.
			return;
		}
		
		for (BasicBlock* pred : predecessors(exitNode))
		{
			if (domTree.dominates(&entryNode, pred))
			{
				// The sequence for this block will need a break statement.
				auto sequence = cast<SequenceStatement>(grapher.getGraphNodeFromEntry(pred)->node);
				auto terminator = pred->getTerminator();
				if (auto branch = dyn_cast<BranchInst>(terminator))
				{
					auto& context = output.getContext();
					Statement* breakStatement = context.breakStatement();
					if (branch->isConditional())
					{
						Expression* cond = output.valueFor(*branch->getCondition());
						if (exitNode == branch->getSuccessor(1))
						{
							cond = output.getContext().negate(cond);
						}
						breakStatement = context.ifElse(cond, breakStatement);
					}
					sequence->pushBack(breakStatement);
				}
				else
				{
					llvm_unreachable("implement missing terminator type");
				}
			}
		}
	}
	
	SequenceStatement* structurizeRegion(FunctionNode& output, AstGrapher& grapher, BasicBlock& entry, BasicBlock* exit)
	{
		AstGraphNode* astEntry = grapher.getGraphNodeFromEntry(&entry);
		AstGraphNode* astExit = grapher.getGraphNodeFromEntry(exit);
		
		// Build reaching conditions.
		ReachingConditions reach(output, grapher);
		reach.buildSumsOfProducts(astEntry, astExit);
		
		// Structure nodes into `if` statements using reaching conditions. Traverse nodes in topological order (reverse
		// postorder). We can't use LLVM's ReversePostOrderTraversal class here because we're working with a subgraph.
		SequenceStatement* sequence = output.getContext().sequence();
		
		for (Statement* node : reversePostOrder(grapher, astEntry, astExit))
		{
			auto& path = reach.conditions.at(node);
			SmallVector<SmallVector<Expression*, 4>, 4> productOfSums = simplifySumOfProducts(output.getPool(), path);
			
			Statement* toInsert = node;
			for (auto iter = productOfSums.rbegin(); iter != productOfSums.rend(); iter++)
			{
				const auto& sum = *iter;
				if (auto sumExpression = coalesce(output.getContext(), NAryOperatorExpression::ShortCircuitOr, sum))
				{
					toInsert = output.getContext().ifElse(sumExpression, toInsert);
				}
			}
			
			sequence->pushBack(toInsert);
		}
		return sequence;
	}
	
#pragma mark - Post-Dominator Tree with Arbitrary Roots
	// This is a fairly nasty hack that hinges on protected members of DominatorTreeBase.
	// We need it because the post-dominator tree can't find roots on a function with an endless loop.
	class RootedPostDominatorTree : public DominatorTreeBase<BasicBlock>
	{
	public:
		RootedPostDominatorTree()
		: DominatorTreeBase<BasicBlock>(true)
		{
		}
		
		void recalculateWithRoots(Function& fn, const SmallVectorImpl<BasicBlock*>& roots)
		{
			reset();
			Vertex.push_back(nullptr);
			for (BasicBlock* bb : roots)
			{
				assert(bb->getParent() == &fn);
				addRoot(bb);
			}
			Calculate<Function, Inverse<BasicBlock*>>(*this, fn);
		}
		
		static void treeFromIncompleteTree(Function& fn, unique_ptr<DominatorTreeBase<BasicBlock>>& postDomTree)
		{
			SmallVector<BasicBlock*, 1> roots;
			// Find loops, check if they have a node in the existing post-dominator tree. If not, we need a new tree.
			auto loops = SESELoop::findBackEdgeDestinations(fn.getEntryBlock());
			
			// According to this Chris Dodd person, you get an okay post-dominator tree just by picking missing
			// nodes at random. Let's see how that works.
			// http://stackoverflow.com/a/35400454/251153
			for (const auto& pair : loops)
			{
				if (postDomTree->getNode(pair.first) == nullptr)
				{
					roots.push_back(pair.first);
				}
			}
			
			if (roots.size() != 0)
			{
				// add the tree's original roots too (in case it had any)
				const auto& originalRoots = postDomTree->getRoots();
				roots.insert(roots.end(), originalRoots.begin(), originalRoots.end());
				
				auto result = std::make_unique<RootedPostDominatorTree>();
				result->recalculateWithRoots(fn, roots);
				postDomTree = move(result);
			}
		}
	};
	
	BasicBlock* postDominatorOf(DominatorTreeBase<BasicBlock>& postDomTree, BasicBlock& bb)
	{
		if (auto node = postDomTree.getNode(&bb))
		if (auto idom = node->getIDom())
		{
			return idom->getBlock();
		}
		return nullptr;
	}
	
#pragma mark - Other Helpers
	uint64_t getVirtualAddress(FunctionNode& node)
	{
		if (auto address = md::getVirtualAddress(node.getFunction()))
		{
			return address->getLimitedValue();
		}
		return 0;
	}
}

#pragma mark - AST Pass
char AstBackEnd::ID = 0;
static RegisterPass<AstBackEnd> astBackEnd("#ast-backend", "Produce AST from LLVM module");

void AstBackEnd::getAnalysisUsage(llvm::AnalysisUsage &au) const
{
	au.addRequired<DominatorTreeWrapperPass>();
	au.addRequired<PostDominatorTree>();
	au.setPreservesAll();
}

void AstBackEnd::addPass(AstModulePass *pass)
{
	assert(pass != nullptr);
	passes.emplace_back(pass);
}

bool AstBackEnd::runOnModule(llvm::Module &m)
{
	outputNodes.clear();
	
	for (Function& fn : m)
	{
		if (md::isPartOfOutput(fn))
		{
			outputNodes.emplace_back(new FunctionNode(fn));
			output = outputNodes.back().get();
			if (!md::isPrototype(fn))
			{
				runOnFunction(fn);
			}
		}
	}
	
	// sort outputNodes by virtual address, then by name
	sort(outputNodes.begin(), outputNodes.end(), [](unique_ptr<FunctionNode>& a, unique_ptr<FunctionNode>& b)
	{
		auto virtA = getVirtualAddress(*a);
		auto virtB = getVirtualAddress(*b);
		if (virtA < virtB)
		{
			return true;
		}
		else if (virtA == virtB)
		{
			return a->getFunction().getName() < b->getFunction().getName();
		}
		else
		{
			return false;
		}
	});
	
	// run passes
	for (auto& pass : passes)
	{
		pass->run(outputNodes);
	}
	
	return false;
}

void AstBackEnd::runOnFunction(llvm::Function& fn)
{
	grapher.reset(new AstGrapher(pool()));
	
	// Before doing anything, create statements for blocks in reverse post-order. This ensures that values exist
	// before they are used. (Post-order would try to use statements before they were created.)
	for (BasicBlock* block : ReversePostOrderTraversal<BasicBlock*>(&fn.getEntryBlock()))
	{
		grapher->createRegion(*block, *output->basicBlockToStatement(*block));
	}
	
	// Identify loops, then visit basic blocks in post-order. If the basic block if the head
	// of a cyclic region, process the loop. Otherwise, if the basic block is the start of a single-entry-single-exit
	// region, process that region.
	
	auto& domTreeWrapper = getAnalysis<DominatorTreeWrapperPass>(fn);
	domTree = &domTreeWrapper.getDomTree();
	postDomTree->recalculate(fn);
	RootedPostDominatorTree::treeFromIncompleteTree(fn, postDomTree);
	
	// Traverse graph in post-order. Try to detect regions with the post-dominator tree.
	// Cycles are only considered once.
	for (BasicBlock* entry : post_order(&fn.getEntryBlock()))
	{
		BasicBlock* postDominator = entry;
		while (postDominator != nullptr)
		{
			AstGraphNode* graphNode = grapher->getGraphNodeFromEntry(postDominator);
			BasicBlock* exit = graphNode->hasExit()
				? graphNode->getExit()
				: postDominatorOf(*postDomTree, *postDominator);
			
			RegionType region = isRegion(*entry, exit);
			if (region == Acyclic)
			{
				runOnRegion(fn, *entry, exit);
			}
			else if (region == Cyclic)
			{
				runOnLoop(fn, *entry, exit);
			}
			
			if (!domTree->dominates(entry, exit))
			{
				break;
			}
			postDominator = exit;
		}
	}
	
	Statement* bodyStatement = grapher->getGraphNodeFromEntry(&fn.getEntryBlock())->node;
	output->setBody(bodyStatement);
}

void AstBackEnd::runOnLoop(Function& fn, BasicBlock& entry, BasicBlock* exit)
{
	// The SESELoop pass already did the meaningful transformations on the loop region:
	// it's now a single-entry, single-exit region, loop membership has already been refined, etc.
	// We really just have to emit the AST.
	// Basically, we want a "while true" loop with break statements wherever we exit the loop scope.
	
	SequenceStatement* sequence = structurizeRegion(*output, *grapher, entry, exit);
	addBreakStatements(*output, *grapher, *domTree, entry, exit);
	AstContext& ctx = output->getContext();
	Statement* endlessLoop = ctx.loop(ctx.expressionForTrue(), LoopStatement::PreTested, sequence);
	grapher->updateRegion(entry, exit, *endlessLoop);
}

void AstBackEnd::runOnRegion(Function& fn, BasicBlock& entry, BasicBlock* exit)
{
	SequenceStatement* sequence = structurizeRegion(*output, *grapher, entry, exit);
	grapher->updateRegion(entry, exit, *sequence);
}

AstBackEnd::RegionType AstBackEnd::isRegion(BasicBlock &entry, BasicBlock *exit)
{
	// LLVM's algorithm for finding regions (as of this early LLVM 3.7 fork) seems over-eager. For instance, with the
	// following graph:
	//
	//   0
	//   |\
	//   | 1
	//   | |
	//   | 2=<|    (where =<| denotes an edge to itself)
	//   |/
	//   3
	//
	// LLVM thinks that BBs 2 and 3 form a region. After asking for help on the mailing list, it appears that LLVM
	// tags it as an "extended region"; that is, a set of nodes that would be a region if we only added one basic block.
	// This is not helpful for our purposes.
	//
	// Sine the classical definition of regions apply to edges and edges are second-class citizens in the LLVM graph
	// world, we're going to roll with this inefficient-but-working, home-baked definition instead:
	//
	// A region is an ordered pair (A, B) of nodes, where A dominates, and B postdominates, every node
	// traversed in any given iteration order from A to B. Additionally, no path starts after B such that a node of the
	// region can be reached again without traversing A.
	// This definition means that B is *excluded* from the region, because B could have predecessors that are not
	// dominated by A. And I'm okay with it, I like [) ranges. To compensate, nullptr represents the end of a function.
	
	bool cyclic = false;
	unordered_set<BasicBlock*> toVisit { &entry };
	unordered_set<BasicBlock*> visited { exit };
	SmallVector<BasicBlock*, 2> nodeSuccessors;
	// Step one: check domination
	while (toVisit.size() > 0)
	{
		auto iter = toVisit.begin();
		BasicBlock* bb = *iter;
		
		// We use `exit = nullptr` to denote that the exit is the end of the function, which post-dominates
		// every basic block. This is a deviation from the normal LLVM dominator tree behavior, where
		// nullptr is considered unreachable (and thus does not dominate or post-dominate anything).
		if (!domTree->dominates(&entry, bb) || (exit != nullptr && !postDomTree->dominates(exit, bb)))
		{
			return NotARegion;
		}
		
		toVisit.erase(iter);
		visited.insert(bb);
		
		// Only visit region successors. This saves times, and saves us from spuriously declaring that regions are
		// cyclic by skipping cycles that have already been identified.
		nodeSuccessors.clear();
		AstGraphNode* graphNode = grapher->getGraphNodeFromEntry(bb);
		if (graphNode->hasExit())
		{
			nodeSuccessors.push_back(graphNode->getExit());
		}
		else
		{
			nodeSuccessors.insert(nodeSuccessors.end(), succ_begin(bb), succ_end(bb));
		}
		
		for (BasicBlock* succ : nodeSuccessors)
		{
			if (visited.count(succ) == 0)
			{
				toVisit.insert(succ);
			}
			else if (succ == &entry)
			{
				cyclic = true;
			}
		}
	}
	
	// Step two: check that no path starting after the exit goes back into the region without first going through the
	// entry.
	unordered_set<BasicBlock*> regionMembers;
	regionMembers.swap(visited);
	regionMembers.erase(exit);
	
	if (exit != nullptr)
	{
		toVisit.insert(succ_begin(exit), succ_end(exit));
	}
	
	visited.insert(&entry);
	while (toVisit.size() > 0)
	{
		auto iter = toVisit.begin();
		BasicBlock* bb = *iter;
		
		if (regionMembers.count(bb) != 0)
		{
			return NotARegion;
		}
		
		toVisit.erase(iter);
		visited.insert(bb);
		for (BasicBlock* succ : successors(bb))
		{
			if (visited.count(succ) == 0)
			{
				toVisit.insert(succ);
			}
		}
	}
	
	return cyclic ? Cyclic : Acyclic;
}

INITIALIZE_PASS_BEGIN(AstBackEnd, "astbe", "AST Back-End", true, false)
INITIALIZE_PASS_DEPENDENCY(DominatorTreeWrapperPass)
INITIALIZE_PASS_DEPENDENCY(PostDominatorTree)
INITIALIZE_PASS_END(AstBackEnd, "astbe", "AST Back-End", true, false)

AstBackEnd* createAstBackEnd()
{
	return new AstBackEnd;
}
