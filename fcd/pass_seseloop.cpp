//
// pass_loopcollapseentries.cpp
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

#include "llvm_warnings.h"
#include "passes.h"

SILENCE_LLVM_WARNINGS_BEGIN()
#include <llvm/ADT/PostOrderIterator.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Support/raw_os_ostream.h>
#include <llvm/Transforms/Utils/SSAUpdater.h>
SILENCE_LLVM_WARNINGS_END()

#include <deque>
#include <unordered_map>
#include <unordered_set>

using namespace llvm;
using namespace std;

namespace
{
	template<typename TGraphType, typename GraphTr = GraphTraits<TGraphType>>
	void findPathsToSinkNodes(TGraphType currentNode, const unordered_set<TGraphType>& sinkNodes, vector<vector<TGraphType>>& results, deque<TGraphType>& stack)
	{
		stack.push_back(currentNode);
		
		if (sinkNodes.count(currentNode) == 1)
		{
			results.emplace_back(stack.begin(), stack.end());
		}
		
		auto end = GraphTr::child_end(currentNode);
		for (auto iter = GraphTr::child_begin(currentNode); iter != end; ++iter)
		{
			TGraphType explored = *iter;
			bool found = any_of(stack.rbegin(), stack.rend(), [&](const TGraphType& item)
			{
				return explored == item;
			});
			
			if (!found)
			{
				findPathsToSinkNodes(explored, sinkNodes, results, stack);
			}
		}
		stack.pop_back();
	}
	
	template<typename TGraphType, typename GraphTr = GraphTraits<TGraphType>>
	vector<vector<TGraphType>> findPathsToSinkNodes(TGraphType startNode, const unordered_set<TGraphType>& sinkNodes)
	{
		vector<vector<TGraphType>> result;
		deque<TGraphType> stack;
		findPathsToSinkNodes(startNode, sinkNodes, result, stack);
		return result;
	}
	
	void findBackEdgeDestinations(BasicBlock* entry, deque<BasicBlock*>& stack, unordered_multimap<BasicBlock*, BasicBlock*>& result, unordered_set<BasicBlock*>& visited)
	{
		visited.insert(entry);
		stack.push_back(entry);
		for (BasicBlock* bb : successors(entry))
		{
			if (visited.count(bb) == 0)
			{
				findBackEdgeDestinations(bb, stack, result, visited);
			}
			else if (find(stack.rbegin(), stack.rend(), bb) != stack.rend())
			{
				result.insert({bb, entry});
			}
		}
		stack.pop_back();
	}
	
	unordered_multimap<BasicBlock*, BasicBlock*> findBackEdgeDestinations(BasicBlock& entryPoint)
	{
		unordered_set<BasicBlock*> visited;
		unordered_multimap<BasicBlock*, BasicBlock*> result;
		deque<BasicBlock*> visitedStack;
		findBackEdgeDestinations(&entryPoint, visitedStack, result, visited);
		return result;
	}
	
	struct SESELoop : public FunctionPass
	{
		static char ID;
		
		// Persistent per-function map of back-edge-destination to loop member.
		// Loops are visited in post-order and the algorithm that finds paths to sink nodes
		// doesn't run through sub-cycles. This helps identify sub-cycles and insert them as loop
		// members for larger cycles.
		unordered_multimap<BasicBlock*, BasicBlock*> loopMembers;
		
		SESELoop() : FunctionPass(ID)
		{
		}
		
		virtual void getAnalysisUsage(AnalysisUsage& au) const override
		{
			au.addRequired<DominatorTreeWrapperPass>();
		}
		
		virtual bool runOnFunction(Function& fn) override
		{
			if (fn.isDeclaration())
			{
				return false;
			}
			
			loopMembers.clear();
			bool changed = false;
			
			unordered_multimap<BasicBlock*, BasicBlock*> destToOrigin = findBackEdgeDestinations(fn.getEntryBlock());
			
			vector<BasicBlock*> postOrderBackwardsEdges;
			for (BasicBlock* bb : post_order(&fn.getEntryBlock()))
			{
				if (destToOrigin.count(bb) != 0)
				{
					postOrderBackwardsEdges.push_back(bb);
				}
			}
			
			for (BasicBlock* bb : postOrderBackwardsEdges)
			{
				changed |= runOnBackgoingBlock(*bb, destToOrigin);
			}
			
			return changed;
		}
		
		void buildLoopMemberSet(BasicBlock& backEdgeDestination, const unordered_multimap<BasicBlock*, BasicBlock*>& destToOrigin, unordered_set<BasicBlock*>& members, unordered_set<BasicBlock*>& entries, unordered_set<BasicBlock*>& exits)
		{
			// Build paths to back-edge start nodes.
			unordered_set<BasicBlock*> sinkNodeSet;
			auto range = destToOrigin.equal_range(&backEdgeDestination);
			for (auto iter = range.first; iter != range.second; iter++)
			{
				sinkNodeSet.insert(iter->second);
			}
			
			auto pathsToBackNodes = findPathsToSinkNodes(&backEdgeDestination, sinkNodeSet);
			
			// Build initial loop membership set
			for (const auto& path : pathsToBackNodes)
			{
				members.insert(path.begin(), path.end());
			}
			
			// The path-to-sink-nodes algorithm won't follow back edges. Because of that, if the cycle contains a
			// sub-cycle, we need to add its member nodes. This is probably handled by the loop membership refinement
			// step from the "No More Gotos" paper, but as noted below, we don't use that step.
			unordered_set<BasicBlock*> newMembers;
			for (BasicBlock* bb : members)
			{
				auto range = loopMembers.equal_range(bb);
				for (auto iter = range.first; iter != range.second; iter++)
				{
					newMembers.insert(iter->second);
				}
			}
			members.insert(newMembers.begin(), newMembers.end());
			
			for (BasicBlock* member : members)
			{
				loopMembers.insert({&backEdgeDestination, member});
				
				for (BasicBlock* pred : predecessors(member))
				{
					if (members.count(pred) == 0)
					{
						entries.insert(member);
					}
				}
				
				for (BasicBlock* succ : successors(member))
				{
					if (members.count(succ) == 0)
					{
						exits.insert(succ);
					}
				}
			}
		}
		
		bool runOnBackgoingBlock(BasicBlock& backEdgeDestination, const unordered_multimap<BasicBlock*, BasicBlock*>& backEdgeMap)
		{
			unordered_set<BasicBlock*> members;
			unordered_set<BasicBlock*> entries; // nodes inside the loop that are reached from the outside
			unordered_set<BasicBlock*> exits; // nodes outside the loop that are preceded by a node inside of it
			buildLoopMemberSet(backEdgeDestination, backEdgeMap, members, entries, exits);

			// The "No More Gotos" paper suggests a step of "loop membership refinement", but it seems dubiously useful
			// to me. I could have done it wrong, but from my experience, it'll just gobble up non-looping nodes and
			// stick a break statement after them. Git commit 9b2f84f9bb5ab5348f7dc8548474442622de5114 has the last
			// revision of this file before I removed the loop membership refinement step.
			
			bool changed = false;
			if (entries.size() > 1)
			{
				// Entering nodes are nodes *outside* the loop that have one of `entries` as a successor...
				unordered_set<BasicBlock*> enteringNodes;
				for (BasicBlock* entry : entries)
				{
					for (BasicBlock* pred : predecessors(entry))
					{
						if (members.count(pred) == 0)
						{
							enteringNodes.insert(pred);
						}
					}
				}
				
				// ... and every predecessor of the back-edge destination node, in or out of the loop.
				for (BasicBlock* pred : predecessors(&backEdgeDestination))
				{
					enteringNodes.insert(pred);
				}
				
				BasicBlock* funnel = createFunnelBlock(members, enteringNodes, false);
				assert(verifyFunction(*backEdgeDestination.getParent(), &errs()) == 0);
				changed = true;
				members.insert(funnel);
			}
			
			if (exits.size() > 1)
			{
				// Fix abnormal exits.
				// Find in-loop predecessors.
				unordered_set<BasicBlock*> exitPreds;
				for (BasicBlock* exit : exits)
				{
					for (BasicBlock* pred : predecessors(exit))
					{
						if (members.count(pred) != 0)
						{
							exitPreds.insert(pred);
						}
					}
				}
				
				createFunnelBlock(members, exitPreds, true);
				assert(verifyFunction(*backEdgeDestination.getParent(), &errs()) == 0);
				changed = true;
			}
			
			return changed;
		}
		
		BasicBlock* createFunnelBlock(const unordered_set<BasicBlock*>& members, const unordered_set<BasicBlock*>& frontierBlocks, bool fixIfMember)
		{
			BasicBlock* anyBB = *frontierBlocks.begin();
			Function* fn = anyBB->getParent();
			LLVMContext& ctx = anyBB->getContext();
			
			// Introduce funnel basic block and PHI node. The PHI node's purpose is to direct execution to one of
			// enteringBlock.
			Type* i32 = Type::getInt32Ty(ctx);
			BasicBlock* funnel = BasicBlock::Create(ctx, "sese.funnel", fn);
			PHINode* predSwitchNode = PHINode::Create(i32, static_cast<unsigned>(frontierBlocks.size()), "", funnel);
			
			// Create a cascade of blocks branching to enteringBlocks.
			BasicBlock* previousBranch = nullptr;
			BasicBlock* branchFrom = funnel;
			unsigned i = 0;
			for (BasicBlock* thisBlock : frontierBlocks)
			{
				previousBranch = branchFrom;
				branchFrom = BasicBlock::Create(ctx, "sese.funnel.cascade", fn);
				auto constantI = ConstantInt::get(i32, i);
				auto cmp = ICmpInst::Create(ICmpInst::ICmp, ICmpInst::ICMP_EQ, predSwitchNode, constantI, "", previousBranch);
				BranchInst::Create(thisBlock, branchFrom, cmp, previousBranch);
				
				SmallPtrSet<BasicBlock*, 4> updatedPredecessors;
				for (Use& blockUse : thisBlock->uses())
				{
					if (auto branch = dyn_cast<BranchInst>(blockUse.getUser()))
					{
						BasicBlock* pred = branch->getParent();
						bool isMember = members.count(pred) != 0;
						if (isMember == fixIfMember)
						{
							blockUse.set(funnel);
							predSwitchNode->addIncoming(constantI, pred);
							updatedPredecessors.insert(pred);
						}
					}
				}
				
				if (updatedPredecessors.size() > 0)
				{
					// If we changed this block's predecessors (we normally have), we need to make sure that it dominates
					// the values that it needs to work with.
					fixNonDominatingValues(members, fixIfMember, thisBlock);
				
					// PHI nodes at the beginning of thisBlock need to be split and "raised" to funnel.
					for (auto iter = thisBlock->begin(); auto phi = dyn_cast<PHINode>(iter); ++iter)
					{
						auto raised = PHINode::Create(phi->getType(), phi->getNumIncomingValues(), "raised." + phi->getName(), predSwitchNode);
						phi->addIncoming(raised, previousBranch);
						unsigned i = 0;
						while (i < phi->getNumIncomingValues())
						{
							BasicBlock* from = phi->getIncomingBlock(i);
							if (updatedPredecessors.count(from) != 0)
							{
								raised->addIncoming(phi->getIncomingValue(i), from);
								phi->removeIncomingValue(i);
							}
							else
							{
								++i;
							}
						}
					}
				}
				
				++i;
			}
			
			BasicBlock* finalBlock = *succ_begin(branchFrom);
			previousBranch->replaceAllUsesWith(finalBlock);
			previousBranch->eraseFromParent();
			branchFrom->eraseFromParent();
			
			return funnel;
		}
		
		void fixNonDominatingValues(const unordered_set<BasicBlock*>& members, bool fixIfMember, BasicBlock* at)
		{
			BasicBlock* entryBlock = &at->getParent()->getEntryBlock();
			DominatorTree& oldDomTree = getAnalysis<DominatorTreeWrapperPass>().getDomTree();
			SSAUpdater updater;
			
			// This dominator tree was not updated since blocks have been rearranged.
			// Walk it up and see which values need updating.
			auto baseTreeNode = oldDomTree.getNode(at);
			for (auto treeNode = baseTreeNode->getIDom(); treeNode != nullptr; treeNode = treeNode->getIDom())
			{
				BasicBlock* dominating = treeNode->getBlock();
				bool isMember = members.count(dominating) != 0;
				if (isMember == fixIfMember)
				{
					// This part is basically the same as StructurizeCFG's rebuildSSA.
					for (auto iter = dominating->begin(); iter != dominating->end(); ++iter)
					{
						bool initialized = false;
						auto useIter = iter->use_begin();
						while (useIter != iter->use_end())
						{
							Use& use = *useIter;
							useIter++;
							
							Instruction* user = cast<Instruction>(use.getUser());
							BasicBlock* userBlock = user->getParent();
							
							if (userBlock == dominating)
							{
								continue;
							}
							else if (auto phi = dyn_cast<PHINode>(user))
							{
								if (phi->getIncomingBlock(use) == dominating)
								{
									continue;
								}
							}
							else if (!oldDomTree.dominates(at, userBlock))
							{
								continue;
							}
							
							if (!initialized)
							{
								Type* type = use->getType();
								updater.Initialize(type, "");
								updater.AddAvailableValue(entryBlock, UndefValue::get(type));
								updater.AddAvailableValue(dominating, iter);
								initialized = true;
							}
							updater.RewriteUseAfterInsertions(use);
						}
					}
				}
			}
		}
	};
	
	char SESELoop::ID = 0;
}

FunctionPass* createSESELoopPass()
{
	return new SESELoop;
}

INITIALIZE_PASS(SESELoop, "seseloop", "Turn loops with multiple entries into loops with a single entry", true, false)
