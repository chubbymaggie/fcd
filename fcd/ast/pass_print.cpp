//
// pass_print.cpp
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

#include "pass_print.h"
#include "clone.h"

using namespace llvm;
using namespace std;

void AstPrint::doRun(deque<std::unique_ptr<FunctionNode>> &functions)
{
	for (unique_ptr<FunctionNode>& fn : functions)
	{
		if (auto body = fn->getBody())
		{
			fn->setBody(CloneVisitor::clone(fn->getContext(), *body));
		}
		fn->print(output);
	}
}

const char* AstPrint::getName() const
{
	return "Print AST";
}
