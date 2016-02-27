//
// pass_propagatevalues.h
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

#ifndef fcd__ast_pass_propagatevalues_h
#define fcd__ast_pass_propagatevalues_h

#include "pass.h"

class AstPropagateValues final : public AstFunctionPass
{
protected:
	virtual void doRun(FunctionNode& fn) override;
	
public:
	virtual const char* getName() const override;
};

#endif /* fcd__ast_pass_propagatevalues_h */
