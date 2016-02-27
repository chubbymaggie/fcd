//
// bindings.h
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

#ifndef fcd__python_bindings_h
#define fcd__python_bindings_h

#include <memory>
#include <Python/Python.h>

template<typename WrappedType>
struct Py_LLVM_Wrapped
{
	PyObject_HEAD
	WrappedType obj;
};

PyMODINIT_FUNC initLlvmModule(PyObject** module);

extern PyTypeObject Py_LLVMUse_Type;
extern PyTypeObject Py_LLVMModuleProvider_Type;
extern PyTypeObject Py_LLVMBuilder_Type;
extern PyTypeObject Py_LLVMValue_Type;
extern PyTypeObject Py_LLVMPassRegistry_Type;
extern PyTypeObject Py_LLVMPassManager_Type;
extern PyTypeObject Py_LLVMModule_Type;
extern PyTypeObject Py_LLVMContext_Type;
extern PyTypeObject Py_LLVMDiagnosticInfo_Type;
extern PyTypeObject Py_LLVMBasicBlock_Type;
extern PyTypeObject Py_LLVMType_Type;

struct PyDecRef
{
	void operator()(PyObject* obj) const
	{
		Py_XDECREF(obj);
	}
};

typedef std::unique_ptr<PyObject, PyDecRef> AutoPyObject;

// use TAKEREF when you receive a new reference
struct TakeRefWrapWithAutoPyObject
{
	// operator|| is the last operator to have more precedence than operator=
	AutoPyObject operator||(PyObject* that) const
	{
		return AutoPyObject(that);
	}
};

// use ADDREF when you receive a borrowed reference
struct AddRefWrapWithAutoPyObject
{
	AutoPyObject operator||(PyObject* that) const
	{
		if (that != nullptr)
		{
			Py_INCREF(that);
		}
		return AutoPyObject(that);
	}
};

#define TAKEREF TakeRefWrapWithAutoPyObject() ||
#define ADDREF AddRefWrapWithAutoPyObject() ||

#endif /* fcd__python_bindings_h */
