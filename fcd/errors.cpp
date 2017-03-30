//
// errors.cpp
// Copyright (C) 2015 Félix Cloutier.
// All Rights Reserved.
//
// This file is distributed under the University of Illinois Open Source
// license. See LICENSE.md for details.
//

#include "errors.h"

using namespace std;

namespace
{
	template<typename T, size_t N>
	constexpr size_t countof(T (&)[N])
	{
		return N;
	}
	
#define ERROR_MESSAGE(code, message) [static_cast<size_t>(FcdError::code)] = message
	string errorMessages[] = {
		ERROR_MESSAGE(NoError, "no error"),
		
		ERROR_MESSAGE(Main_EntryPointOutOfMappedMemory, "additional entry address points outside of executable"),
		ERROR_MESSAGE(Main_NoEntryPoint, "no entry point (see --help)"),
		ERROR_MESSAGE(Main_DecompilationError, "decompiler error"),
		ERROR_MESSAGE(Main_HeaderParsingError, "header file parsing error"),
		
		ERROR_MESSAGE(Python_LoadError, "couldn't load Python script"),
		ERROR_MESSAGE(Python_InvalidPassFunction, "run function should accept a single argument"),
		ERROR_MESSAGE(Python_PassTypeConfusion, "Python pass must declare exactly one of runOnFunction or runOnModule"),
		ERROR_MESSAGE(Python_ExecutableScriptInitializationError, "Python script failed to initialize correctly"),
	};
	
	static_assert(countof(errorMessages) == static_cast<size_t>(FcdError::MaxError), "missing error strings");
	
	fcd_error_category instance;
}

std::error_code make_error_code(FcdError error)
{
	return error_code((int)error, fcd_error_category::instance());
}

fcd_error_category& fcd_error_category::instance()
{
	return ::instance;
}

const char* fcd_error_category::name() const noexcept
{
	return "fcd error";
}

string fcd_error_category::message(int condition) const
{
	if (condition >= static_cast<int>(FcdError::MaxError))
	{
		return "unknown error";
	}
	
	return errorMessages[condition];
}
