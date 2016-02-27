//
// llvm_warnings.h
// Copyright (C) 2015 Félix Cloutier.
// All Rights Reserved.
//
// This file is part of fcd. fcd as a whole is licensed under the terms
// of the GNU GPLv3 license, but specific parts (such as this one) are
// dual-licensed under the terms of a BSD-like license as well. You
// may use, modify and distribute this part of fcd under the terms of
// either license, at your choice.
//

// By default, Xcode tells Clang to complain about truncated integers. Rather than disabling that warning for the whole
// project, we guard #include <llvm/...> statements with these macros that disable them temporarily only.

// Xcode excludes header guard macros from autocompletion. For editing convenience, we don't use either
// SILENCE_LLVM_WARNINGS_* macro as a header guard.
#ifndef fcd__llvm_warnings_h
#define fcd__llvm_warnings_h

#ifdef __GNUC__

#define SILENCE_LLVM_WARNINGS_BEGIN() \
	_Pragma("clang diagnostic push") \
	_Pragma("clang diagnostic ignored \"-Wshorten-64-to-32\"")

#define SILENCE_LLVM_WARNINGS_END() \
	_Pragma("clang diagnostic pop")

#elif _MSC_VER

#define SILENCE_LLVM_WARNINGS_BEGIN() \
	__pragma(warning(push, 0))

#define SILENCE_LLVM_WARNINGS_END() \
	__pragma(warning(push))
#endif

#endif /* fcd__llvm_warnings_h */
