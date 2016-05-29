//===-- CGException.h - ----------*- C++ -*-===//

#ifndef LLVM_CLANG_LIB_CODEGEN_CGEXCEPTION_H
#define LLVM_CLANG_LIB_CODEGEN_CGEXCEPTION_H

#include "clang/AST/CharUnits.h"
#include "clang/AST/Type.h"
#include "clang/Basic/SourceLocation.h"
#include "Address.h"

namespace llvm {
class Constant;
class Value;
}

namespace clang {
class Expr;

namespace CodeGen {
class CodeGenModule;
class CodeGenFunction;

// llvm::Constant *getBeginCatchFn(CodeGenModule &CGM);
// llvm::Constant *getEndCatchFn(CodeGenModule &CGM);

llvm::Value *CallBeginCatch(CodeGenFunction &CGF,
                                   llvm::Value *Exn,
                                   bool EndMightThrow);

void InitCatchParam(CodeGenFunction &CGF,
                           llvm::Value *Exn,
                           QualType CatchParamTy,
                           const Expr *CatchParamInit,
                           Address ParamAddr,
                           SourceLocation Loc);

}  // end namespace CodeGen
}  // end namespace clang

#endif