#pragma once
#include <vector>
#include <mathvm.h>
#include <string.h>
#include "Interpreter.h"
#include "JITCompiler.h"

#define VM_STACK_SIZE 32 * 1024 * 1024

class ExecutionEnv {
  Executable executable;

  mathvm::Status* interpretAll(std::vector<mathvm::Var*>& vars) {
    Interpreter interpreter(executable);
    interpreter.interpret();
    return new mathvm::Status();
  }

  mathvm::Status* machineExecAll(std::vector<mathvm::Var*>& vars) {
    JITCompiler cc(executable);
    cc.compileAll();
    stringPull = cc.getStringPull();
    void* *cFuncs = cc.getCompFuncPtrs();
    JITCompiler::VoidFunc main = AsmJit::function_cast<JITCompiler::VoidFunc>(cFuncs[0]);
    TranslatableFunction& mainMetaData = executable.getMetaData()[0];
    main(vmStack, vmStack + mainMetaData.getFrameSize()); //bp sp
    return new mathvm::Status();
  }
  char* vmStack;
  bool opt;
  std::vector<char*> stringPull;

public:
  ExecutionEnv(Executable& executable, bool opt) 
    : executable(executable) 
    , opt(opt)
  {
    vmStack = (char*)malloc(VM_STACK_SIZE);
  }

  virtual ~ExecutionEnv() {
    free(vmStack);
    for(size_t i = 0; i != stringPull.size(); ++i) {
      free(stringPull[i]);
    }
  }

  mathvm::Status* execute(std::vector<mathvm::Var*>& vars) {
    if (opt) {
      return machineExecAll(vars);
    } else {
      return interpretAll(vars);
    }
  }

  Executable& getExecutable() {
    return executable;
  }
};