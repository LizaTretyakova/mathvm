ROOT   = .
VM_ROOT = ../../..

OPT = 1
NO_JIT = 0
WITH_SDL = 1

USER_CFLAGS = -std=c++11

ifneq ($(NO_JIT), 1)
JIT_OBJ = $(OBJ)/jit$(OBJ_SUFF)
else
JIT_OBJ =
endif

USER_OBJ = \
   $(JIT_OBJ) \
   $(OBJ)/ast_printer$(OBJ_SUFF) \
   $(OBJ)/bytecode_impl$(OBJ_SUFF) \
   $(OBJ)/main$(OBJ_SUFF) \
   $(OBJ)/translator_impl$(OBJ_SUFF) \
   $(OBJ)/translator_visitor$(OBJ_SUFF) \

include $(VM_ROOT)/common.mk

MATHVM = $(BIN)/mvm

all: $(MATHVM)

$(MATHVM): $(OUT) $(USER_OBJ) $(MATHVM_OBJ)
	$(CXX) -o $@ $(USER_OBJ) $(MATHVM_OBJ) $(LIBS)
