#ifndef _AST_TO_BYTECODE_IMPL_H
#define _AST_TO_BYTECODE_IMPL_H

#include "../include/ast.h"
#include "../include/mathvm.h"
#include "../include/visitors.h"

#include "bytecode_code.h"

#include <vector>
#include <stack>
#include <map>
#include <string>
#include <dlfcn.h>

namespace mathvm {

using namespace std;

typedef void* (*dl_fun_ptr)();

class BytecodeTranslateVisitor : public AstBaseVisitor {
//    BytecodeCode* translated_code = NULL;
//    BytecodeFunction* translated_function = NULL;
    // The default value. It's here due to invariant that
    // *** visitor visits one function at a time ***
//    VarType return_type = VT_VOID;

    BytecodeCode* bcode;
    vector<StackFrame*> fun_hierarchy; // No.
    stack<VarType> type_stack;
    Status* status = Status::Ok();

    void invalidate(string msg, uint32_t pos);
    VarType update_type_stack_un();
    VarType update_type_stack();
    void push_numeric(VarType type, Instruction i_bc, Instruction d_bc, uint32_t pos);
    void push_comparison(VarType type, Instruction i_bc, Instruction d_bc, Instruction s_bc, uint32_t pos);
    void push_condition(VarType type, Instruction comp_insn, uint32_t pos);
    void push_logic(VarType type, Instruction bcode, uint32_t pos);
    void push_store(VarType type, uint16_t scope_id, uint16_t var_id, uint32_t pos);
    // returns the position of the jmp's argument, 0 on error
    uint32_t push_cond_jump(uint32_t pos);
    void push_load_i(uint16_t scope_id, uint16_t var_id);
    void push_ja(uint32_t to);
    void update_jmp(uint32_t from);
    bool fix_type_mismatch(VarType expected_type, VarType got_type);

    void print_fun_hierarchy() {
        cerr << "[FunHierarchy]: ";
        for(int i = 0; i < (int)fun_hierarchy.size(); ++i) {
            cerr << fun_hierarchy[i]->name() << " ";
        }
        cerr << endl;
    }

public:

    BytecodeTranslateVisitor(BytecodeCode* b): bcode(b) {}

    Status* get_status();
    void setTopFunction(AstFunction* f) {
        StackFrame* sf = new StackFrame(f);
        fun_hierarchy.push_back(sf);
        print_fun_hierarchy();

    }
    void unsetTopFunction() {
        assert(fun_hierarchy.size() == 1);
        StackFrame* sf = fun_hierarchy.back();
        uint16_t fun_id = bcode->addFunction(sf);
        bcode->set_top_function_id(fun_id);
        fun_hierarchy.pop_back();
        print_fun_hierarchy();
    }

    virtual void visitBinaryOpNode(BinaryOpNode* node);
    virtual void visitUnaryOpNode(UnaryOpNode* node);
    virtual void visitStringLiteralNode(StringLiteralNode* node);
    virtual void visitDoubleLiteralNode(DoubleLiteralNode* node);
    virtual void visitIntLiteralNode(IntLiteralNode* node);
    virtual void visitLoadNode(LoadNode* node);
    virtual void visitStoreNode(StoreNode* node);
    virtual void visitForNode(ForNode* node);
    virtual void visitWhileNode(WhileNode* node);
    virtual void visitIfNode(IfNode* node);
    virtual void visitBlockNode(BlockNode* node);
    virtual void visitFunctionNode(FunctionNode* node);
    virtual void visitReturnNode(ReturnNode* node);
    virtual void visitCallNode(CallNode* node);
    virtual void visitNativeCallNode(NativeCallNode* node);
    virtual void visitPrintNode(PrintNode* node);
};

}

#endif // _AST_TO_BYTECODE_IMPL_H
