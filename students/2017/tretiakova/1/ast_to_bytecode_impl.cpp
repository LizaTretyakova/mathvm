#include "../include/ast.h"
#include "../include/mathvm.h"
#include "../include/visitors.h"

#include "include/ast_to_bytecode_impl.h"

#include "bytecode_code.h"

#include <vector>
#include <stack>
#include <map>
#include <string>
#include <dlfcn.h>

namespace mathvm {

using namespace std;

void BytecodeTranslateVisitor::invalidate(string msg, uint32_t pos) {
//        type_stack.pop();
    cerr << "[Translator] invalidate INVALID";
    type_stack.push(VT_INVALID);
    status = Status::Error(msg.c_str(), pos);
}

VarType BytecodeTranslateVisitor::update_type_stack_un() { // check
    if(type_stack.size() < 1) {
        cerr << "[Translator] type stack too small (<1) INVALID";
        type_stack.push(VT_INVALID);
        return VT_INVALID;
    }
    return type_stack.top();
}

VarType BytecodeTranslateVisitor::update_type_stack() {
    if(type_stack.size() < 2) {
        cerr << "[Translator] type stack too small (<2) INVALID";
        type_stack.push(VT_INVALID);
        return VT_INVALID;
    }

    VarType t_right = type_stack.top();
    type_stack.pop();
    VarType t_left = type_stack.top();
    type_stack.pop();
    VarType result;

    switch(t_left) {
    case VT_DOUBLE:
    case VT_INT:
    case VT_STRING:
        result =
            t_right == t_left ? t_left : VT_INVALID;
        break;
    default:
        result = VT_INVALID;
        break;
    }

    cerr << "[Translator] update type stack, new "
         << typeToName(result) << endl;
    type_stack.push(result);
    return result;
}

void BytecodeTranslateVisitor::push_numeric(VarType type, Instruction i_bc, Instruction d_bc, uint32_t pos) {
    switch(type) {
    case VT_INT:
        translated_function->bytecode()->addInsn(i_bc);
        break;
    case VT_DOUBLE:
        translated_function->bytecode()->addInsn(d_bc);
        break;
    default:
        cerr << "Invalid operand type in numeric op" << endl;
        invalidate("Invalid operand type in numeric op", pos);
        break;
    }
}

void BytecodeTranslateVisitor::push_comparison(VarType type, Instruction i_bc, Instruction d_bc, Instruction s_bc, uint32_t pos) {
    switch(type) {
    case VT_INT:
        translated_function->bytecode()->addInsn(i_bc);
        break;
    case VT_DOUBLE:
        translated_function->bytecode()->addInsn(d_bc);
        break;
    case VT_STRING:
        translated_function->bytecode()->addInsn(s_bc);
        break;
    default:
        cerr << "Invalid type in comparison" << endl;
        invalidate("Invalid type in comparison", pos);
        break;
    }
}

void BytecodeTranslateVisitor::push_condition(VarType type, Instruction comp_insn, uint32_t pos) {
    push_comparison(type, BC_ICMP, BC_DCMP, BC_ICMP, pos);
    translated_function->bytecode()->addInsn(BC_ILOAD0);
    push_comparison(VT_INT, comp_insn, comp_insn, comp_insn, pos);
    translated_function->bytecode()->addInt16(2 + 2);
    translated_function->bytecode()->addInsn(BC_ILOAD0);
    translated_function->bytecode()->addInsn(BC_JA);
    translated_function->bytecode()->addInt16(1);
    translated_function->bytecode()->addInsn(BC_ILOAD1);
}

void BytecodeTranslateVisitor::push_logic(VarType type, Instruction bc, uint32_t pos) {
    if(type != VT_INT) {
        cerr << "Non-int type in logic" << endl;
        invalidate("Non-int type in logic", pos);
        return;
    }
    translated_function->bytecode()->addInsn(bc);
}

void BytecodeTranslateVisitor::push_store(VarType type, uint16_t scope_id, uint16_t var_id, uint32_t pos) {
//    VarType last_type = update_type_stack_un();
//    if(last_type != type) {
//        cerr << "Type mismatch in STORE, expected " << typeToName(last_type)
//             << ", got " << typeToName(type) << endl;
//        invalidate("Type mismatch in STORE", pos);
//        return;
//    }

//    // because STORE will take one value from stack
//    type_stack.pop();

    switch(type) {
    case VT_INT:
        translated_function->bytecode()->addInsn(BC_STORECTXIVAR);
        break;
    case VT_DOUBLE:
        translated_function->bytecode()->addInsn(BC_STORECTXDVAR);
        break;
    case VT_STRING:
        translated_function->bytecode()->addInsn(BC_STORECTXSVAR);
        break;
    default:
        cerr << "Unexpected type " << typeToName(type) << " in STORE" << endl;
        invalidate("Unexpected type", pos);
        break;
    }

    translated_function->bytecode()->addUInt16(scope_id);
    translated_function->bytecode()->addUInt16(var_id);

    return;
}

// returns the position of the jmp's argument, 0 on error
uint32_t BytecodeTranslateVisitor::push_cond_jump(uint32_t pos) {
    if(type_stack.size() < 2) {
        cerr << "Too few entries on stack (<2)" << endl;
        invalidate("Too few entries on stack (<2)", pos);
        return 0;
    }

    VarType type_zero = type_stack.top();
    type_stack.pop();
    VarType type_expr = type_stack.top();
    type_stack.pop();
    if(type_zero == VT_INT && type_expr == VT_INT) {
        // if `cond == 0`, i.e. false -- jump to "after block"
        translated_function->bytecode()->addInsn(BC_IFICMPE);
        uint32_t index = translated_function->bytecode()->current();
        translated_function->bytecode()->addInt16(0); // temporarily
        return index;
    }

    cerr << "Non-int operands (" << typeToName(type_zero)
         << ", " << typeToName(type_expr) << ") in CMP JUMP" << endl;
    invalidate("Non-int operands in CMP JUMP", pos);
    return 0;
}

void BytecodeTranslateVisitor::push_load_i(uint16_t scope_id, uint16_t var_id) {
    translated_function->bytecode()->addInsn(BC_LOADCTXIVAR);
    translated_function->bytecode()->addUInt16(scope_id);
    translated_function->bytecode()->addUInt16(var_id);
    type_stack.push(VT_INT);
}

void BytecodeTranslateVisitor::push_ja(uint32_t to) {
    translated_function->bytecode()->addInsn(BC_JA);
    uint32_t from = translated_function->bytecode()->current();
    uint32_t offset = to - from;
    translated_function->bytecode()->addInt16((int16_t)offset);
}

void BytecodeTranslateVisitor::update_jmp(uint32_t from) {
    uint32_t to = translated_function->bytecode()->current();
    uint32_t offset = to - from;
    translated_function->bytecode()->setInt16(from, (int16_t)offset);
}

uint16_t BytecodeTranslateVisitor::add_scope(Scope* scope) {
    return translated_code->add_scope(scope);
}

uint16_t BytecodeTranslateVisitor::add_var(Scope* scope, VarType type, string name) {
    return translated_code->add_var(scope, type, name);
}

//BytecodeTranslateVisitor() = default;

//BytecodeTranslateVisitor(BytecodeFunction* bf, BytecodeCode* bc):
//    BytecodeTranslateVisitor() {
//    translated_function = bf;
//    translated_code = bc;
//}

//BytecodeTranslateVisitor(const BytecodeTranslateVisitor& b) = default;

//BytecodeTranslateVisitor(const BytecodeTranslateVisitor &b, BytecodeFunction* bf, VarType t):
//    BytecodeTranslateVisitor(b) {
//    translated_function = bf;
//    return_type = t;
//}

BytecodeCode* BytecodeTranslateVisitor::program() {
    translated_code->set_translated_function(translated_function);
    return translated_code;
}

Status* BytecodeTranslateVisitor::get_status() {
    return status;
}

void BytecodeTranslateVisitor::visitBinaryOpNode(BinaryOpNode* node) {
    cerr << "[BinaryOp]" << endl;

    // Order!
    node->right()->visit(this);
    node->left()->visit(this);

    VarType type = update_type_stack();
    if(type == VT_INVALID || type == VT_VOID) {
        cerr << "Invalid type before BinaryOp, type "
             << typeToName(type)
             << ", position " << node->position() << endl;
        invalidate("Invalid type before BinaryOp", node->position());
        return;
    }

    switch(node->kind()) {
    case tOR:
    case tAOR:
        push_logic(type, BC_IAOR, node->position());
        break;
    case tAND:
    case tAAND:
        push_logic(type, BC_IAAND, node->position());
        break;
    case tAXOR:
        push_logic(type, BC_IAXOR, node->position());
        break;
    case tNEQ:
        push_condition(type, BC_IFICMPNE, node->position());
        break;
    case tEQ:
        // the logic might change but for now it seems that
        // this is the right version
        push_condition(type, BC_IFICMPE, node->position());
        break;
    case tGT:
        push_condition(type, BC_IFICMPG, node->position());
        break;
    case tGE:
        push_condition(type, BC_IFICMPGE, node->position());
        break;
    case tLT:
        push_condition(type, BC_IFICMPL, node->position());
        break;
    case tLE:
        push_condition(type, BC_IFICMPLE, node->position());
        break;
    case tADD:
        push_numeric(type, BC_IADD, BC_DADD, node->position());
        break;
    case tSUB:
        push_numeric(type, BC_ISUB, BC_DSUB, node->position());
        break;
    case tMUL:
        push_numeric(type, BC_IMUL, BC_DMUL, node->position());
        break;
    case tDIV:
        push_numeric(type, BC_IDIV, BC_DDIV, node->position());
        break;
    case tMOD:
        if(type == VT_INT) {
            translated_function->bytecode()->addInsn(BC_IMOD);
            break;
        }
    default:
        cerr << "Unknown token op " << string(tokenOp(node->kind()))
             << " at position " << node->position() << endl;
        invalidate("Unknown token op", node->position());
        break;
    }
}

void BytecodeTranslateVisitor::visitUnaryOpNode(UnaryOpNode* node) {
    cerr << "[UnaryOp]" << endl;

    node->operand()->visit(this);

    VarType type = update_type_stack_un();
    if(type == VT_INVALID || type == VT_VOID || type == VT_STRING) {
        cerr << "Invalid operand type, position " << node->position() << endl;
        invalidate("Invalid operand type", node->position());
        return;
    }

    switch(node->kind()) {
    case tNOT:
        if(type != VT_INT) {
            cerr << "Non-int operand in tNOT, type "
                 << typeToName(type)
                 << ", position " << node->position() << endl;
            invalidate("Non-int operand in tNOT", node->position());
            break;
        }
        translated_function->bytecode()->addUInt16(0);
        translated_function->bytecode()->addInsn(BC_ICMP);
        break;
    case tSUB:
        push_numeric(type, BC_INEG, BC_DNEG, node->position());
        break;
    default:
        cerr << "Unknown unary op " << tokenOp(node->kind())
             << ", position " << node->position() << endl;
        invalidate("Unknown unary op", node->position());
        break;
    }
}

void BytecodeTranslateVisitor::visitStringLiteralNode(StringLiteralNode* node) {
    cerr << "[StringLiteral]" << endl;

    uint16_t const_id = translated_code->makeStringConstant(node->literal());
    translated_function->bytecode()->addInsn(BC_SLOAD);
    translated_function->bytecode()->addUInt16(const_id);
}

void BytecodeTranslateVisitor::visitDoubleLiteralNode(DoubleLiteralNode* node) {
    cerr << "[DoubleLiteral]" << endl;

    translated_function->bytecode()->addInsn(BC_DLOAD);
    translated_function->bytecode()->addDouble(node->literal());
}

void BytecodeTranslateVisitor::visitIntLiteralNode(IntLiteralNode* node) {
    cerr << "[IntLiteral]" << endl;

    translated_function->bytecode()->addInsn(BC_ILOAD);
    translated_function->bytecode()->addInt64(node->literal());
}

void BytecodeTranslateVisitor::visitLoadNode(LoadNode* node) {
    cerr << "[Load]" << endl;

    const AstVar* var = node->var();
    Scope* scope = var->owner();
    uint16_t scope_id = add_scope(scope);
    uint16_t var_id = add_var(scope, var->type(), var->name());

    VarType type = var->type();
    switch(type) {
    case VT_INT:
        translated_function->bytecode()->addInsn(BC_LOADCTXIVAR);
        break;
    case VT_DOUBLE:
        translated_function->bytecode()->addInsn(BC_LOADCTXDVAR);
        break;
    case VT_STRING:
        translated_function->bytecode()->addInsn(BC_LOADCTXSVAR);
        break;
    default:
        cerr << "Invalid LOAD type " << typeToName(type)
             << ", position " << node->position() << endl;
        invalidate("Invalid LOAD type", node->position());
        break;
    }

    translated_function->bytecode()->addUInt16(scope_id);
    translated_function->bytecode()->addUInt16(var_id);
}

void BytecodeTranslateVisitor::visitStoreNode(StoreNode* node) {
    cerr << "[Store]" << endl;

    TokenKind op = node->op();
    const AstVar* var = node->var();
    Scope* scope = var->owner();
    VarType type = var->type();

    uint16_t scope_id = add_scope(scope);
    uint16_t var_id = add_var(scope, var->type(), var->name());

    if(op == tINCRSET || op == tDECRSET) {
        switch(type) {
        case VT_INT:
            translated_function->bytecode()->addInsn(BC_LOADCTXIVAR);
            type_stack.push(VT_INT);
            break;
        case VT_DOUBLE:
            translated_function->bytecode()->addInsn(BC_LOADCTXDVAR);
            type_stack.push(VT_DOUBLE);
            break;
        default:
            cerr << "Unknown STORE op " << tokenOp(op)
                 << ", position " << node->position() << endl;
            invalidate("Unknown STORE op", node->position());
            break;
        }

        translated_function->bytecode()->addUInt16(scope_id);
        translated_function->bytecode()->addUInt16(var_id);
    }

    node->value()->visit(this);

    if(op == tINCRSET) {
        push_numeric(type, BC_IADD, BC_DADD, node->position());
    } else if(op == tDECRSET) {
        push_numeric(type, BC_ISUB, BC_DSUB, node->position());
    }

    push_store(type, scope_id, var_id, node->position());
}

void BytecodeTranslateVisitor::visitForNode(ForNode* node) {
    cerr << "[For]" << endl;

    // get and check the condition
    BinaryOpNode* range = dynamic_cast<BinaryOpNode*>(node->inExpr());
    if(!range) {
        cerr << "non-BinaryOpNode range in for, position " << node->position() << std::endl;
        invalidate("non-BinaryOpNode range in for", node->position());
        return;
    }
    TokenKind op = range->kind();
    if(op != tRANGE) {
        cerr << "non-range op in for, position " << node->position() << std::endl;
        invalidate("non-range op in for", node->position());
        return;
    }

    // evaluate the condition start
    range->left()->visit(this);

    // load to var
    const AstVar* var = node->var();
    Scope* scope = var->owner();
    uint16_t scope_id = add_scope(scope);
    uint16_t var_id = add_var(scope, var->type(), var->name());

    VarType type = var->type();
    if(type != VT_INT) {
        cerr << "non-int iterator in for, position " << node->position() << endl;
        invalidate("non-int iterator in for", node->position());
        return;
    }
    push_store(type, scope_id, var_id, node->position());

    uint32_t to_cond_pos = translated_function->bytecode()->current();

    // make condtion
    push_load_i(scope_id, var_id);

    range->right()->visit(this);
    type = update_type_stack_un();
    if(type != VT_INT) {
        cerr << "non-int cond in for, position " << node->position() << endl;
        invalidate("non-int cond in for", node->position());
        return;
    }

    // set jump
    translated_function->bytecode()->addInsn(BC_IFICMPG);
    uint32_t cond_checked_pos= translated_function->bytecode()->current();
    translated_function->bytecode()->addInt16(0);

    // loop body
    node->body()->visit(this);

    // set incr
    push_load_i(scope_id, var_id);

    translated_function->bytecode()->addInsn(BC_ILOAD1);
    type_stack.push(VT_INT);

    translated_function->bytecode()->addInsn(BC_IADD);
    type = update_type_stack();
    assert(type == VT_INT);

    push_store(type, scope_id, var_id, node->position());

    // jump
    push_ja(to_cond_pos);
    update_jmp(cond_checked_pos);
}

void BytecodeTranslateVisitor::visitWhileNode(WhileNode* node) {
    cerr << "[While]" << endl;

    uint32_t to_cond_pos = translated_function->bytecode()->current();

    node->whileExpr()->visit(this);
    translated_function->bytecode()->addInsn(BC_ILOAD0);
    type_stack.push(VT_INT);

    uint32_t cond_checked_pos = push_cond_jump(node->position());

    node->loopBlock()->visit(this);
    push_ja(to_cond_pos);

    update_jmp(cond_checked_pos);
}

void BytecodeTranslateVisitor::visitIfNode(IfNode* node) {
    cerr << "[If]" << endl;

    // If...
    node->ifExpr()->visit(this);
    translated_function->bytecode()->addInsn(BC_ILOAD0);
    type_stack.push(VT_INT);
    uint32_t first_jmp_pos = push_cond_jump(node->position());

    // ... then ...
    node->thenBlock()->visit(this);
    uint32_t after_then_pos = translated_function->bytecode()->current();

    uint32_t offset = after_then_pos - first_jmp_pos;
    translated_function->bytecode()->setInt16(first_jmp_pos, (int16_t)offset);

    // ... else
    if(node->elseBlock()) {
        translated_function->bytecode()->addInsn(BC_JA);
        uint32_t second_jmp_pos = translated_function->bytecode()->current();
        translated_function->bytecode()->addInt16(0);
        node->elseBlock()->visit(this);

        uint32_t after_else_pos = translated_function->bytecode()->current();
        uint32_t offset2 = after_else_pos - second_jmp_pos;

        translated_function->bytecode()->setInt16(second_jmp_pos, offset2);
    }
}

void BytecodeTranslateVisitor::visitBlockNode(BlockNode* node) {
    cerr << "[Block]" << endl;

//        for(Scope::VarIterator it(node->scope()); it.hasNext();) {
//            AstVar* var = it.next();
//            store_var(scope, var);
//        }

    for(Scope::FunctionIterator it(node->scope()); it.hasNext();) {
        AstFunction* fun = it.next();
        BytecodeFunction* bf = new BytecodeFunction(fun);
        BytecodeTranslateVisitor funVisitor(*this, bf, fun->node()->returnType());
        fun->node()->visit(&funVisitor);

        translated_code->addFunction(bf);
    }

    for (uint32_t i = 0; i < node->nodes(); i++) {
        node->nodeAt(i)->visit(this);
    }
}

void BytecodeTranslateVisitor::visitFunctionNode(FunctionNode* node) {
    cerr << "[Function]" << node->name() << endl;

    Scope* scope = node->body()->scope();
    uint16_t scope_id = add_scope(scope);

    for(uint32_t i = 0; i < node->parametersNumber(); i++) {
        VarType parameterType = node->parameterType(i);
        string parameterName = node->parameterName(i);

        uint16_t var_id = add_var(scope, parameterType, parameterName);

        push_store(parameterType, scope_id, var_id, node->position());
    }

    node->body()->visit(this);
}

void BytecodeTranslateVisitor::visitReturnNode(ReturnNode* node) {
    cerr << "[Return]" << endl;

    AstNode* return_expr = node->returnExpr();
    if(return_expr) {
        return_expr->visit(this);

        // check for the correct return type
        VarType return_expr_type = update_type_stack_un();
        if(return_expr_type != return_type) {
            cerr << "Invalid return type; expected "
                 << typeToName(return_type) << ", got"
                 << typeToName(return_expr_type)
                 << ", position " << node->position() << endl;
            invalidate("Invalid return type", node->position());
            return;
        }
    }
    translated_function->bytecode()->addInsn(BC_RETURN);
}

void BytecodeTranslateVisitor::visitCallNode(CallNode* node) {
    cerr << "[Call]" << endl;

    BytecodeFunction* fun =
            (BytecodeFunction*)translated_code->functionByName(node->name());

    if(node->parametersNumber() != fun->parametersNumber()) {
        cerr << "Parameters number mismatch at function " << node->name()
             << " at position " << node->position();
        invalidate("Parameters number mismatch at function", node->position());
        return;
    }

    VarType param_type, stack_type;
    for(uint32_t i = 0; i < node->parametersNumber(); i++) {
        node->parameterAt(i)->visit(this);

        param_type = fun->parameterType(i);
        stack_type = update_type_stack_un();
        if(param_type != stack_type) {
            cerr << "Parameter type mismatch, expected "
                 << typeToName(param_type) << ", got "
                 << typeToName(stack_type) << ", position"
                 << node->position() << endl;
            invalidate("Parameter type mismatch", node->position());
            return;
        }
    }

    translated_function->bytecode()->addInsn(BC_CALL);
    translated_function->bytecode()->addUInt16(fun->id());
}

void BytecodeTranslateVisitor::visitNativeCallNode(NativeCallNode* node) {
    cerr << "[NativeCall]" << endl;

    dl_fun_ptr function_handler;
    void* handle = dlopen(0,RTLD_NOW|RTLD_GLOBAL);
    *(void**)(&function_handler) = dlsym(handle, node->nativeName().c_str());

    if(!function_handler) {
        cerr << "Failed to load native function " << node->nativeName()
             << ", position " << node->position();
        invalidate("Failed to load native function", node->position());
        return;
    }

    uint16_t nat_id =
            translated_code->makeNativeFunction(
                node->nativeName(),
                node->nativeSignature(),
                (const void*)function_handler);

    translated_function->bytecode()->addInsn(BC_CALLNATIVE);
    translated_function->bytecode()->addUInt16(nat_id);
}

void BytecodeTranslateVisitor::visitPrintNode(PrintNode* node) {
    cerr << "[Print]" << endl;

    VarType operand_type;
    for(uint32_t i = 0; i < node->operands(); i++) {
        node->operandAt(i)->visit(this);

        operand_type = update_type_stack_un();
        switch (operand_type) {
        case VT_INT:
            translated_function->bytecode()->addInsn(BC_IPRINT);
            break;
        case VT_DOUBLE:
            translated_function->bytecode()->addInsn(BC_DPRINT);
            break;
        case VT_STRING:
            translated_function->bytecode()->addInsn(BC_SPRINT);
            break;
        default:
            cerr << "Invalid operand type for print: " << typeToName(operand_type)
                 << ", position " << node->position() << endl;
            invalidate("Invalid operand type for print", node->position());
            break;
        }
    }
}

}
