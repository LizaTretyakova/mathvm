#ifndef _AST_TO_BYTECODE_IMPL_H
#define _AST_TO_BYTECODE_IMPL_H

#include "../include/ast.h"
#include "../include/mathvm.h"
#include "../include/visitors.h"

#include <vector>
#include <stack>
#include <map>
#include <string>

namespace mathvm {

using namespace std;

typedef union {
    double _doubleValue;
    int64_t _intValue;
    const char* _stringValue;
} Value;

class BytecodeTranslateVisitor : public AstBaseVisitor {
    typedef map<Scope*, uint16_t> ScopeMap;
    typedef map<string, uint16_t> VarNameMap;

    BytecodeFunction translated_function;
    Code translated_code;
    stack<VarType> type_stack;
    ScopeMap scope_map;
    map<Scope*, VarNameMap> var_map;
    vector<vector<AstVar*>> var_by_scope;

    VarType update_type_stack_un() { // check
        if(type_stack.size() < 1) {
            type_stack.push(VT_INVALID);
            return VT_INVALID;
        }
        return type_stack.top();
    }

    VarType update_type_stack() {
        if(type_stack.size() < 2) {
            // TODO: signal the error somehow =/
            type_stack.push(VT_INVALID);
            return;
        }

        VarType t_right = type_stack.pop();
        VarType t_left = type_stack.pop();
        VarType result;

        switch(t_left) {
//        case VT_STRING:
//            if(t_right == VT_STRING) {
//                result = VT_STRING;
//            } else {
//                result = VT_INVALID;
//            }
//            break;
//        case VT_DOUBLE:
//        case VT_INT:
//            if(t_right == VT_DOUBLE) {
//                result = VT_DOUBLE;
//            } else if(t_right == VT_INT) {
//                result = t_left;
//            } else {
//                result = VT_INVALID;
//            }
//            break;
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

        type_stack.push(result);
        return result;
    }

    void invalidate() {
        type_stack.pop();
        type_stack.push(VT_INVALID);
    }

    void push_numeric(VarType type, Instruction i_bc, Instruction d_bc) {
        switch(type) {
        case VT_INT:
            translated_function.bytecode()->addInsn(i_bc);
            break;
        case VT_DOUBLE:
            translated_function.bytecode()->addInsn(d_bc);
            break;
        default:
            invalidate();
            break;
        }
    }

    void push_comparison(VarType type, Instruction i_bc, Instruction d_bc, Instruction s_bc) {
        switch(type) {
        case VT_INT:
            translated_function.bytecode()->addInsn(i_bc);
            break;
        case VT_DOUBLE:
            translated_function.bytecode()->addInsn(d_bc);
            break;
        case VT_STRING:
            translated_function.bytecode()->addInsn(s_bc);
            break;
        default:
            invalidate();
            break;
        }
    }

    void push_logic(VarType type, Instruction bc) {
        if(type != VT_INT) {
            invalidate();
            break;
        }
        translated_function.bytecode()->addInsn(bc);
    }

    void push_store(VarType type) {
        VarType last_type = update_type_stack_un();
        if(last_type != type) {
            invalidate();
            return;
        }
        switch(type) {
        case VT_INT:
            translated_function.bytecode()->addInsn(BC_STORECTXIVAR);
            break;
        case VT_DOUBLE:
            translated_function.bytecode()->addInsn(BC_STORECTXDVAR);
            break;
        case VT_STRING:
            translated_function.bytecode()->addInsn(BC_STORECTXSVAR);
            break;
        default:
            invalidate();
            break;
        }
        return;
    }

    // returns the position of the jmp's argument, 0 on error
    uint32_t push_cond_jump() {
        if(type_stack.size() < 2) {
            invalidate();
            return 0;
        }

        VatType type_zero = type_stack.pop();
        VarType type_expr = type_stack.pop();
        if(type_zero == VT_INT && type_expr == VT_INT) {
            // if `cond == 0`, i.e. false -- jump to "after block"
            translated_function.bytecode()->addInsn(BC_IFICMPE);
            uint32_t index = translated_function.bytecode()->current();
            translated_function.bytecode()->addInt16(0); // temporarily
            return index;
        }

        invalidate();
        return 0;
    }

    void push_load_i(uint16_t scope_id, uint16_t var_id) {
        translated_function.bytecode()->addInsn(BC_LOADCTXIVAR);
        translated_function.bytecode()->addTyped(scope_id);
        translated_function.bytecode()->addTyped(var_id);
        type_stack.push(VT_INT);
    }

    void push_store_i(uint16_t scope_id, uint16_t var_id) {
        translated_function.bytecode()->addInsn(BC_STORECTXIVAR);
        translated_function.bytecode()->addTyped(scope_id);
        translated_function.bytecode()->addTyped(var_id);
    }

    void push_ja(uint32_t to) {
        translated_function.bytecode()->addInsn(BC_JA);
        uint32_t from = translated_function.bytecode()->current();
        uint32_t_t offset = to - from;
        assert(offset == (int16_t)offset);
        translated_function.bytecode()->addInt16((int16_t)offset);
    }

    void update_jmp(uint32_t from) {
        uint32_t to = translated_function.bytecode()->current();
        uint32_t offset = to - from;
        assert(offset == (int16_t)offset);
        translated_function.bytecode()->setInt16(from, (int16_t)offset);
    }

    uint16_t store_scope(Scope* scope) {
        if(!scope_map.count(scope)) {
            uint16_t scope_id = (uint16_t)scope_map.size();
            scope_map.insert(scope, scope_id);
            var_map.insert(scope, VarNameMap());
            var_by_scope.push_back(vector<AstVar*>());
            return scope_id;
        }
        return scope_map[scope];
    }

    uint16_t store_var(Scope* scope, AstVar* var) {
        string name = var->name();
        uint16_t scope_id = store_scope();
        VarNameMap smap = var_map[scope];

        if(!smap.count(name)) {
            uint16_t var_id = smap.size();
            smap.insert(name, var_id);
            var_by_scope[scope_id].push_back(var);
            return var_id;
        }
        return smap[name];
    }

public:

    BytecodeTranslateVisitor() {}

    Bytecode program() {
        return bytecode;
    }

    virtual void visitBinaryOpNode(BinaryOpNode* node) {
        cerr << "[BinaryOp]" << endl;

        node->left()->visit(this);
        node->right()->visit(this);

        VarType type = update_type_stack();
        if(type == VT_INVALID || type == VT_VOID) {
            invalidate();
            return; // TODO: signal somehow else?
        }

        switch(node->kind()) {
        case tOR:
        case tAOR:
            push_logic(BC_IAOR);
            break;
        case tAND:
        case tAAND:
            push_logic(BC_IAAND);
            break;
        case tAXOR:
            push_logic(BC_IAXOR);
            break;
        case tEQ:
        case tGT:
        case tGE:
        case tLT:
        case tLE:
            if(type == VT_INT || type == VT_STRING) {
                // let's say that strings are only equal if they are the same
                bytecode.addInsn(BC_ICMP);
                break;
            }
            bytecode.add(BC_DCMP);
            break;
        case tADD:
            push_numeric(type, BC_IADD, BC_DADD);
            break;
        case tSUB:
            push_numeric(type, BC_ISUB, BC_DSUB);
            break;
        case tMUL:
            push_numeric(type, BC_IMUL, BC_DMUL);
            break;
        case tDIV:
            push_numeric(type, BC_IDIV, BC_DDIV);
            break;
        case tMOD:
            if(type == VT_INT) {
                bytecode.add(BC_MOD);
                break;
            }
            invalidate();
            break;
        }
    }

    virtual void visitUnaryOpNode(UnaryOpNode* node) {
        cerr << "[UnaryOp]" << endl;

        node->operand()->visit(this);

        VarType type = update_type_stack_un();
        if(type == VT_INVALID || type == VT_VOID || type == VT_STRING) {
            invalidate();
            return;
        }

        switch(node->kind()) {
        case tNOT:
            if(type != VT_INT) {
                invalidate();
                break;
            }
            bytecode.addTyped<uint16_t>(0);
            bytecode.addInsn(BC_ICMP);
            break;
        case tSUB:
            push_numeric(type, BC_INEG, BC_DNEG);
            break;
        default:
            invalidate();
            break;
        }
    }

    virtual void visitStringLiteralNode(StringLiteralNode* node) {
        cerr << "[StringLiteral]" << endl;

        uint16_t const_id = translated_code.makeStringConstant(node->literal());
        translated_function.bytecode()->addInsn(BC_SLOAD);
        translated_function.bytecode()->addTyped(const_id);
    }

    virtual void visitDoubleLiteralNode(DoubleLiteralNode* node) {
        cerr << "[DoubleLiteral]" << endl;

        translated_function.bytecode()->addInsn(BC_DLOAD);
        translated_function.bytecode()->addDouble(node->literal());
    }

    virtual void visitIntLiteralNode(IntLiteralNode* node) {
        cerr << "[IntLiteral]" << endl;

        translated_function.bytecode()->addInsn(BC_ILOAD);
        translated_function.bytecode()->addInt64(node->literal());
    }

    virtual void visitLoadNode(LoadNode* node) {
        cerr << "[Load]" << endl;

        const AstVar* var = node->var();
        Scope* scope = var->owner();
        uint16_t scope_id = store_scope(scope);
        uint16_t var_id = store_var(scope, var);

        VarType type = var->type();
        switch(type) {
        case VT_INT:
            translated_function.bytecode()->addInsn(BC_LOADCTXIVAR);
            break;
        case VT_DOUBLE:
            translated_function.bytecode()->addInsn(BC_LOADCTXDVAR);
            break;
        case VT_STRING:
            translated_function.bytecode()->addInsn(BC_LOADCTXSVAR);
            break;
        default:
            invalidate();
            break;
        }

        translated_function.bytecode()->addTyped(scope_id);
        translated_function.bytecode()->addTyped(var_id);
    }

    virtual void visitStoreNode(StoreNode* node) {
        cerr << "[Store]" << endl;

        TokenKind op = node->op();
        AstVar* var = node->var();
        Scope* scope = var->owner();
        VarType type = var->type();

        uint16_t scope_id = store_scope(scope);
        uint16_t var_id = store_var(scope, var);

        if(op == tINCRSET || op == tDECRSET) {
            switch(type) {
            case VT_INT:
                translated_function.bytecode()->addInsn(BC_LOADCTXIVAR);
                type_stack.push(VT_INT);
                break;
            case VT_DOUBLE:
                translated_function.bytecode()->addInsn(BC_LOADCTXDVAR);
                type_stack.push(VT_DOUBLE);
                break;
            default:
                invalidate();
                break;
            }

            translated_function.bytecode()->addTyped(scope_id);
            translated_function.bytecode()->addTyped(var_id);
        }

        node->value()->visit(this);

        if(op == tINCRSET) {
            push_numeric(type, BC_IADD, BC_DADD);
        } else if(op == tDECRSET) {
            push_numeric(type, BC_ISUB, BC_DSUB);
        }

        push_store(type);
        translated_function.bytecode()->addTyped(scope_id);
        translated_function.bytecode()->addTyped(var_id);
    }

    virtual void visitForNode(ForNode* node) {
        cerr << "[For]" << endl;

        // get and check the condition
        BinaryOpNode* range = node->inExpr();
        TokenKind op = range->kind();
        if(op != tRANGE) {
            cerr << "non-range op in for" << std::endl;
            invalidate();
            return;
        }

        // evaluate the condition start
        range->left()->visit(this);

        // load to var
        const AstVar* var = node->var();
        Scope* scope = var->owner();
        uint16_t scope_id = store_scope(scope);
        uint16_t var_id = store_var(scope, var);

        VarType type = var->type();
        if(type != VT_INT) {
            cerr << "non-int iterator in for" << endl;
            invalidate();
            return;
        }
        push_store_i(scope_id, var_id);

        uint32_t to_cond_pos = translated_function.bytecode()->current();

        // make condtion
        push_load_i(scope_id, var_id);

        range->right()->visit(this);
        type = update_type_stack_un();
        if(type != VT_INT) {
            cerr << "non-int cond in for" << endl;
            invalidate();
            return;
        }

        // set jump
        translated_function.bytecode()->addInsn(BC_IFICMPG);
        uint32_t cond_checked_pos= translated_function.bytecode()->current();
        translated_function.bytecode()->addInt16(0);

        // loop body
        node->body()->visit(this);

        // set incr
        push_load_i(scope_id, var_id);

        translated_function.bytecode()->addInsn(BC_ILOAD1);
        type_stack.push(VT_INT);

        translated_function.bytecode()->addInsn(BC_IADD);
        type = update_type_stack();
        assert(type == VT_INT);

        push_store_i(scope_id, var_id);

        // jump
        push_ja(to_cond_pos);
        update_jmp(cond_checked_pos);
    }

    virtual void visitWhileNode(WhileNode* node) {
        cerr << "[While]" << endl;

        uint32_t to_cond_pos = translated_function.bytecode()->current();

        node->whileExpr()->visit(this);
        translated_function.bytecode()->addInsn(BC_ILOAD0);
        type_stack.push(VT_INT);

        uint32_t cond_checked_pos = push_cond_jump();

        node->loopBlock()->visit(this);
        push_ja(to_cond_pos);

        update_jmp(cond_checked_pos);
    }

    virtual void visitIfNode(IfNode* node) {
        cerr << "[If]" << endl;

        // If...
        node->ifExpr()->visit(this);
        translated_function.bytecode()->addInsn(BC_ILOAD0);
        type_stack.push(VT_INT);
        uint32_t first_jmp_pos = push_cond_jump();

        // ... then ...
        node->thenBlock()->visit(this);
        uint32_t after_then_pos = translated_function.bytecode()->current();

        uint32_t offset = after_then_pos - first_jmp_pos;
        assert(offset == (int16_t)offset);
        translated_function.bytecode()->setInt16(first_jmp_pos, (int16_t)offset);

        // ... else
        if(node->elseBlock()) {
            translated_function.bytecode()->addInsn(BC_JA);
            uint32_t second_jmp_pos = translated_function.bytecode()->current();
            translated_function.bytecode()->addInt16(0);
            node->elseBlock()->visit(this);

            uint32_t after_else_pos = translated_function.bytecode()->current();
            uint32_t offset2 = after_else_pos - second_jmp_pos;
            assert(offset2 == (int16_t)offset2);

            translated_function.bytecode()->setInt16(second_jmp_pos, offset2);
        }
    }

    virtual void visitBlockNode(BlockNode* node) {
        cerr << "[Block]" << endl;

        Scope* scope = node->scope();
        store_scope(scope);

        for(Scope::VarIterator it(node->scope()); it.hasNext();) {
            AstVar* var = it.next();
            store_var(scope, var);
        }

        for(Scope::FunctionIterator it(node->scope()); it.hasNext();) {
            AstFunction* fun = it.next();
            BytecodeTranslateVisitor funVisitor(this);
            fun->node()->visit(this);
            need_semicolon = true;

            translated_code.addFunction()
        }

        for (uint32_t i = 0; i < node->nodes(); i++) {
            pout << indent;

            node->nodeAt(i)->visit(this);
            if(need_semicolon) {
                pout << ";\n";
            } else {
                need_semicolon = true;
            }
        }

        indent_size -= indent_shift;
        create_indent(indent_size);
        cerr << "[/" << indent_size << " " << node << "]" << endl;
    }

    virtual void visitFunctionNode(FunctionNode* node) {
        cerr << "[Function]" << node->name() << endl;

        pout << "function " << typeToName(node->returnType())
             << " " << node->name() << "(";
        for(uint32_t i = 0; i < node->parametersNumber(); i++) {
            if(i > 0) {
                pout << ", ";
            }

            string parameterType =
                    string(typeToName(node->parameterType(i)));
            string parameterName = node->parameterName(i);
            pout << parameterType << " " << parameterName;
        }
        pout << ") {\n";
        node->body()->visit(this);
        pout << create_indent(indent_size - indent_shift) << "}\n";
        need_semicolon = false;
    }

    virtual void visitReturnNode(ReturnNode* node) {
        cerr << "[Return]" << endl;

        pout << "return ";
        AstNode* return_expr = node->returnExpr();
        if(return_expr == NULL) {
            pout << "void";
        } else {
            return_expr->visit(this);
        }
    }

    virtual void visitCallNode(CallNode* node) {
        cerr << "[Call]" << endl;

        pout << node->name() << "(";
        for(uint32_t i = 0; i < node->parametersNumber(); i++) {
            if(i > 0) {
                pout << ", ";
            }
            node->parameterAt(i)->visit(this);
        }
        pout << ")";
    }

    virtual void visitNativeCallNode(NativeCallNode* node) {
        cerr << "[NativeCall]" << endl;

        pout << "native '" << node->nativeName() << "'";
    }

    virtual void visitPrintNode(PrintNode* node) {
        cerr << "[Print]" << endl;

        pout << "print(";
        for(uint32_t i = 0; i < node->operands(); i++) {
            if(i > 0) {
                pout << ", ";
            }
            node->operandAt(i)->visit(this);
        }
        pout << ")";
    }
};

}

#endif // _AST_TO_BYTECODE_IMPL_H
