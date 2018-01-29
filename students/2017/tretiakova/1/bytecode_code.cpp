#include "../include/ast.h"
#include "../include/mathvm.h"
#include "../include/visitors.h"

#include "include/bytecode_code.h"

#include <vector>
#include <stack>
#include <map>

namespace mathvm {

//    BytecodeCode() {
//        translated_function = NULL;
//        var_by_scope = new vector<vector<Var>>();
//    }

//    BytecodeCode(BytecodeFunction* bf, vector<vector<Var>> *v_ptr):
//        BytecodeCode() {
//        translated_function = bf;
//        var_by_scope = v_ptr;
//    }

void BytecodeCode::set_translated_function(BytecodeFunction* bf) {
    translated_function = bf;
}

vector<vector<Var> > BytecodeCode::get_var_by_scope() {
    return *var_by_scope;
}

uint16_t BytecodeCode::add_scope(Scope* scope) {
    if(!scope_map.count(scope)) {
        uint16_t scope_id = (uint16_t)scope_map.size();
        scope_map[scope] = scope_id;
        assert(scope_id == scopes.size());
        scopes.push_back(scope);
        var_map[scope] = VarNameMap();
        var_by_scope->push_back(vector<Var>());
        return scope_id;
    }
    return scope_map[scope];
}

uint16_t BytecodeCode::add_var(Scope* scope, VarType type, string name) {
    uint16_t scope_id = add_scope(scope);
    if(!var_map[scope].count(name)) {
        uint16_t var_id = var_map[scope].size();
        assert(var_id == (*var_by_scope)[scope_id].size());
        var_map[scope][name] = var_id;
        (*var_by_scope)[scope_id].emplace_back(type, name);
        return var_id;
    }
    return var_map[scope][name];
}

uint16_t BytecodeCode::add_var(Scope* scope, AstVar* var) {
    return add_var(scope, var->type(), var->name());
}

/***/

void BytecodeCode::set_var(Var* to, Var* from) {
    switch(from->type()) {
    case VT_INT:
        to->setIntValue(from->getIntValue());
        return;
    case VT_DOUBLE:
        to->setDoubleValue(from->getDoubleValue());
        return;
    case VT_STRING:
        to->setStringValue(from->getStringValue());
        return;
    default:
        cerr << "Invalid variable type" << endl;
        assert(false);
    }
}

Status* BytecodeCode::call(int call_id) {
    Bytecode* cur = call_stack[call_id];
    // cerr << call_stack[call_id] << endl;
    uint32_t len = cur->length();
    uint32_t i = 0;

    // cannot define them in the switch-block
    Value t;
    Value b;
    double dval;
    int64_t ival;
    int16_t  offset;
    uint16_t sid;
    uint16_t scope_id;
    uint16_t var_id;
    uint16_t fun_id;
    uint16_t nat_id;
    BytecodeFunction* f;
    Signature* signature;
    string* name;
    void* handler;
    Status* status;
    int stack_size;
    int diff;

    while(i < len) {
        Instruction insn = cur->getInsn(i);
        cerr << "Insn: " << insn
             << " i: " << i
             << " len: " << len << endl;

        switch(insn) {
        case BC_DADD:
            t = value_stack.top();
            value_stack.pop();
            b = value_stack.top();
            value_stack.pop();
            value_stack.emplace(t._doubleValue + b._doubleValue);
            i += sizeof(Instruction) / sizeof(uint8_t);
            break;

        case BC_IADD:
            t = value_stack.top();
            value_stack.pop();
            b = value_stack.top();
            value_stack.pop();
            value_stack.emplace(t._intValue + b._intValue);
            i += sizeof(Instruction) / sizeof(uint8_t);
            break;

        case BC_DCMP:
            t = value_stack.top();
            value_stack.pop();
            b = value_stack.top();
            value_stack.pop();
            if(t._doubleValue < b._doubleValue) {
                value_stack.emplace(-1);
            } else if(t._doubleValue == b._doubleValue) {
                value_stack.emplace(0);
            } else {
                value_stack.emplace(1);
            }
            i += sizeof(Instruction) / sizeof(uint8_t);
            break;

        case BC_ICMP:
            t = value_stack.top();
            value_stack.pop();
            b = value_stack.top();
            value_stack.pop();
            if(t._intValue < b._intValue) {
                value_stack.emplace(-1);
            } else if(t._intValue == b._intValue) {
                value_stack.emplace(0);
            } else {
                value_stack.emplace(1);
            }
            i += sizeof(Instruction) / sizeof(uint8_t);
            break;

        case BC_DDIV:
            t = value_stack.top();
            value_stack.pop();
            b = value_stack.top();
            value_stack.pop();
            value_stack.emplace(t._doubleValue / b._doubleValue);
            i += sizeof(Instruction) / sizeof(uint8_t);
            break;

        case BC_IDIV:
            t = value_stack.top();
            value_stack.pop();
            b = value_stack.top();
            value_stack.pop();
            value_stack.emplace(t._intValue / b._intValue);
            i += sizeof(Instruction) / sizeof(uint8_t);
            break;

        case BC_DLOAD:
            dval = cur->getDouble(i + 1);
            value_stack.emplace(dval);
            i += (sizeof(Instruction) + sizeof(double)) / sizeof(uint8_t);
            break;

        case BC_ILOAD:
            ival = cur->getInt64(i + 1);
            value_stack.emplace(ival);
            i += (sizeof(Instruction) + sizeof(int64_t)) / sizeof(uint8_t);
            break;

        case BC_SLOAD:
            sid = cur->getUInt16(i + 1);
            value_stack.emplace(constantById(sid));
            i += (sizeof(Instruction) + sizeof(uint16_t)) / sizeof(uint8_t);
            break;

        case BC_DMUL:
            t = value_stack.top();
            value_stack.pop();
            b = value_stack.top();
            value_stack.pop();
            value_stack.emplace(t._doubleValue * b._doubleValue);
            i += sizeof(Instruction) / sizeof(uint8_t);
            break;

        case BC_IMUL:
            t = value_stack.top();
            value_stack.pop();
            b = value_stack.top();
            value_stack.pop();
            value_stack.emplace(t._intValue * b._intValue);
            i += sizeof(Instruction) / sizeof(uint8_t);
            break;

        case BC_DNEG:
            t = value_stack.top();
            value_stack.pop();
            value_stack.emplace(-t._doubleValue);
            i += sizeof(Instruction) / sizeof(uint8_t);
            break;

        case BC_INEG:
            t = value_stack.top();
            value_stack.pop();
            value_stack.emplace(-t._intValue);
            i += sizeof(Instruction) / sizeof(uint8_t);
            break;

        case BC_DPRINT:
            t = value_stack.top();
            value_stack.pop();
            cout << t._doubleValue;
            i += sizeof(Instruction) / sizeof(uint8_t);
            break;

        case BC_IPRINT:
            t = value_stack.top();
            value_stack.pop();
            cout << t._intValue;
            i += sizeof(Instruction) / sizeof(uint8_t);
            break;

        case BC_SPRINT:
            sid = cur->getUInt16(i + 1);
            cout << constantById(sid);
            i += (sizeof(Instruction) + sizeof(uint16_t)) / sizeof(uint8_t);
            break;

        case BC_DSUB:
            t = value_stack.top();
            value_stack.pop();
            b = value_stack.top();
            value_stack.pop();
            value_stack.emplace(t._doubleValue - b._doubleValue);
            i += sizeof(Instruction) / sizeof(uint8_t);
            break;

        case BC_ISUB:
            t = value_stack.top();
            value_stack.pop();
            b = value_stack.top();
            value_stack.pop();
            value_stack.emplace(t._intValue - b._intValue);
            i += sizeof(Instruction) / sizeof(uint8_t);
            break;

        case BC_IMOD:
            t = value_stack.top();
            value_stack.pop();
            b = value_stack.top();
            value_stack.pop();
            value_stack.emplace(t._intValue % b._intValue);
            i += sizeof(Instruction) / sizeof(uint8_t);
            break;

        case BC_IAAND:
            t = value_stack.top();
            value_stack.pop();
            b = value_stack.top();
            value_stack.pop();
            value_stack.emplace(t._intValue && b._intValue);
            i += sizeof(Instruction) / sizeof(uint8_t);
            break;

        case BC_IAOR:
            t = value_stack.top();
            value_stack.pop();
            b = value_stack.top();
            value_stack.pop();
            value_stack.emplace(t._intValue || b._intValue);
            i += sizeof(Instruction) / sizeof(uint8_t);
            break;

        case BC_IAXOR:
            t = value_stack.top();
            value_stack.pop();
            b = value_stack.top();
            value_stack.pop();
            value_stack.emplace(t._intValue != b._intValue);
            i += sizeof(Instruction) / sizeof(uint8_t);
            break;

        case BC_IFICMPG:
            t = value_stack.top();
            value_stack.pop();
            b = value_stack.top();
            value_stack.pop();
            offset = cur->getInt16(i + 1);
            i += (sizeof(Instruction) + sizeof(int16_t)) / sizeof(uint8_t);
            if(t._intValue > b._intValue) {
                i += offset;
            }
            break;

        case BC_IFICMPGE:
            t = value_stack.top();
            value_stack.pop();
            b = value_stack.top();
            value_stack.pop();
            offset = cur->getInt16(i + 1);
            i += (sizeof(Instruction) + sizeof(int16_t)) / sizeof(uint8_t);
            if(t._intValue >= b._intValue) {
                i += offset;
            }
            break;

        case BC_IFICMPE:
            t = value_stack.top();
            value_stack.pop();
            b = value_stack.top();
            value_stack.pop();
            offset = cur->getInt16(i + 1);
            i += (sizeof(Instruction) + sizeof(int16_t)) / sizeof(uint8_t);
            if(t._intValue == b._intValue) {
                i += offset;
            }
            break;

        case BC_IFICMPLE:
            t = value_stack.top();
            value_stack.pop();
            b = value_stack.top();
            value_stack.pop();
            offset = cur->getInt16(i + 1);
            i += (sizeof(Instruction) + sizeof(int16_t)) / sizeof(uint8_t);
            if(t._intValue <= b._intValue) {
                i += offset;
            }
            break;

        case BC_IFICMPL:
            t = value_stack.top();
            value_stack.pop();
            b = value_stack.top();
            value_stack.pop();
            offset = cur->getInt16(i + 1);
            i += (sizeof(Instruction) + sizeof(int16_t)) / sizeof(uint8_t);
            if(t._intValue < b._intValue) {
                i += offset;
            }
            break;

        case BC_JA:
            offset = cur->getInt16(i + 1);
            i += offset + ((sizeof(Instruction) + sizeof(int16_t)) / sizeof(uint8_t));
            break;

        case BC_LOADCTXDVAR:
            scope_id = cur->getUInt16(i + 1);
            var_id = cur->getUInt16(i + 1 + 2);
            value_stack.emplace((*var_by_scope)[scope_id][var_id].getDoubleValue());
            i += 1 + 2 + 2;
            break;

        case BC_LOADCTXIVAR:
            scope_id = cur->getUInt16(i + 1);
            var_id = cur->getUInt16(i + 1 + 2);
            value_stack.emplace((*var_by_scope)[scope_id][var_id].getIntValue());
            i += 1 + 2 + 2;
            break;

        case BC_LOADCTXSVAR:
            scope_id = cur->getUInt16(i + 1);
            var_id = cur->getUInt16(i + 1 + 2);
            value_stack.emplace((*var_by_scope)[scope_id][var_id].getStringValue());
            i += 1 + 2 + 2;
            break;

        case BC_STORECTXDVAR:
            scope_id = cur->getUInt16(i + 1);
            var_id = cur->getUInt16(i + 1 + 2);
            t = value_stack.top();
            value_stack.pop();
            (*var_by_scope)[scope_id][var_id].setDoubleValue(t._doubleValue);
            i += 1 + 2 + 2;
            break;

        case BC_STORECTXIVAR:
            scope_id = cur->getUInt16(i + 1);
            var_id = cur->getUInt16(i + 1 + 2);
            t = value_stack.top();
            value_stack.pop();
            (*var_by_scope)[scope_id][var_id].setIntValue(t._intValue);
            i += 1 + 2 + 2;
            break;

        case BC_STORECTXSVAR:
            scope_id = cur->getUInt16(i + 1);
            var_id = cur->getUInt16(i + 1 + 2);
            t = value_stack.top();
            value_stack.pop();
            (*var_by_scope)[scope_id][var_id].setStringValue(t._stringValue);
            i += 1 + 2 + 2;
            break;

        case BC_CALL:
            fun_id = cur->getUInt16(i + 1);
            f = (BytecodeFunction*)functionById(fun_id);
            call_stack.push_back(f->bytecode());
            stack_size = value_stack.size();
            status = call(call_stack.size() - 1);
            if(status->isError()) {
                return status;
            }
            diff = value_stack.size() - stack_size;
            if(diff != 0 && diff != 1) {
                cerr << "Suspicious value stack size (d "
                     << diff << ") after function call " << fun_id << endl;
                return Status::Error("Suspicious value stack size", i);
            }
            call_stack.pop_back();
            i += (sizeof(Instruction) + sizeof(uint16_t)) / sizeof(uint8_t);
            break;

        case BC_CALLNATIVE:
            nat_id = cur->getUInt16(i + 1);
//                handler = nativeById(nat_id, &signature, &name);
            (void)nat_id;
            (void)handler;
            (void)signature;
            (void)name;
            i += (sizeof(Instruction) + sizeof(uint16_t)) / sizeof(uint8_t);
            break;

        case BC_RETURN:
            return Status::Ok();
        default:
            cerr << "Unexpected bytecode " << insn
                 << " at the position " << i << endl;
            return Status::Error("Unexpected bytecode", i);
        }
        cerr << "Finished [" << bytecodeName(insn) << "]" << endl;
    }
    return Status::Ok();
}

void print_vars(vector<vector<Var>>& vars) {
    for(int i = 0; i < (int)vars.size(); ++i) {
        cout << "scope " << i << ": ";
        for(int j = 0; j < (int)vars[i].size(); ++j) {
            cout << "(" << typeToName(vars[i][j].type())
                 << " " << vars[i][j].name() << ") ";
        }
        cout << endl;
    }
}

Status* BytecodeCode::execute(vector<Var *> &vars) {
    uint16_t top_scope_id = 0;
    Scope* top_scope = scopes[top_scope_id];
    for(Var* var: vars) {
        if(var_map[top_scope].count(var->name())) {
            uint16_t var_id = var_map[top_scope][var->name()];
            set_var(&(*var_by_scope)[top_scope_id][var_id], var);
        } else {
            print_vars(*var_by_scope);

            cerr << "Unknown global var; type " << typeToName(var->type())
                 << ", name " << var->name() << endl;
        }
    }
    call_stack.push_back(translated_function->bytecode());
//    cerr << call_stack[0] << endl;
//    cerr << translated_function->bytecode() << endl;
    Status* status = call(0);
    return status;
}

}
