#ifndef _BYTECODE_CODE_H
#define _BYTECODE_CODE_H

#include "../include/ast.h"
#include "../include/mathvm.h"
#include "../include/visitors.h"

#include <vector>
#include <stack>
#include <map>

namespace mathvm {

typedef union {
    double _doubleValue;
    int64_t _intValue;
    const char* _stringValue;
} Value;

class BytecodeCode : public Code {
    typedef map<Scope*, uint16_t> ScopeMap;
    typedef map<string, uint16_t> VarNameMap;

    ScopeMap scope_map;
    vector<Scope*> socpes;
    map<Scope*, VarNameMap> var_map;

    BytecodeFunction translated_function;
    vector<vector<Var>> *var_by_scope;

    vector<uint16_t> scope_stack;
    stack<Value> value_stack;
    vector<Bytecode*> call_stack;
public:

    BytecodeCode() = default;

    BytecodeCode(vector<vector<Var>> *v_ptr): BytecodeCode(), var_by_scope(v_ptr) {}

    Bytecode* bytecode() {
        return translated_function.bytecode();
    }

    BytecodeFunction* get_translated_function() {
        return &translated_function;
    }

    vector<vector<Var> > get_var_by_scope() {
        return *var_by_scope;
    }

    void set_clear() {
        translated_function = BytecodeFunction();
    }

    uint16_t add_scope(Scope* scope) {
        if(!scope_map.count(scope)) {
            uint16_t scope_id = (uint16_t)scope_map.size();
            scope_map.insert(scope, scope_id);
            scopes.push_back(scope);
            var_map.insert(scope, VarNameMap());
            var_by_scope.push_back(vector<Var>());
            return scope_id;
        }
        return scope_map[scope];
    }

    uint16_t add_var(Scope* scope, VarType type, string name) {
        uint16_t scope_id = add_scope();
        VarNameMap smap = var_map[scope];

        if(!smap.count(name)) {
            uint16_t var_id = smap.size();
            smap.insert(name, var_id);
            var_by_scope[scope_id].emplace_back(type, name);
            return var_id;
        }
        return smap[name];
    }

    uint16_t add_var(Scope* scope, AstVar* var) {
        return add_var(scope, var->type(), var->name());
    }

    uint16_t fun_id_by_name(string name) {
        FunctionMap::const_iterator it = _functionById.find(name);
        if (it == _functionById.end()) {
            return 0;
        }
        return (*it).second;
    }

    uint16_t native_id_by_name(string name) {
        NativeMap::const_iterator it = _nativeById.find(name);
        if (it == _nativeById.end()) {
            return 0;
        }
        return (*it).second;
    }

    /***/

    void setVar(Var* to, Var* from) {
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

    void call(int call_id) {
        Bytecode* cur = call_stack[call_id];
        uint32_t len = cur->length();
        uint32_t i = 0;
        Value t;
        Value b;
        while(i < len) {
            Instruction insn = cur->getInsn(i);
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
                double dval = cur->getDouble(i + 1);
                value_stack.emplace(dval);
                i += (sizeof(Instruction) + sizeof(double)) / sizeof(uint8_t);
                break;

            case BC_ILOAD:
                int64_t ival = cur->getInt64(i + 1);
                value_stack.emplace(ival);
                i += (sizeof(Instruction) + sizeof(int64_t)) / sizeof(uint8_t);
                break;

            case BC_SLOAD:
                uint16_t sid = cur->getTyped(i + 1);
                const string& str = constantById(sid);
                value_stack.emplace(str);
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
                uint16_t sid = cur->getTyped(i + 1);
                const string& str = constantById(sid);
                cout << str;
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
                int16_t offset = cur->getTyped(i + 1);
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
                int16_t offset = cur->getTyped(i + 1);
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
                int16_t offset = cur->getTyped(i + 1);
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
                int16_t offset = cur->getTyped(i + 1);
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
                int16_t offset = cur->getTyped(i + 1);
                i += (sizeof(Instruction) + sizeof(int16_t)) / sizeof(uint8_t);
                if(t._intValue < b._intValue) {
                    i += offset;
                }
                break;

            case BC_JA:
                int16_t offset = cur->getTyped(i + 1);
                i += offset + ((sizeof(Instruction) + sizeof(int16_t)) / sizeof(uint8_t));
                break;

            case BC_LOADCTXDVAR:
                int16_t scope_id = cur->getTyped(i + 1);
                int16_t var_id = cur->getTyped(i + 1 + 2);
                value_stack.emplace((*var_by_scope)[scope_id][var_id].getDoubleValue());
                i += 1 + 2 + 2;
                break;

            case BC_LOADCTXIVAR:
                int16_t scope_id = cur->getTyped(i + 1);
                int16_t var_id = cur->getTyped(i + 1 + 2);
                value_stack.emplace((*var_by_scope)[scope_id][var_id].getIntValue());
                i += 1 + 2 + 2;
                break;

            case BC_LOADCTXSVAR:
                int16_t scope_id = cur->getTyped(i + 1);
                int16_t var_id = cur->getTyped(i + 1 + 2);
                value_stack.emplace((*var_by_scope)[scope_id][var_id].getStringValue);
                i += 1 + 2 + 2;
                break;

            case BC_STORECTXDVAR:
                int16_t scope_id = cur->getTyped(i + 1);
                int16_t var_id = cur->getTyped(i + 1 + 2);
                t = value_stack.top();
                value_stack.pop();
                (*var_by_scope)[scope_id][var_id].setDoubleValue(t._doubleValue);
                i += 1 + 2 + 2;
                break;

            case BC_STORECTXIVAR:
                int16_t scope_id = cur->getTyped(i + 1);
                int16_t var_id = cur->getTyped(i + 1 + 2);
                t = value_stack.top();
                value_stack.pop();
                (*var_by_scope)[scope_id][var_id].setIntValue(t._intValue);
                i += 1 + 2 + 2;
                break;

            case BC_STORECTXSVAR:
                int16_t scope_id = cur->getTyped(i + 1);
                int16_t var_id = cur->getTyped(i + 1 + 2);
                t = value_stack.top();
                value_stack.pop();
                (*var_by_scope)[scope_id][var_id].setStringValue(t._stringValue);
                i += 1 + 2 + 2;
                break;

            case BC_CALL:
                uint16_t fun_id = cur->getUInt16(i + 1);
                BytecodeFunction* f = (BytecodeFunction*)functionById(fun_id);
                call_stack.push_back(f->bytecode());
                int stack_size = value_stack.size();
                call(call_stack.size() - 1);
                int diff = value_stack.size() - stack_size;
                if(diff != 0 && diff != 1) {
                    cerr << "Suspicious value stack size (d "
                         << diff << ") after function call " << fun_id << endl;
                }
                call_stack.pop_back();
                i += (sizeof(Instruction) + sizeof(uint16_t)) / sizeof(uint8_t);
                break;

            case BC_CALLNATIVE:
                uint16_t nat_id = cur->getUInt16(i + 1);
                Signature* signature;
                string* name;
                void* handler = nativeById(nat_id, &signature, &name);
                i += (sizeof(Instruction) + sizeof(uint16_t)) / sizeof(uint8_t);
                break;

            case BC_RETURN:
                return;
            default:
                cerr << "Unknown bytecode " << string(bytecodeName(insn))
                     << "at the position " << i << endl;
            }
        }
    }

    virtual Status* execute(vector<Var *> &vars) {
        uint16_t top_scope_id = 0;
        Scope* top_scope = scopes[top_scope_id];
        for(Var* var: vars) {
            if(var_map[top_scope].count(var->name())) {
                setVar(&(*var_by_scope)[top_scope_id][var->name()], var);
            } else {
                cerr << "Unknown global var; type " << typeToName(var->type())
                     << ", name " << var->name() << endl;
            }
        }
        call_stack.push_back(translated_function.bytecode());
        call(0);
    }

    /*
     * BC_CALL
        BC_CALLNATIVE
        BC_DADD
        BC_DCMP
        BC_DDIV
        BC_DLOAD
        BC_DMUL
        BC_DNEG
        BC_DPRINT
        BC_DSUB
        BC_IAAND
        BC_IADD
        BC_IAOR
        BC_IAXOR
        BC_ICMP
        BC_IDIV
        BC_IFICMPE
        BC_IFICMPG
        BC_ILOAD
        BC_IMUL
        BC_INEG
        BC_IPRINT
        BC_ISUB
        BC_JA
        BC_LOADCTXDVAR
        BC_LOADCTXIVAR
        BC_LOADCTXSVAR
        BC_MOD
        BC_RETURN
        BC_SLOAD
        BC_SPRINT
        BC_STORECTXDVAR
        BC_STORECTXIVAR
        BC_STORECTXSVAR
     */
};

}

#endif // _BYTECODE_CODE_H
