#include "../include/ast.h"
#include "../include/mathvm.h"
#include "../include/visitors.h"

#include "include/bytecode_code.h"

#include <vector>
#include <stack>
#include <map>
#include <iostream>
#include <fstream>

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

        switch(type) {
        case VT_INT:
            (*var_by_scope)[scope_id][var_id].setIntValue(0);
            break;
        case VT_DOUBLE:
            (*var_by_scope)[scope_id][var_id].setDoubleValue(0);
            break;
        case VT_STRING:
            (*var_by_scope)[scope_id][var_id].setStringValue("");
            break;
        default:
            break;
        }

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
    ofstream out("debug.output");
    // cerr << call_stack[call_id] << endl;
    assert(call_id < (int)call_stack.size());
//    uint32_t len = cur->length();
//    uint32_t i = 0;

    cur->dump(out);

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
//    uint16_t nat_id;
    BytecodeFunction* f;
//    Signature* signature;
//    string* name;
//    void* handler;
    Status* status;
    int stack_size;
    int diff;

    for (size_t bci = 0; bci < cur->length();) {
        size_t length;
        Instruction insn = cur->getInsn(bci);
        out << bci << ": ";
        cerr << "value_stack.size: "
             << value_stack.size() << endl;
        const char* name = bytecodeName(insn, &length);
        switch (insn) {
            case BC_DLOAD:
                out << name << " " << cur->getDouble(bci + 1);

                dval = cur->getDouble(bci + 1);
                value_stack.emplace(dval);

                break;
            case BC_ILOAD:
                out << name << " " << cur->getInt64(bci + 1);

                ival = cur->getInt64(bci + 1);
                value_stack.emplace(ival);

                break;
            case BC_DLOAD0:
                out << name;

                value_stack.emplace(0.0);

                break;
            case BC_ILOAD0:
                out << name;

                value_stack.emplace(0);

                break;
            case BC_DLOAD1:
                out << name;

                value_stack.emplace(1.0);

                break;
            case BC_ILOAD1:
                out << name;

                value_stack.emplace(1);

                break;
            case BC_SLOAD:
                out << name << " @" << cur->getUInt16(bci + 1);

                sid = cur->getUInt16(bci + 1);
                value_stack.emplace(constantById(sid));

                break;
            case BC_CALL:
                out << name << " *" << cur->getUInt16(bci + 1);

                fun_id = cur->getUInt16(bci + 1);
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
                    return Status::Error("Suspicious value stack size", bci);
                }
                call_stack.pop_back();

                break;
            case BC_CALLNATIVE:
                out << name << " *" << cur->getUInt16(bci + 1);
                break;
            case BC_LOADDVAR:
            case BC_STOREDVAR:
            case BC_LOADIVAR:
            case BC_STOREIVAR:
            case BC_LOADSVAR:
            case BC_STORESVAR:
                out << name << " @" << cur->getUInt16(bci + 1);
                break;
            case BC_LOADCTXDVAR:
                out << name << " @" << cur->getUInt16(bci + 1)
                    << ":" << cur->getUInt16(bci + 3);

                scope_id = cur->getUInt16(bci + 1);
                var_id = cur->getUInt16(bci + 3);
                value_stack.emplace((*var_by_scope)[scope_id][var_id].getDoubleValue());

                break;
            case BC_STORECTXDVAR:
                out << name << " @" << cur->getUInt16(bci + 1)
                    << ":" << cur->getUInt16(bci + 3);

                scope_id = cur->getUInt16(bci + 1);
                var_id = cur->getUInt16(bci + 3);
                t = value_stack.top();
                value_stack.pop();
                (*var_by_scope)[scope_id][var_id].setDoubleValue(t._doubleValue);

                break;
            case BC_LOADCTXIVAR:
                out << name << " @" << cur->getUInt16(bci + 1)
                    << ":" << cur->getUInt16(bci + 3);

                scope_id = cur->getUInt16(bci + 1);
                var_id = cur->getUInt16(bci + 3);
                value_stack.emplace((*var_by_scope)[scope_id][var_id].getIntValue());

                break;
            case BC_STORECTXIVAR:
                out << name << " @" << cur->getUInt16(bci + 1)
                    << ":" << cur->getUInt16(bci + 3);

                scope_id = cur->getUInt16(bci + 1);
                var_id = cur->getUInt16(bci + 3);
                t = value_stack.top();
                value_stack.pop();
                (*var_by_scope)[scope_id][var_id].setIntValue(t._intValue);

                break;
            case BC_LOADCTXSVAR:
                out << name << " @" << cur->getUInt16(bci + 1)
                    << ":" << cur->getUInt16(bci + 3);

                scope_id = cur->getUInt16(bci + 1);
                var_id = cur->getUInt16(bci + 3);
                value_stack.emplace((*var_by_scope)[scope_id][var_id].getStringValue());

                break;
            case BC_STORECTXSVAR:
                out << name << " @" << cur->getUInt16(bci + 1)
                    << ":" << cur->getUInt16(bci + 3);

                scope_id = cur->getUInt16(bci + 1);
                var_id = cur->getUInt16(bci + 3);
                t = value_stack.top();
                value_stack.pop();
                (*var_by_scope)[scope_id][var_id].setDoubleValue(t._doubleValue);

                break;
            case BC_IFICMPNE:
                out << name << " " << cur->getInt16(bci + 1) + bci + 1;

                t = value_stack.top();
                value_stack.pop();
                b = value_stack.top();
                value_stack.pop();
                offset = cur->getInt16(bci + 1);
                if(t._intValue != b._intValue) {
                    bci += offset;
                }

                break;
            case BC_IFICMPE:
                out << name << " " << cur->getInt16(bci + 1) + bci + 1;

                t = value_stack.top();
                value_stack.pop();
                b = value_stack.top();
                value_stack.pop();
                offset = cur->getInt16(bci + 1);
                if(t._intValue == b._intValue) {
                    bci += offset;
                }

                break;
            case BC_IFICMPG:
                out << name << " " << cur->getInt16(bci + 1) + bci + 1;

                t = value_stack.top();
                value_stack.pop();
                b = value_stack.top();
                value_stack.pop();
                offset = cur->getInt16(bci + 1);
                if(t._intValue > b._intValue) {
                    bci += offset;
                }

                break;
            case BC_IFICMPGE:
                out << name << " " << cur->getInt16(bci + 1) + bci + 1;

                t = value_stack.top();
                value_stack.pop();
                b = value_stack.top();
                value_stack.pop();
                offset = cur->getInt16(bci + 1);
                if(t._intValue >= b._intValue) {
                    bci += offset;
                }

                break;
            case BC_IFICMPL:
                out << name << " " << cur->getInt16(bci + 1) + bci + 1;

                t = value_stack.top();
                value_stack.pop();
                b = value_stack.top();
                value_stack.pop();
                offset = cur->getInt16(bci + 1);
                if(t._intValue < b._intValue) {
                    bci += offset;
                }

                break;
            case BC_IFICMPLE:
                out << name << " " << cur->getInt16(bci + 1) + bci + 1;

                t = value_stack.top();
                value_stack.pop();
                b = value_stack.top();
                value_stack.pop();
                offset = cur->getInt16(bci + 1);
                if(t._intValue <= b._intValue) {
                    bci += offset;
                }

                break;
            case BC_JA:
                out << name << " " << cur->getInt16(bci + 1) + bci + 1;

                offset = cur->getInt16(bci + 1);
                bci += offset;

                break;
            case BC_RETURN:
                out << name;
                return Status::Ok();

            case BC_DADD:
                out << name;
                t = value_stack.top();
                value_stack.pop();
                b = value_stack.top();
                value_stack.pop();
                value_stack.emplace(t._doubleValue + b._doubleValue);
                break;

            case BC_IADD:
                out << name;
                t = value_stack.top();
                value_stack.pop();
                b = value_stack.top();
                value_stack.pop();
                value_stack.emplace(t._intValue + b._intValue);
                break;

            case BC_DCMP:
                out << name;
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
                break;

            case BC_ICMP:
                out << name;
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
                break;

            case BC_DDIV:
            out << name;
                t = value_stack.top();
                value_stack.pop();
                b = value_stack.top();
                value_stack.pop();
                value_stack.emplace(t._doubleValue / b._doubleValue);
                break;

            case BC_IDIV:
                out << name;
                t = value_stack.top();
                value_stack.pop();
                b = value_stack.top();
                value_stack.pop();
                value_stack.emplace(t._intValue / b._intValue);
                break;

            case BC_DMUL:
                out << name;
                t = value_stack.top();
                value_stack.pop();
                b = value_stack.top();
                value_stack.pop();
                value_stack.emplace(t._doubleValue * b._doubleValue);
                break;

            case BC_IMUL:
                out << name;
                t = value_stack.top();
                value_stack.pop();
                b = value_stack.top();
                value_stack.pop();
                value_stack.emplace(t._intValue * b._intValue);
                break;

            case BC_DNEG:
                out << name;
                t = value_stack.top();
                value_stack.pop();
                value_stack.emplace(-t._doubleValue);
                break;

            case BC_INEG:
                out << name;
                t = value_stack.top();
                value_stack.pop();
                value_stack.emplace(-t._intValue);
                break;

            case BC_DPRINT:
                out << name;
                t = value_stack.top();
                value_stack.pop();
                cout << t._doubleValue;
                break;

            case BC_IPRINT:
                out << name;
                t = value_stack.top();
                value_stack.pop();
                cout << t._intValue;
                break;

            case BC_SPRINT:
                out << name;
                t = value_stack.top();
                value_stack.pop();
                cout << t._stringValue;
                break;

            case BC_DSUB:
                out << name;
                t = value_stack.top();
                value_stack.pop();
                b = value_stack.top();
                value_stack.pop();
                value_stack.emplace(t._doubleValue - b._doubleValue);
                break;

            case BC_ISUB:
                out << name;
                t = value_stack.top();
                value_stack.pop();
                b = value_stack.top();
                value_stack.pop();
                value_stack.emplace(t._intValue - b._intValue);
                break;

            case BC_IMOD:
                out << name;
                t = value_stack.top();
                value_stack.pop();
                b = value_stack.top();
                value_stack.pop();
                value_stack.emplace(t._intValue % b._intValue);
                break;

            case BC_IAAND:
                out << name;
                t = value_stack.top();
                value_stack.pop();
                b = value_stack.top();
                value_stack.pop();
                value_stack.emplace(t._intValue & b._intValue);
                break;

            case BC_IAOR:
                out << name;
                t = value_stack.top();
                value_stack.pop();
                b = value_stack.top();
                value_stack.pop();
                value_stack.emplace(t._intValue | b._intValue);
                break;

            case BC_IAXOR:
                out << name;
                t = value_stack.top();
                value_stack.pop();
                b = value_stack.top();
                value_stack.pop();
                value_stack.emplace(t._intValue ^ b._intValue);
                break;
          default:
                out << name;
        }
        out << endl;
        bci += length;
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
//    Scope* top_scope = scopes[top_scope_id];
    for(Var* var: vars) {
//        if(var_map[top_scope].count(var->name())) {
        for(int i = 0; i < (int)(*var_by_scope)[top_scope_id].size(); ++i) {
            Var v = (*var_by_scope)[top_scope_id][i];
            if(v.name() != var->name()) {
                continue;
            }
//            uint16_t var_id = var_map[top_scope][var->name()];
            set_var(&(*var_by_scope)[top_scope_id][i], var);
            break;
        }

    }
    call_stack.push_back(translated_function->bytecode());
//    cerr << call_stack[0] << endl;
//    cerr << translated_function->bytecode() << endl;
    Status* status = call(0);
    return status;
}

}
