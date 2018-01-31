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

int BytecodeCode::get_scope_id(Scope* scope) {
    if(!scope_map.count(scope)) {
        return -1;
    }
    return scope_map[scope];
}

int BytecodeCode::get_var_id(Scope* scope, string name) {
    if(!var_map[scope].count(name)) {
        return -1;
    }
    return var_map[scope][name];
}

uint16_t BytecodeCode::add_scope(Scope* scope) {
    if(!scope_map.count(scope)) {
        uint16_t scope_id = (uint16_t)scope_map.size();
        scope_map[scope] = scope_id;
        assert(scope_id == scopes.size());
        scopes.push_back(scope);
        var_map[scope] = VarNameMap();
        var_by_scope.push_back(vector<LocalVar>());
        return scope_id;
    }
    return scope_map[scope];
}

int BytecodeCode::add_var(Scope* scope, VarType type, string name) {
    int scope_id = get_scope_id(scope);
    if(scope_id < 0) {
        return scope_id;
    }

    if(!var_map[scope].count(name)) {
        uint16_t var_id = var_map[scope].size();
        assert(var_id == var_by_scope[scope_id].size());
        var_map[scope][name] = var_id;
        var_by_scope[scope_id].emplace_back(type, name);

        switch(type) {
        case VT_INT:
            var_by_scope[scope_id][var_id].setIntValue(0);
            break;
        case VT_DOUBLE:
            var_by_scope[scope_id][var_id].setDoubleValue(0);
            break;
        case VT_STRING:
            var_by_scope[scope_id][var_id].setStringValue("");
            break;
        default:
            break;
        }

        return var_id;
    }
    return var_map[scope][name];
}

/***/

void BytecodeCode::set_var(LocalVar* to, LocalVar* from) {
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
    Bytecode* cur = call_stack[call_id].bytecode();
    map<pair<uint16_t, uint16_t>, LocalVar>& local_vars =
            call_stack[call_id].local_vars();
    ofstream out("debug.output");

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
    StackFrame* f;
    Status* status;
    int stack_size;
    int diff;
    pair<uint16_t, uint16_t> identifier;

    for (size_t bci = 0; bci < cur->length();) {
        size_t length;
        Instruction insn = cur->getInsn(bci);
        out << bci << ": ";
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
                f = (StackFrame*)functionById(fun_id);
                call_stack.push_back(*f);
                stack_size = value_stack.size();
                status = call(call_stack.size() - 1);
                if(status->isError()) {
                    return status;
                }
                diff = stack_size - value_stack.size();
                if(diff != f->parametersNumber() && diff != f->parametersNumber() - 1) {
                    cerr << "Suspicious value stack size ("
                         << "was " << stack_size
                         << ", became " << value_stack.size()
                         << ") after function call '"
                         << functionById(fun_id)->name()
                         << "'" << endl;
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
                identifier = make_pair(scope_id, var_id);
                assert(local_vars.count(identifier) > 0);
                value_stack.emplace(local_vars[identifier].getDoubleValue());

                break;
            case BC_STORECTXDVAR:
                out << name << " @" << cur->getUInt16(bci + 1)
                    << ":" << cur->getUInt16(bci + 3);

                scope_id = cur->getUInt16(bci + 1);
                var_id = cur->getUInt16(bci + 3);
                identifier = make_pair(scope_id, var_id);
                t = value_stack.top();
                value_stack.pop();
                local_vars[identifier].setDoubleValue(t._doubleValue);

                break;
            case BC_LOADCTXIVAR:
                out << name << " @" << cur->getUInt16(bci + 1)
                    << ":" << cur->getUInt16(bci + 3);

                scope_id = cur->getUInt16(bci + 1);
                var_id = cur->getUInt16(bci + 3);
                identifier = make_pair(scope_id, var_id);
                assert(local_vars.count(identifier) > 0);
                value_stack.emplace(local_vars[identifier].getIntValue());

                break;
            case BC_STORECTXIVAR:
                out << name << " @" << cur->getUInt16(bci + 1)
                    << ":" << cur->getUInt16(bci + 3);

                scope_id = cur->getUInt16(bci + 1);
                var_id = cur->getUInt16(bci + 3);
                identifier = make_pair(scope_id, var_id);
                t = value_stack.top();
                value_stack.pop();
                local_vars[identifier].setIntValue(t._intValue);

                break;
            case BC_LOADCTXSVAR:
                out << name << " @" << cur->getUInt16(bci + 1)
                    << ":" << cur->getUInt16(bci + 3);

                scope_id = cur->getUInt16(bci + 1);
                var_id = cur->getUInt16(bci + 3);
                identifier = make_pair(scope_id, var_id);
                assert(local_vars.count(identifier) > 0);
                value_stack.emplace(local_vars[identifier].getStringValue());
                break;
            case BC_STORECTXSVAR:
                out << name << " @" << cur->getUInt16(bci + 1)
                    << ":" << cur->getUInt16(bci + 3);

                scope_id = cur->getUInt16(bci + 1);
                var_id = cur->getUInt16(bci + 3);
                identifier = make_pair(scope_id, var_id);
                t = value_stack.top();
                value_stack.pop();
                local_vars[identifier].setStringValue(t._stringValue);

                break;
            case BC_IFICMPNE:
                out << name << " " << cur->getInt16(bci + 1) + bci + length;// + 1;

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
                out << name << " " << cur->getInt16(bci + 1) + bci + length;// + 1;

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
                out << name << " " << cur->getInt16(bci + 1) + bci + length;// + 1;

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
                out << name << " " << cur->getInt16(bci + 1) + bci + length;// + 1;

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
                out << name << " " << cur->getInt16(bci + 1) + bci + length;// + 1;

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
                out << name << " " << cur->getInt16(bci + 1) + bci + length;// + 1;

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
                out << name << " " << cur->getInt16(bci + 1) + bci + length;// + 1;

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

void BytecodeCode::print_funs() {
    int it;
    BytecodeFunction* fun;
    for(it = 0, fun = (BytecodeFunction*)functionById(it); fun != 0; ++it, fun = (BytecodeFunction*)functionById(it)) {
        cerr << "function " << fun->name() << ": " << endl;
        fun->bytecode()->dump(cerr);
    }
}

Status* BytecodeCode::execute(vector<Var *> &vars) {
    print_funs();

    uint16_t top_scope_id = 0;
    for(Var* var: vars) {
        LocalVar* lvar = (LocalVar*)var;
        for(int i = 0; i < (int)var_by_scope[top_scope_id].size(); ++i) {
            LocalVar v = var_by_scope[top_scope_id][i];
            if(v.name() != lvar->name()) {
                continue;
            }
            set_var(&var_by_scope[top_scope_id][i], lvar);
            break;
        }

    }

//    call_stack.push_back(translated_function->bytecode());
    StackFrame sf(*(StackFrame*)(functionById(top_function_id)));
    call_stack.push_back(sf);
    Status* status = call(0);
    return status;
}

}
