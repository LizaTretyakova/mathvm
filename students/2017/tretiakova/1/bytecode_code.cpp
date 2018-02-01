#include "../include/ast.h"
#include "../include/mathvm.h"
#include "../include/visitors.h"

#include "include/bytecode_code.h"

#include <vector>
#include <stack>
#include <map>
#include <iostream>
#include <fstream>
#include <string>

namespace mathvm {

int BytecodeCode::get_scope_id(Scope* scope) {
//    cerr << "get scope id for " << scope << endl;
    if(!scope_map.count(scope)) {
        return -1;
    }
    return scope_map[scope];
}

pair<int, int> BytecodeCode::get_var_id(Scope* scope, string name) {
//    cerr << "get var id for " << name << " in " << scope << endl;
    Scope* cur = scope;
    while(cur && !var_map[cur].count(name)) {
        cur = cur->parent();
    }
    if(!cur) {
        return make_pair(-1, -1);
    }
    // (scope, var)
    int scope_id = get_scope_id(cur);
    assert(scope_id >= 0);
    return make_pair(scope_id, var_map[cur][name]);
}

int BytecodeCode::add_var(Scope* scope, VarType type, string name) {
//    cerr << "add var id for " << typeToName(type) << " " << name << " in " << scope << endl;
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

uint16_t BytecodeCode::add_scope(Scope* scope) {
//    cerr << "add scope " << scope << "{" << endl;
    if(!scope_map.count(scope)) {
        uint16_t scope_id = (uint16_t)scope_map.size();
        scope_map[scope] = scope_id;
        assert(scope_id == scopes.size());
        scopes.push_back(scope);
        var_map[scope] = VarNameMap();
        var_by_scope.push_back(vector<LocalVar>());

        for(int i = 0; i < (int)scope->childScopeNumber(); ++i) {
            add_scope(scope->childScopeAt(i));
        }

        for(Scope::VarIterator it(scope); it.hasNext();) {
            AstVar* v = it.next();
            add_var(scope, v->type(), v->name());
        }

        for(Scope::FunctionIterator fit(scope); fit.hasNext();) {
            AstFunction* f = fit.next();
            StackFrame* sf = new StackFrame(f);
            uint16_t f_id = addFunction(sf);
            if(f->name() == "<top>") {
                top_function_id = f_id;
            }
        }

//        cerr << "} id " << scope_id << endl;
        return scope_id;
    }

//    cerr << "}" << endl;
    return scope_map[scope];
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
//        cerr << "Invalid variable type" << endl;
        assert(false);
    }
}

void print_value_stack(stack<Value> s) { // sic! copy
    cerr << "Value stack [top <-- bottom]: ";
    while(s.size() > 0) {
        cerr << "("
             << s.top()._doubleValue << ", "
             << s.top()._intValue << ", "
             << s.top()._stringValue << ") ";
        s.pop();
    }
    cerr << endl;
}

Status* BytecodeCode::call(int call_id, ofstream& out) {
//    cout << call_id << endl;
//    out << endl;
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
    int frame_ptr;
    int diff;
    pair<uint16_t, uint16_t> identifier;

    LocalVar lvar;

    for (size_t bci = 0; bci < call_stack[call_id].bytecode()->length();) {
        size_t length;
        Instruction insn = call_stack[call_id].bytecode()->getInsn(bci);
//        out << bci << ": ";
        const char* name = bytecodeName(insn, &length);
        (void)name;
//        print_value_stack(value_stack);
//        cerr << name << endl;
        switch (insn) {
        case BC_DLOAD:
//            out << name << " " << call_stack[call_id].bytecode()->getDouble(bci + 1);
//            cerr << name << " " << call_stack[call_id].bytecode()->getDouble(bci + 1);

            dval = call_stack[call_id].bytecode()->getDouble(bci + 1);
            value_stack.emplace(dval);

            break;
        case BC_ILOAD:
//            out << name << " " << call_stack[call_id].bytecode()->getInt64(bci + 1);
//            cerr << name << " " << call_stack[call_id].bytecode()->getInt64(bci + 1);

            ival = call_stack[call_id].bytecode()->getInt64(bci + 1);
            value_stack.emplace(ival);

            break;
        case BC_DLOAD0:
//            cerr << name;
//            out << name;

            value_stack.emplace(0.0);

            break;
        case BC_ILOAD0:
//            cerr << name;
//            out << name;

            value_stack.emplace(0);

            break;
        case BC_DLOAD1:
//            cerr << name;
//            out << name;

            value_stack.emplace(1.0);

            break;
        case BC_ILOAD1:
//            cerr << name;
//            out << name;

            value_stack.emplace(1);

            break;
        case BC_SLOAD:
//            cerr << name << " @" << call_stack[call_id].bytecode()->getUInt16(bci + 1);
//            out << name << " @" << call_stack[call_id].bytecode()->getUInt16(bci + 1);

            sid = call_stack[call_id].bytecode()->getUInt16(bci + 1);
            value_stack.emplace(constantById(sid));

            break;
        case BC_CALL:
//    //        cerr << name << " *" << call_stack[call_id].bytecode()->getUInt16(bci + 1);
//            out << name << " *" << call_stack[call_id].bytecode()->getUInt16(bci + 1);

            fun_id = call_stack[call_id].bytecode()->getUInt16(bci + 1);
            f = (StackFrame*)functionById(fun_id);
            call_stack.push_back(*f);
            stack_size = value_stack.size();
            status = call(call_stack.size() - 1, out);
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
//    //        cerr << name << " *" << call_stack[call_id].bytecode()->getUInt16(bci + 1);
//            out << name << " *" << call_stack[call_id].bytecode()->getUInt16(bci + 1);
            break;
        case BC_LOADDVAR:
        case BC_STOREDVAR:
        case BC_LOADIVAR:
        case BC_STOREIVAR:
        case BC_LOADSVAR:
        case BC_STORESVAR:
//            cerr << name << " @" << call_stack[call_id].bytecode()->getUInt16(bci + 1);
//            out << name << " @" << call_stack[call_id].bytecode()->getUInt16(bci + 1);
            break;
        case BC_LOADCTXDVAR:
//            cerr << name << " @" << call_stack[call_id].bytecode()->getUInt16(bci + 1)
//                << ":" << call_stack[call_id].bytecode()->getUInt16(bci + 3);
//            out << name << " @" << call_stack[call_id].bytecode()->getUInt16(bci + 1)
//                << ":" << call_stack[call_id].bytecode()->getUInt16(bci + 3);

            scope_id = call_stack[call_id].bytecode()->getUInt16(bci + 1);
            var_id = call_stack[call_id].bytecode()->getUInt16(bci + 3);
            identifier = make_pair(scope_id, var_id);

            frame_ptr = lookup_frame(call_id, identifier);
            assert(frame_ptr >= 0);

            value_stack.emplace((*call_stack[frame_ptr].local_vars())[identifier].getDoubleValue());
            break;

        case BC_STORECTXDVAR:
//            cerr << name << " @" << call_stack[call_id].bytecode()->getUInt16(bci + 1)
//                << ":" << call_stack[call_id].bytecode()->getUInt16(bci + 3);
//            out << name << " @" << call_stack[call_id].bytecode()->getUInt16(bci + 1)
//                << ":" << call_stack[call_id].bytecode()->getUInt16(bci + 3);

            scope_id = call_stack[call_id].bytecode()->getUInt16(bci + 1);
            var_id = call_stack[call_id].bytecode()->getUInt16(bci + 3);
            identifier = make_pair(scope_id, var_id);

            frame_ptr = lookup_frame(call_id, identifier);
            assert(frame_ptr >= 0);

            t = value_stack.top();
            value_stack.pop();
            (*call_stack[frame_ptr].local_vars())[identifier] = var_by_scope[scope_id][var_id];
            (*call_stack[frame_ptr].local_vars())[identifier].setDoubleValue(t._doubleValue);

            break;
        case BC_LOADCTXIVAR:
//            cerr << name << " @" << call_stack[call_id].bytecode()->getUInt16(bci + 1)
//                << ":" << call_stack[call_id].bytecode()->getUInt16(bci + 3);
//            out << name << " @" << call_stack[call_id].bytecode()->getUInt16(bci + 1)
//                << ":" << call_stack[call_id].bytecode()->getUInt16(bci + 3);

            scope_id = call_stack[call_id].bytecode()->getUInt16(bci + 1);
            var_id = call_stack[call_id].bytecode()->getUInt16(bci + 3);
            identifier = make_pair(scope_id, var_id);

            frame_ptr = lookup_frame(call_id, identifier);
            assert(frame_ptr >= 0);

            value_stack.emplace((*call_stack[frame_ptr].local_vars())[identifier].getIntValue());
            break;

        case BC_STORECTXIVAR:
//            cerr << name << " @" << call_stack[call_id].bytecode()->getUInt16(bci + 1)
//                << ":" << call_stack[call_id].bytecode()->getUInt16(bci + 3);
//            out << name << " @" << call_stack[call_id].bytecode()->getUInt16(bci + 1)
//                << ":" << call_stack[call_id].bytecode()->getUInt16(bci + 3);

            scope_id = call_stack[call_id].bytecode()->getUInt16(bci + 1);
            var_id = call_stack[call_id].bytecode()->getUInt16(bci + 3);
            identifier = make_pair(scope_id, var_id);

            frame_ptr = lookup_frame(call_id, identifier);
            assert(frame_ptr >= 0);

            t = value_stack.top();
            value_stack.pop();
            (*call_stack[frame_ptr].local_vars())[identifier] = var_by_scope[scope_id][var_id];
            (*call_stack[frame_ptr].local_vars())[identifier].setIntValue(t._intValue);

//            lvar = (*call_stack[frame_ptr].local_vars())[identifier];
//            cerr << "[STORE]d CTXIVAR " << typeToName(lvar.type())
//                 << " " << lvar.name()
//                 << " " << lvar.getIntValue() << endl;
//            cerr << endl << "[STORE]d CTXIVAR " << typeToName(lvar.type())
//                 << " " << lvar.name()
//                 << " " << lvar.getIntValue()
//                 << " " << frame_ptr << endl;

            break;

        case BC_LOADCTXSVAR:
//            cerr << name << " @" << call_stack[call_id].bytecode()->getUInt16(bci + 1)
//                << ":" << call_stack[call_id].bytecode()->getUInt16(bci + 3);
//            out << name << " @" << call_stack[call_id].bytecode()->getUInt16(bci + 1)
//                << ":" << call_stack[call_id].bytecode()->getUInt16(bci + 3);

            scope_id = call_stack[call_id].bytecode()->getUInt16(bci + 1);
            var_id = call_stack[call_id].bytecode()->getUInt16(bci + 3);
            identifier = make_pair(scope_id, var_id);

            frame_ptr = lookup_frame(call_id, identifier);
            assert(frame_ptr >= 0);

            value_stack.emplace((*call_stack[frame_ptr].local_vars())[identifier].getStringValue());
            break;

        case BC_STORECTXSVAR:
//            cerr << name << " @" << call_stack[call_id].bytecode()->getUInt16(bci + 1)
//                << ":" << call_stack[call_id].bytecode()->getUInt16(bci + 3);
//            out << name << " @" << call_stack[call_id].bytecode()->getUInt16(bci + 1)
//                << ":" << call_stack[call_id].bytecode()->getUInt16(bci + 3);

            scope_id = call_stack[call_id].bytecode()->getUInt16(bci + 1);
            var_id = call_stack[call_id].bytecode()->getUInt16(bci + 3);
            identifier = make_pair(scope_id, var_id);

            frame_ptr = lookup_frame(call_id, identifier);
            assert(frame_ptr >= 0);

            t = value_stack.top();
            value_stack.pop();

            (*call_stack[frame_ptr].local_vars())[identifier] = var_by_scope[scope_id][var_id];
            (*call_stack[frame_ptr].local_vars())[identifier].setStringValue(t._stringValue);
            break;

        case BC_IFICMPNE:
//            cerr << name << " " << call_stack[call_id].bytecode()->getInt16(bci + 1) + bci + length;// + 1;
//            out << name << " " << call_stack[call_id].bytecode()->getInt16(bci + 1) + bci + length;// + 1;

            t = value_stack.top();
            value_stack.pop();
            b = value_stack.top();
            value_stack.pop();
            offset = call_stack[call_id].bytecode()->getInt16(bci + 1);
            if(t._intValue != b._intValue) {
                bci += offset;
            }

            break;
        case BC_IFICMPE:
//            cerr << name << " " << call_stack[call_id].bytecode()->getInt16(bci + 1) + bci + length;// + 1;
//            out << name << " " << call_stack[call_id].bytecode()->getInt16(bci + 1) + bci + length;// + 1;

            t = value_stack.top();
            value_stack.pop();
            b = value_stack.top();
            value_stack.pop();
            offset = call_stack[call_id].bytecode()->getInt16(bci + 1);
            if(t._intValue == b._intValue) {
                bci += offset;
            }

            break;
        case BC_IFICMPG:
//            cerr << name << " " << call_stack[call_id].bytecode()->getInt16(bci + 1) + bci + length;// + 1;
//            out << name << " " << call_stack[call_id].bytecode()->getInt16(bci + 1) + bci + length;// + 1;

            t = value_stack.top();
            value_stack.pop();
            b = value_stack.top();
            value_stack.pop();
            offset = call_stack[call_id].bytecode()->getInt16(bci + 1);
            if(t._intValue > b._intValue) {
                bci += offset;
            }

            break;
        case BC_IFICMPGE:
//            cerr << name << " " << call_stack[call_id].bytecode()->getInt16(bci + 1) + bci + length;// + 1;
//            out << name << " " << call_stack[call_id].bytecode()->getInt16(bci + 1) + bci + length;// + 1;

            t = value_stack.top();
            value_stack.pop();
            b = value_stack.top();
            value_stack.pop();
            offset = call_stack[call_id].bytecode()->getInt16(bci + 1);
            if(t._intValue >= b._intValue) {
                bci += offset;
            }

            break;
        case BC_IFICMPL:
//            cerr << name << " " << call_stack[call_id].bytecode()->getInt16(bci + 1) + bci + length;// + 1;
//            out << name << " " << call_stack[call_id].bytecode()->getInt16(bci + 1) + bci + length;// + 1;

            t = value_stack.top();
            value_stack.pop();
            b = value_stack.top();
            value_stack.pop();
            offset = call_stack[call_id].bytecode()->getInt16(bci + 1);
            if(t._intValue < b._intValue) {
                bci += offset;
            }

            break;
        case BC_IFICMPLE:
//            cerr << name << " " << call_stack[call_id].bytecode()->getInt16(bci + 1) + bci + length;// + 1;
//            out << name << " " << call_stack[call_id].bytecode()->getInt16(bci + 1) + bci + length;// + 1;

            t = value_stack.top();
            value_stack.pop();
            b = value_stack.top();
            value_stack.pop();
            offset = call_stack[call_id].bytecode()->getInt16(bci + 1);
            if(t._intValue <= b._intValue) {
                bci += offset;
            }

            break;
        case BC_JA:
//            cerr << name << " " << call_stack[call_id].bytecode()->getInt16(bci + 1) + bci + length;// + 1;
//            out << name << " " << call_stack[call_id].bytecode()->getInt16(bci + 1) + bci + length;// + 1;

            offset = call_stack[call_id].bytecode()->getInt16(bci + 1);
            bci += offset;

            break;
        case BC_RETURN:
//            cerr << name;
//            out << name;
            return Status::Ok();

        case BC_DADD:
//            cerr << name;
//            out << name;

            t = value_stack.top();
            value_stack.pop();
            b = value_stack.top();
            value_stack.pop();
            value_stack.emplace(t._doubleValue + b._doubleValue);
            break;

        case BC_IADD:
//            cerr << name;
//            out << name;

            t = value_stack.top();
            value_stack.pop();
            b = value_stack.top();
            value_stack.pop();
            value_stack.emplace(t._intValue + b._intValue);
            break;

        case BC_DCMP:
//            cerr << name;
//            out << name;

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
//            cerr << name;
//            out << name;

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
//            cerr << name;
//            out << name;

            t = value_stack.top();
            value_stack.pop();
            b = value_stack.top();
            value_stack.pop();
            value_stack.emplace(t._doubleValue / b._doubleValue);
            break;

        case BC_IDIV:
//            cerr << name;
//            out << name;

            t = value_stack.top();
            value_stack.pop();
            b = value_stack.top();
            value_stack.pop();
            value_stack.emplace(t._intValue / b._intValue);
            break;

        case BC_DMUL:
//            cerr << name;
//            out << name;

            t = value_stack.top();
            value_stack.pop();
            b = value_stack.top();
            value_stack.pop();
            value_stack.emplace(t._doubleValue * b._doubleValue);
            break;

        case BC_IMUL:
//            cerr << name;
//            out << name;

            t = value_stack.top();
            value_stack.pop();
            b = value_stack.top();
            value_stack.pop();
            value_stack.emplace(t._intValue * b._intValue);
            break;

        case BC_DNEG:
//            cerr << name;
//            out << name;

            t = value_stack.top();
            value_stack.pop();
            value_stack.emplace(-t._doubleValue);
            break;

        case BC_INEG:
//            cerr << name;
//            out << name;

            t = value_stack.top();
            value_stack.pop();
            value_stack.emplace(-t._intValue);
            break;

        case BC_DPRINT:
//            cerr << name;
//            out << name;

            t = value_stack.top();
            value_stack.pop();
            cout << t._doubleValue;
            break;

        case BC_IPRINT:
//            cerr << name;
//            out << name;

            t = value_stack.top();
            value_stack.pop();
            cout << t._intValue;
            break;

        case BC_SPRINT:
//            cerr << name;
//            out << name;

            t = value_stack.top();
            value_stack.pop();
            cout << t._stringValue;
            break;

        case BC_DSUB:
//            cerr << name;
//            out << name;

            t = value_stack.top();
            value_stack.pop();
            b = value_stack.top();
            value_stack.pop();
            value_stack.emplace(t._doubleValue - b._doubleValue);
            break;

        case BC_ISUB:
//            cerr << name;
//            out << name;

            t = value_stack.top();
            value_stack.pop();
            b = value_stack.top();
            value_stack.pop();
            value_stack.emplace(t._intValue - b._intValue);
            break;

        case BC_IMOD:
//            cerr << name;
//            out << name;

            t = value_stack.top();
            value_stack.pop();
            b = value_stack.top();
            value_stack.pop();
            value_stack.emplace(t._intValue % b._intValue);
            break;

        case BC_IAAND:
//            cerr << name;
//            out << name;

            t = value_stack.top();
            value_stack.pop();
            b = value_stack.top();
            value_stack.pop();
            value_stack.emplace(t._intValue & b._intValue);
            break;

        case BC_IAOR:
//            cerr << name;
//            out << name;

            t = value_stack.top();
            value_stack.pop();
            b = value_stack.top();
            value_stack.pop();
            value_stack.emplace(t._intValue | b._intValue);
            break;

        case BC_IAXOR:
//            cerr << name;
//            out << name;

            t = value_stack.top();
            value_stack.pop();
            b = value_stack.top();
            value_stack.pop();
            value_stack.emplace(t._intValue ^ b._intValue);
            break;

        case BC_DUMP:
//            cerr << "--- idle";
//            out << "--- idle";
            break;

        case BC_I2D:
//            cerr << name;
//            out << name;
            t = value_stack.top();
            value_stack.pop();
            value_stack.emplace((double)t._intValue);
            break;

        case BC_D2I:
//            cerr << name;
//            out << name;
            t = value_stack.top();
            value_stack.pop();
            value_stack.emplace((int)t._doubleValue);
            break;

        case BC_S2I:
//            cerr << name;
//            out << name;
            t = value_stack.top();
            value_stack.pop();
            value_stack.emplace(stoi(t._stringValue));
            break;

        case BC_POP:
//            cerr << name;
//            out << name;
            value_stack.pop();
            break;

        default:
//            cerr << name;
//            out << name;
            break;
        }
//        cerr << endl;
//        out << endl;
        bci += length;
    }
    return Status::Ok();
}

void BytecodeCode::print_funs(ofstream& out) {
    int it;
    BytecodeFunction* fun;
    for(it = 0, fun = (BytecodeFunction*)functionById(it); fun != 0; ++it, fun = (BytecodeFunction*)functionById(it)) {
        out << "function " << fun->name() << ": " << endl;
        fun->bytecode()->dump(out);
    }
}

Status* BytecodeCode::execute(vector<Var *> &vars) {
    ofstream out("debug.output");
    print_funs(out);

    uint16_t top_scope_id = 1; // sic!
    StackFrame sf(*(StackFrame*)(functionById(top_function_id)));
    map<pair<uint16_t, uint16_t>, LocalVar>* global_vars = sf.local_vars();
    for(Var* var: vars) {
        LocalVar lvar = *(LocalVar*)var;
        pair<int, int> var_id = get_var_id(scopes[top_scope_id], lvar.name());
        if(var_id.first != -1 && var_id.second != -1) {
            (*global_vars)[var_id] = lvar;
        }
    }
    call_stack.push_back(sf);
    Status* status = call(0, out);
    return status;
}

}
