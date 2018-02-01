#ifndef _BYTECODE_CODE_H
#define _BYTECODE_CODE_H

#include "../include/ast.h"
#include "../include/mathvm.h"
#include "../include/visitors.h"

#include <vector>
#include <stack>
#include <map>

namespace mathvm {

struct Value {
    double _doubleValue;
    int64_t _intValue;
    string _stringValue = "";

    Value() = default;
    Value(double d): _doubleValue(d) {}
    Value(int64_t i): _intValue(i) {}
    Value(int i): _intValue((uint64_t)i) {}
    Value(string s): _stringValue(s) {}
};

class LocalVar : public Var {
    string stringValue;
public:
    LocalVar(VarType type = VT_INT, const string& name = ""):
        Var(type, name) {}

    void setStringValue(string s) {
        stringValue = s;
    }

    string getStringValue() const {
        return stringValue;
    }
};

const pair<int, int> EMPTY(-1, -1);

class StackFrame : public BytecodeFunction {
    map<pair<uint16_t, uint16_t>, LocalVar> vars;
public:
    StackFrame(const BytecodeFunction& bf): BytecodeFunction(bf) {}
    StackFrame(AstFunction* f): BytecodeFunction(f) {}

    map<pair<uint16_t, uint16_t>, LocalVar>* local_vars() {
        return &vars;
    }

    pair<int, int> lookup_local_var(AstVar* var) {
        for(auto const& entry: vars) {
            if(entry.second.name() == var->name()
                    && entry.second.type() == var->type()) {
                return entry.first;
            }
        }
        return EMPTY;
    }

    void define_local_var(pair<uint16_t, uint16_t> identifier) {
        vars[identifier];
    }
};

class BytecodeCode : public Code {
    typedef map<Scope*, uint16_t> ScopeMap;
    typedef map<string, uint16_t> VarNameMap;

    ScopeMap scope_map;
    vector<Scope*> scopes;
    map<Scope*, VarNameMap> var_map;

    vector<vector<LocalVar>> var_by_scope;

    vector<uint16_t> scope_stack;
    stack<Value> value_stack;
    vector<StackFrame> call_stack;

    uint16_t top_function_id = 0;

    void print_funs(ofstream& out);
public:

    uint16_t add_scope(Scope* scope);
    int add_var(Scope* scope, VarType type, string name);
    int get_scope_id(Scope* scope);
    pair<int, int> get_var_id(Scope* scope, string name);
    /***/

    void set_top_function_id(uint16_t id) {
        top_function_id = id;
    }

    int lookup_frame(int call_id, pair<uint16_t, uint16_t> identifier) {
        int frame_ptr = call_id;
        while(frame_ptr >= 0 && !call_stack[frame_ptr].local_vars()->count(identifier)) {
            cerr << "frame_ptr " << frame_ptr
                 << " stack scope id " << call_stack[frame_ptr].scopeId()
                 << " target scope id " << identifier.first
                 << " target var id " << identifier.second
                 << " map size " << call_stack[frame_ptr].local_vars()->size() << endl;
            --frame_ptr;
        }
        return frame_ptr;
    }

    void set_var(LocalVar* to, LocalVar* from);
    Status* call(int call_id, ofstream& out);
    virtual Status* execute(vector<Var *> &vars);
    /*
     *  BC_CALL
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
