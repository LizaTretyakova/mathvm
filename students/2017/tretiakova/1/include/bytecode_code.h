#ifndef _BYTECODE_CODE_H
#define _BYTECODE_CODE_H

#include "../include/ast.h"
#include "../include/mathvm.h"
#include "../include/visitors.h"

#include <vector>
#include <stack>
#include <map>

namespace mathvm {

union Value {
    double _doubleValue;
    int64_t _intValue;
    const char* _stringValue;

    Value() = default;
    Value(double d): _doubleValue(d) {}
    Value(int64_t i): _intValue(i) {}
    Value(int i): _intValue((uint64_t)i) {}
    Value(const char* s): _stringValue(s) {}
    Value(string s): _stringValue(s.c_str()) {}
};

class BytecodeCode : public Code {
    typedef map<Scope*, uint16_t> ScopeMap;
    typedef map<string, uint16_t> VarNameMap;

    ScopeMap scope_map;
    vector<Scope*> scopes;
    map<Scope*, VarNameMap> var_map;

    BytecodeFunction* translated_function = NULL;
    vector<vector<Var>> *var_by_scope = NULL;

    vector<uint16_t> scope_stack;
    stack<Value> value_stack;
    vector<Bytecode*> call_stack;
public:

    BytecodeCode() {
        translated_function = NULL;
        var_by_scope = new vector<vector<Var>>();
    }

//    BytecodeCode(BytecodeFunction* bf, vector<vector<Var>> *v_ptr):
//        BytecodeCode() {
//        translated_function = bf;
//        var_by_scope = v_ptr;
//    }

    BytecodeFunction* get_translated_function() {
        return translated_function;
    }

    void set_translated_function(BytecodeFunction* bf);
    vector<vector<Var> > get_var_by_scope();
    uint16_t add_scope(Scope* scope);
    uint16_t add_var(Scope* scope, VarType type, string name);
    uint16_t add_var(Scope* scope, AstVar* var);
    /***/

    void set_var(Var* to, Var* from);
    Status* call(int call_id);
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
