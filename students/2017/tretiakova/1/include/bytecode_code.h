#ifndef _BYTECODE_CODE_H
#define _BYTECODE_CODE_H

#include "../include/ast.h"
#include "../include/mathvm.h"
#include "../include/visitors.h"

#include <vector>
#include <stack>
#include <map>

namespace mathvm {

class BytecodeCode : public Code {
    typedef map<Scope*, uint16_t> ScopeMap;
    typedef map<string, uint16_t> VarNameMap;

    ScopeMap scope_map;
    map<Scope*, VarNameMap> var_map;

    BytecodeFunction translated_function;
    vector<vector<Var>> *var_by_scope;
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
            var_map.insert(scope, VarNameMap());
            var_by_scope.push_back(vector<AstVar*>());
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

    virtual
};

}

#endif // _BYTECODE_CODE_H
