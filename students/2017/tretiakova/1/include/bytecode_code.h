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

    BytecodeFunction translated_function;

    ScopeMap scope_map;
    map<Scope*, VarNameMap> var_map;
    vector<vector<AstVar*>> var_by_scope;
public:

    Bytecode* bytecode() {
        return translated_function.bytecode();
    }

    BytecodeFunction* get_translated_function() {
        return &translated_function;
    }

    vector<vector<AstVar*> > get_var_by_scope() {
        return var_by_scope;
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

    uint16_t add_var(Scope* scope, string name) {
        uint16_t scope_id = add_scope();
        VarNameMap smap = var_map[scope];

        if(!smap.count(name)) {
            uint16_t var_id = smap.size();
            smap.insert(name, var_id);
            var_by_scope[scope_id].push_back(var);
            return var_id;
        }
        return smap[name];
    }

    uint16_t add_var(Scope* scope, AstVar* var) {
        return add_var(scope, var->name());
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
};

}

#endif // _BYTECODE_CODE_H
