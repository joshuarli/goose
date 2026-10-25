#pragma once

namespace goose {

struct UnitProgramSupport {
    string single, types, declarations, definitions;

    void Space(const string &text) { single += text; }

    void Type(const string &text) {
        single += text;
        types += text;
    }

    void State(const string &declaration) {
        Append(single, "static ", declaration);
        Append(declarations, "extern GS_HIDDEN ", declaration);
        Append(definitions, "GS_HIDDEN ", declaration);
    }

    void Function(const string &signature, const string &body) {
        Append(single, "static ", signature, " ", body);
        Append(declarations, "GS_HIDDEN ", signature, ";\n");
        Append(definitions, "GS_HIDDEN ", signature, " ", body);
    }

    void Forward(const string &declaration) {
        Append(single, "static ", declaration);
    }
};

}
