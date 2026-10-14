// Goose compiler — Typed Goose Core, the in-memory module.
//
// Core is the source-side meaning of a checked program after resolution and
// specialization: evaluation order, value versus place, scopes, the root
// annotations of each checked context and the effect summaries are all
// explicit. This header is only the data model; building it from the checked
// program is core_export.h, the effect summaries are core_summary.h, and the
// serialization is core_json.h. Nothing here refers back to the AST.
//
// Identifiers are dense indices. Types and origins are interned while the
// module is built, in whatever order the builder meets them; the writer
// renumbers them by first mention in the document, so the numbers in memory
// carry no meaning.
#pragma once

#include <optional>

namespace goose {

enum class CoreIntTy : uint8_t { I8, I16, I32, I64, U8, U16, U32, U64 };
enum class CoreMut : uint8_t { Mut, Const };
enum class CoreVarKind : uint8_t { Let, Var };
enum class CoreProfile : uint8_t { Pilot, Shrink, Construction };
enum class CoreRequest : uint8_t { Register, Value, ElementRun };

inline const char *CoreRequestName(CoreRequest request) {
    static const char *names[] = { "register", "value", "element_run" };
    return names[(int)request];
}

inline const char *CoreProfileName(CoreProfile profile) {
    static const char *names[] = { "core-pilot", "core-shrink", "core-construction" };
    return names[(int)profile];
}

inline bool CoreHasShrink(CoreProfile profile) {
    return profile == CoreProfile::Shrink || profile == CoreProfile::Construction;
}
inline bool CoreHasConstruction(CoreProfile profile) { return profile == CoreProfile::Construction; }
inline CoreProfile CoreWithShrink(CoreProfile profile) {
    return profile == CoreProfile::Pilot ? CoreProfile::Shrink : profile;
}

inline const char *CoreIntName(CoreIntTy t) {
    static const char *names[] = { "i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64" };
    return names[(int)t];
}
inline const char *CoreMutName(CoreMut m) { return m == CoreMut::Mut ? "mut" : "const"; }
inline bool CoreIsUnsigned(CoreIntTy t) { return t >= CoreIntTy::U8; }
inline int CoreIntBits(CoreIntTy t) {
    switch (t) {
        case CoreIntTy::I8: case CoreIntTy::U8: return 8;
        case CoreIntTy::I16: case CoreIntTy::U16: return 16;
        case CoreIntTy::I32: case CoreIntTy::U32: return 32;
        default: return 64;
    }
}

using CoreTypeId = int;
using CoreFileId = int;
using CoreOriginId = int;
using CoreScopeId = int;
using CoreStructId = int;
using CoreVarId = int;
using CoreGlobalId = int;
using CoreContextId = int;
using CoreImplId = int;
using CoreResultId = int;
using CoreTargetId = int;

struct CoreType {
    enum Kind : uint8_t { Int, Bool, Unit, Arr, VarArr, Grow, GrowShrink, Limited, Ref, Slice, View, Ptr,
                          Tuple, Struct, Dest, Built, Cancelled } kind = Unit;
    CoreIntTy ity = CoreIntTy::I64;
    CoreMut mut = CoreMut::Mut;
    CoreTypeId elem = -1;
    vector<CoreTypeId> parts;
    int64_t count = 0;
    CoreStructId structid = -1;
    CoreRequest request = CoreRequest::Value;
    bool operator==(const CoreType &) const = default;
};

// Layout and permissions for one real field of a nominal flat fixed struct.
// Pads have byte offsets but never become fields here.
struct CoreField {
    CoreTypeId type = -1;
    CoreVarKind binding = CoreVarKind::Let;
    CoreMut contents = CoreMut::Mut;
    int64_t offset = 0;
};

struct CoreStruct {
    int64_t size = 0;
    vector<CoreField> fields;
};

enum class CoreOriginKind : uint8_t {
    Global, Param, Let, Assign, AssignOp, Rebind, Expr, If, While, For, Return, Break,
    Continue, Print, Assert, Abort, Exit, Call, Index, Slice, Binary, Unary, Cast,
};

inline const char *CoreOriginKindName(CoreOriginKind k) {
    static const char *names[] = { "global", "param", "let", "assign", "assign_op", "rebind",
                                   "expr", "if", "while", "for", "return", "break", "continue",
                                   "print", "assert", "abort", "exit", "call", "index", "slice",
                                   "binary", "unary", "cast" };
    return names[(int)k];
}

// Where an operation came from: an index into CoreModule::files, a line from
// 1, and the kind of source construct.
struct CoreOrigin {
    CoreFileId file = 0;
    int line = 0;
    CoreOriginKind kind = CoreOriginKind::Expr;
    bool operator==(const CoreOrigin &) const = default;
};

enum class CoreUnOp : uint8_t { Neg, BitNot };
enum class CoreBinOp : uint8_t { Add, Sub, Mul, Div, Mod, BitAnd, BitOr, BitXor, Shl, Shr };
enum class CoreCmpOp : uint8_t { Eq, Ne, Lt, Le, Gt, Ge };
enum class CoreConvKind : uint8_t { Widen, As, AsUnchecked };

inline const char *CoreUnOpName(CoreUnOp o) {
    static const char *names[] = { "neg", "bitnot" };
    return names[(int)o];
}
inline const char *CoreBinOpName(CoreBinOp o) {
    static const char *names[] = { "add", "sub", "mul", "div", "mod", "bitand", "bitor",
                                   "bitxor", "shl", "shr" };
    return names[(int)o];
}
inline const char *CoreCmpOpName(CoreCmpOp o) {
    static const char *names[] = { "eq", "ne", "lt", "le", "gt", "ge" };
    return names[(int)o];
}
inline const char *CoreConvKindName(CoreConvKind o) {
    static const char *names[] = { "widen", "as", "as_unchecked" };
    return names[(int)o];
}

struct CoreExpr;
struct CorePlace;
struct CoreView;
struct CoreStmt;
using CoreExprP = unique_ptr<CoreExpr>;
using CorePlaceP = unique_ptr<CorePlace>;
using CoreViewP = unique_ptr<CoreView>;

// A scope. Variables are declared by a `let` or a loop statement inside it.
struct CoreBlock {
    CoreScopeId scope = 0;
    vector<CoreStmt> stmts;
    CoreExprP value;   // Absent for a unit block.
};

// A location: a variable, a global, what a reference points to, or an element
// of a view.
struct CorePlace {
    enum Kind : uint8_t { Local, Global, Deref, Elem, Field } kind = Local;
    int index = 0;           // Local: variable; Global: global.
    CoreExprP expr;          // Deref: an expression of reference type; Elem: the index.
    CoreViewP view;          // Elem
    CorePlaceP base;          // Field: containing storage.
    CoreOrigin org;          // Elem
};

// A sampled run of elements: the array a place holds, with its length taken
// now, or the run a slice value stands for.
struct CoreView {
    enum Kind : uint8_t { Of, Val } kind = Of;
    CorePlaceP place;        // Of
    CoreExprP expr;          // Val
};

struct CoreBound {
    enum Kind : uint8_t { None, Expr, End } kind = None;
    CoreExprP expr;
};

struct CoreArgValue { CoreExprP expr; };
struct CoreArgConstruct { CoreExprP expr; };
struct CoreArgReference { CoreMut mut = CoreMut::Mut; CorePlaceP place; };
using CoreArg = variant<CoreArgValue, CoreArgConstruct, CoreArgReference>;

enum class CoreExprKind : uint8_t {
    Lit, Bool, Read, Ref, Slice, Len, Un, Bin, Cmp, And, Or, Not, Conv, Call, Push, Pop, If, Block,
    Arr, Fill, Struct, Bytes, String, Copy, ResultLocal, Values,
};

struct CorePrintArg;

struct CoreExpr {
    CoreExprKind kind = CoreExprKind::Bool;
    CoreTypeId type = -1;
    string value;
    bool flag = false;
    CoreMut mut = CoreMut::Mut;
    CoreUnOp un = CoreUnOp::Neg;
    CoreBinOp bin = CoreBinOp::Add;
    CoreCmpOp cmp = CoreCmpOp::Eq;
    CoreConvKind conv = CoreConvKind::Widen;
    CoreContextId ctx = 0;
    CoreVarId var = -1;
    CorePlaceP place;
    CoreViewP view;
    CoreBound lo, hi;
    CoreExprP a, b;
    vector<CoreArg> args;
    vector<CoreExprP> elems;
    vector<CoreExprP> values;
    vector<CorePrintArg> print;
    vector<uint8_t> bytes;
    unique_ptr<CoreBlock> then, otherwise;
    CoreOrigin org;
};

struct CorePrintArg {
    enum Kind : uint8_t { Text, Expr, View } kind = Text;
    string str;
    CoreExprP expr;
    CoreViewP view;
};

enum class CoreStmtKind : uint8_t {
    Let, Assign, AssignOp, AssignWhole, Rebind, Expr, Append, PopN, Resize, Clear, If, While, ForRange, ForEach, Ret, Break,
    Continue, Print, Assert, Abort, Exit, Receive, AppendValue, AppendConstruct, RetValues, RetForward,
    ReturnFrom, ReturnFromForward, BreakValue,
};

struct CoreStmt {
    CoreStmtKind kind = CoreStmtKind::Break;
    int var = 0;
    int index = -1;
    CoreTargetId target = -1;
    bool byRef = false;
    CoreBinOp bin = CoreBinOp::Add;
    CorePlaceP place;
    CoreViewP view;
    CoreExprP expr, expr2;
    vector<CoreVarId> vars;
    vector<CoreExprP> values;
    unique_ptr<CoreBlock> then, otherwise;
    vector<CorePrintArg> print;
    string message;
    CoreOrigin org;
};

struct CoreRootRef {
    enum Kind : uint8_t { Static, Local, Global, Param } kind = Local;
    int index = 0;
    auto operator<=>(const CoreRootRef &) const = default;
};

// An effect target: a parameter or a global.
struct CoreTarget {
    bool global = false;
    int index = 0;
    auto operator<=>(const CoreTarget &o) const {
        // Parameters sort before globals.
        if (global != o.global) return global ? strong_ordering::greater : strong_ordering::less;
        return index <=> o.index;
    }
    bool operator==(const CoreTarget &) const = default;
};

// What an implementation may do, over its parameters and the globals. Unknown
// implies every effect.
struct CoreSummary {
    bool unknown = false;
    vector<CoreTarget> reads, writes, grows, shrinks, rebinds;
    vector<CoreResultId> constructs;
    vector<CoreTargetId> needs, escapes;
    bool aborts = false;
    bool outputs = false;
};

struct CoreVar {
    string name;
    CoreTypeId type = -1;
    CoreVarKind kind = CoreVarKind::Let;
    CoreScopeId scope = 0;
    CoreOrigin org;
};

struct CoreParam {
    int var = 0;
    bool byRef = false;
};

struct CoreResultDescriptor {
    CoreTypeId type = -1;
    CoreRequest request = CoreRequest::Register;
    optional<CoreVarId> namedLocal;
};

struct CoreImpl {
    string name;
    vector<CoreParam> params;
    vector<CoreResultDescriptor> results;
    vector<CoreVar> vars;
    CoreBlock body;
    CoreSummary summary;
};

struct CoreTargetSet {
    vector<CoreImplId> members;
};

// One checked specialization of a source function. Execution never reads it.
struct CoreContext {
    CoreImplId impl = 0;
    string declkey;
    // The stable identity of the checked context and the module of its
    // declaration, for naming what is emitted from it. Not part of the wire format.
    string stablekey, module;
    // Root set of each reference- or slice-typed variable, by ascending variable.
    vector<pair<CoreVarId, vector<CoreRootRef>>> varroots;
    vector<vector<CoreRootRef>> resultroots;
    // The content roots of the variables whose type is a reference to a slice,
    // aligned with `varroots`: what the slice the variable refers to may be
    // rooted at, named as this implementation names it. `hascontent` is 1 for
    // those variables and 0 for the rest.
    vector<vector<CoreRootRef>> content;
    vector<char> hascontent;
};

struct CoreGlobal {
    string name;
    CoreTypeId type = -1;
    CoreVarKind kind = CoreVarKind::Let;
    CoreExprP init;
    CoreOrigin org;
    string module;   // As for a context.
};

struct CoreModule {
    vector<string> files;
    // The path of each file as the compiler writes it in a runtime diagnostic,
    // aligned with `files`. Not part of the wire format.
    vector<string> diagfiles;
    vector<string> filemodules;   // The module of each file, aligned with `files`.
    vector<CoreType> types;
    CoreProfile profile = CoreProfile::Pilot;
    vector<CoreStruct> structs;
    vector<CoreTargetSet> targets;
    vector<CoreGlobal> globals;
    vector<CoreImpl> impls;
    vector<CoreContext> contexts;
    CoreContextId entry = 0;

    CoreTypeId Intern(const CoreType &t) {
        for (size_t i = 0; i < types.size(); i++)
            if (types[i] == t) return (CoreTypeId)i;
        types.push_back(t);
        return (CoreTypeId)types.size() - 1;
    }
    CoreTypeId IntType(CoreIntTy t) {
        CoreType ty; ty.kind = CoreType::Int; ty.ity = t;
        return Intern(ty);
    }
    CoreTypeId BoolType() { CoreType ty; ty.kind = CoreType::Bool; return Intern(ty); }
    CoreTypeId UnitType() { CoreType ty; ty.kind = CoreType::Unit; return Intern(ty); }
    const CoreType &Type(CoreTypeId id) const { return types[id]; }
    bool IsRefOrSlice(CoreTypeId id) const {
        return types[id].kind == CoreType::Ref || types[id].kind == CoreType::Slice;
    }

    // Resolve a place's type from its owning implementation and module tables.
    // Operation classification uses this instead of carrying a second type fact
    // beside the place that could disagree with it.
    optional<CoreTypeId> PlaceType(int impl, const CorePlace &place) const {
        switch (place.kind) {
            case CorePlace::Local:
                if (impl < 0 || impl >= (int)impls.size() || place.index < 0 ||
                    place.index >= (int)impls[impl].vars.size()) return {};
                return impls[impl].vars[place.index].type;
            case CorePlace::Global:
                if (place.index < 0 || place.index >= (int)globals.size()) return {};
                return globals[place.index].type;
            case CorePlace::Deref: {
                if (!place.expr || place.expr->type < 0 || place.expr->type >= (int)types.size()) return {};
                auto &ref = Type(place.expr->type);
                if (ref.kind != CoreType::Ref) return {};
                return ref.elem;
            }
            case CorePlace::Elem: {
                if (!place.view) return {};
                optional<CoreTypeId> owner;
                if (place.view->kind == CoreView::Of) {
                    if (!place.view->place) return {};
                    owner = PlaceType(impl, *place.view->place);
                } else if (place.view->expr && place.view->expr->type >= 0 &&
                           place.view->expr->type < (int)types.size()) {
                    auto &view = Type(place.view->expr->type);
                    if (view.kind == CoreType::Slice || view.kind == CoreType::View) return view.elem;
                    return {};
                }
                if (!owner || *owner < 0 || *owner >= (int)types.size()) return {};
                auto &array = Type(*owner);
                if (array.kind != CoreType::Arr && array.kind != CoreType::VarArr && array.kind != CoreType::Grow &&
                    array.kind != CoreType::GrowShrink && array.kind != CoreType::Limited) return {};
                return array.elem;
            }
            case CorePlace::Field: {
                if (!place.base || place.index < 0) return {};
                auto base = PlaceType(impl, *place.base);
                if (!base || *base < 0 || *base >= (int)types.size()) return {};
                auto type = *base;
                if (Type(type).kind == CoreType::Ref) type = Type(type).elem;
                if (type < 0 || type >= (int)types.size() || Type(type).kind != CoreType::Struct) return {};
                auto structid = Type(type).structid;
                if (structid < 0 || structid >= (int)structs.size() ||
                    place.index >= (int)structs[structid].fields.size()) return {};
                return structs[structid].fields[place.index].type;
            }
        }
        return {};
    }
};

// Calls f on every expression of a block, outer before inner, in evaluation
// order: those nested in places, views, bounds, arguments and arms included.
inline void CoreVisitExprs(const CoreBlock &b, const function<void(const CoreExpr &)> &f);

inline void CoreVisitExprs(const CoreExpr &e, const function<void(const CoreExpr &)> &f);

inline void CoreVisitExprs(const CorePlace &p, const function<void(const CoreExpr &)> &f) {
    if (p.kind == CorePlace::Deref) CoreVisitExprs(*p.expr, f);
    if (p.kind == CorePlace::Elem) {
        if (p.view->kind == CoreView::Of) CoreVisitExprs(*p.view->place, f);
        else CoreVisitExprs(*p.view->expr, f);
        CoreVisitExprs(*p.expr, f);
    }
    if (p.kind == CorePlace::Field) CoreVisitExprs(*p.base, f);
}

inline void CoreVisitExprs(const CoreView &v, const function<void(const CoreExpr &)> &f) {
    if (v.kind == CoreView::Of) CoreVisitExprs(*v.place, f);
    else CoreVisitExprs(*v.expr, f);
}

inline void CoreVisitExprs(const CoreExpr &e, const function<void(const CoreExpr &)> &f) {
    f(e);
    if (e.place) CoreVisitExprs(*e.place, f);
    if (e.view) CoreVisitExprs(*e.view, f);
    if (e.lo.expr) CoreVisitExprs(*e.lo.expr, f);
    if (e.hi.expr) CoreVisitExprs(*e.hi.expr, f);
    if (e.a) CoreVisitExprs(*e.a, f);
    if (e.b) CoreVisitExprs(*e.b, f);
    for (auto &a : e.args) visit([&](auto &arg) {
        using Arg = decay_t<decltype(arg)>;
        if constexpr (is_same_v<Arg, CoreArgValue> || is_same_v<Arg, CoreArgConstruct>) {
            if (arg.expr) CoreVisitExprs(*arg.expr, f);
        } else if (arg.place) CoreVisitExprs(*arg.place, f);
    }, a);
    for (auto &el : e.elems) CoreVisitExprs(*el, f);
    for (auto &value : e.values) CoreVisitExprs(*value, f);
    for (auto &part : e.print) {
        if (part.kind == CorePrintArg::Expr && part.expr) CoreVisitExprs(*part.expr, f);
        if (part.kind == CorePrintArg::View && part.view) CoreVisitExprs(*part.view, f);
    }
    if (e.then) CoreVisitExprs(*e.then, f);
    if (e.otherwise) CoreVisitExprs(*e.otherwise, f);
}

inline void CoreVisitExprs(const CoreBlock &b, const function<void(const CoreExpr &)> &f) {
    for (auto &s : b.stmts) {
        if (s.place) CoreVisitExprs(*s.place, f);
        if (s.view) CoreVisitExprs(*s.view, f);
        if (s.expr) CoreVisitExprs(*s.expr, f);
        if (s.expr2) CoreVisitExprs(*s.expr2, f);
        for (auto &a : s.print) {
            if (a.kind == CorePrintArg::Expr) CoreVisitExprs(*a.expr, f);
            if (a.kind == CorePrintArg::View) CoreVisitExprs(*a.view, f);
        }
        for (auto &value : s.values) CoreVisitExprs(*value, f);
        if (s.then) CoreVisitExprs(*s.then, f);
        if (s.otherwise) CoreVisitExprs(*s.otherwise, f);
    }
    if (b.value) CoreVisitExprs(*b.value, f);
}

}  // namespace goose
