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

namespace goose {

enum class CoreIntTy : uint8_t { I8, I16, I32, I64, U8, U16, U32, U64 };
enum class CoreMut : uint8_t { Mut, Const };
enum class CoreVarKind : uint8_t { Let, Var };

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

// A pilot type. `elem` is the element or pointee type; `count` is an array's
// fixed length.
struct CoreType {
    enum Kind : uint8_t { Int, Bool, Unit, Arr, Grow, Ref, Slice } kind = Unit;
    CoreIntTy ity = CoreIntTy::I64;   // Int
    CoreMut mut = CoreMut::Mut;       // Ref, Slice
    CoreTypeId elem = -1;             // Arr, Grow, Ref, Slice
    int64_t count = 0;                // Arr
    bool operator==(const CoreType &) const = default;
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
    int file = 0;
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
    int scope = 0;
    vector<CoreStmt> stmts;
    CoreExprP value;   // Absent for a unit block.
};

// A location: a variable, a global, what a reference points to, or an element
// of a view.
struct CorePlace {
    enum Kind : uint8_t { Local, Global, Deref, Elem } kind = Local;
    int index = 0;           // Local: variable; Global: global.
    CoreExprP expr;          // Deref: an expression of reference type; Elem: the index.
    CoreViewP view;          // Elem
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

struct CoreArg {
    enum Kind : uint8_t { Val, Ref } kind = Val;
    CoreMut mut = CoreMut::Mut;   // Ref
    CoreExprP expr;               // Val
    CorePlaceP place;             // Ref
};

enum class CoreExprKind : uint8_t {
    Lit, Bool, Read, Ref, Slice, Len, Un, Bin, Cmp, And, Or, Not, Conv, Call, Push, If, Block,
    Arr, Fill,
};

// One expression. `type` is the expression's own Core type for every kind
// (the exporter and the summary pass both read it); the writer prints it only
// where the encoding carries a type. Which of the other members are meaningful
// is fixed by `kind`:
//   Lit: value, type          Bool: flag               Read: place
//   Ref: mut, place           Slice: mut, view, lo, hi, org
//   Len: view                 Un: un, a, org           Bin: bin, a, b, org
//   Cmp: cmp, a, b            And/Or: a, b             Not: a
//   Conv: conv, a, org        Call: ctx, args, org     Push: place, a
//   If: a, then, else         Block: then              Arr: elems, type
//   Fill: a, type
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
    int ctx = 0;
    CorePlaceP place;
    CoreViewP view;
    CoreBound lo, hi;
    CoreExprP a, b;
    vector<CoreArg> args;
    vector<CoreExprP> elems;
    unique_ptr<CoreBlock> then, otherwise;
    CoreOrigin org;
};

struct CorePrintArg {
    bool text = false;
    string str;          // text
    CoreExprP expr;      // !text
};

enum class CoreStmtKind : uint8_t {
    Let, Assign, AssignOp, Rebind, Expr, Append, If, While, ForRange, ForEach, Ret, Break,
    Continue, Print, Assert, Abort, Exit,
};

// One statement. Meaningful members by kind:
//   Let: var, expr          Assign: place, expr      AssignOp: bin, place, expr
//   Rebind: var, expr       Expr: expr               Append: place, view
//   If: expr, then, otherwise (optional)             While: expr, then
//   ForRange: var, expr (lo), expr2 (hi), then
//   ForEach: var, index (optional), view, byRef, then
//   Ret: expr (optional)    Print: print             Assert/Exit: expr
//   Abort: message
struct CoreStmt {
    CoreStmtKind kind = CoreStmtKind::Break;
    int var = 0;
    int index = -1;
    bool byRef = false;
    CoreBinOp bin = CoreBinOp::Add;
    CorePlaceP place;
    CoreViewP view;
    CoreExprP expr, expr2;
    unique_ptr<CoreBlock> then, otherwise;
    vector<CorePrintArg> print;
    string message;
    CoreOrigin org;
};

struct CoreRootRef {
    enum Kind : uint8_t { Local, Global, Param } kind = Local;
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
    vector<CoreTarget> reads, writes, grows, rebinds;
    bool aborts = false;
    bool outputs = false;
};

struct CoreVar {
    string name;
    CoreTypeId type = -1;
    CoreVarKind kind = CoreVarKind::Let;
    int scope = 0;
    CoreOrigin org;
};

struct CoreParam {
    int var = 0;
    bool byRef = false;
};

struct CoreImpl {
    string name;
    vector<CoreParam> params;
    vector<CoreTypeId> results;
    vector<CoreVar> vars;
    CoreBlock body;
    CoreSummary summary;
};

// One checked specialization of a source function. Execution never reads it.
struct CoreContext {
    int impl = 0;
    string declkey;
    // Root set of each reference- or slice-typed variable, by ascending variable.
    vector<pair<int, vector<CoreRootRef>>> varroots;
    vector<vector<CoreRootRef>> resultroots;
};

struct CoreGlobal {
    string name;
    CoreTypeId type = -1;
    CoreVarKind kind = CoreVarKind::Let;
    CoreExprP init;
    CoreOrigin org;
};

struct CoreModule {
    vector<string> files;
    vector<CoreType> types;
    vector<CoreGlobal> globals;
    vector<CoreImpl> impls;
    vector<CoreContext> contexts;
    int entry = 0;

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
};

}  // namespace goose
