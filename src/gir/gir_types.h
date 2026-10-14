// Goose compiler — GIR-H, the type of the value each instruction defines.
//
// The lowering uses this to give joins and block parameters their types and
// the verifier uses it to check operands, so the two cannot disagree about
// what an instruction yields. Mutability is not checked here: an instruction
// that needs a mutable reference accepts either, and the storage check
// rejects a read-only one.
#pragma once

namespace goose {

inline bool GirOwnerKind(CoreType::Kind kind) {
    return kind == CoreType::Grow || kind == CoreType::GrowShrink || kind == CoreType::Limited;
}

inline bool GirResizableKind(CoreType::Kind kind) {
    return kind == CoreType::Grow || kind == CoreType::GrowShrink;
}

inline bool GirWholeOwnerBorrowUsesContents(CoreType::Kind kind) {
    return kind == CoreType::Grow || kind == CoreType::GrowShrink;
}

// What typing an instruction may consult.
struct GirTyEnv {
    GirModule &m;
    const vector<GirSlot> &slots;
    // Parameter and result types of each function.
    const vector<pair<vector<GirTypeId>, vector<GirTypeId>>> &sigs;
    // The type of every value so far by id, -1 where none is known.
    const vector<GirTypeId> &vals;
    // The frame of a low function, when typing one.
    const vector<GirMember> *members = nullptr;
    const vector<GirBlock> *blocks = nullptr;
};

// A type error or the type.
struct GirTyResult {
    GirTypeId ty = -1;
    string error;
    bool ok() const { return error.empty(); }
};

inline GirTyResult GirTyOk(GirTypeId t) { return { t, {} }; }
inline GirTyResult GirTyErr(string msg) { return { -1, std::move(msg) }; }

// Flat fixed: integers, booleans, fixed arrays and nominal structs of them.
inline bool GirFlat(const GirModule &m, GirTypeId t, vector<char> &open) {
    if (t < 0 || t >= (int)m.types.size() || open[t]) return false;
    auto &c = m.Type(t);
    if (c.kind == CoreType::Int || c.kind == CoreType::Bool) return true;
    if (c.kind != CoreType::Arr && c.kind != CoreType::Struct) return false;
    open[t] = 1;
    bool flat;
    if (c.kind == CoreType::Arr) {
        flat = GirFlat(m, c.elem, open);
    } else if (c.structid < 0 || c.structid >= (int)m.structs.size()) {
        flat = false;
    } else {
        flat = true;
        for (auto &field : m.structs[c.structid].fields)
            flat = GirFlat(m, field.type, open) && flat;
    }
    open[t] = 0;
    return flat;
}

inline bool GirFlat(const GirModule &m, GirTypeId t) {
    vector<char> open(m.types.size(), 0);
    return GirFlat(m, t, open);
}

inline bool GirVariableElement(const GirModule &m, GirTypeId type) {
    if (type < 0 || type >= (int)m.types.size()) return false;
    auto &t = m.Type(type);
    if (t.elem < 0 || t.elem >= type) return false;
    if (t.kind == CoreType::VarArr)
        return GirFlat(m, t.elem) || GirVariableElement(m, t.elem);
    return t.kind == CoreType::Arr && GirVariableElement(m, t.elem);
}

inline bool GirNonfixed(const GirModule &m, GirTypeId type) {
    auto &t = m.Type(type);
    return t.kind == CoreType::VarArr || GirOwnerKind(t.kind) ||
           (t.kind == CoreType::Arr && GirVariableElement(m, t.elem));
}

inline bool GirConstructible(const GirModule &m, GirTypeId type) {
    auto &t = m.Type(type);
    if (t.kind == CoreType::VarArr || t.kind == CoreType::Grow || t.kind == CoreType::Arr)
        return GirFlat(m, t.elem) || (CoreHasConstruction(m.profile) && GirVariableElement(m, t.elem));
    if (t.kind == CoreType::GrowShrink || t.kind == CoreType::Limited) return GirFlat(m, t.elem);
    return GirFlat(m, type);
}

inline bool GirArrayKind(CoreType::Kind kind) {
    return kind == CoreType::Arr || kind == CoreType::VarArr || GirOwnerKind(kind);
}

// What a reference may point to.
inline bool GirRefTarget(const GirModule &m, GirTypeId t) {
    auto &c = m.Type(t);
    if (c.kind == CoreType::Int || c.kind == CoreType::Bool) return true;
    if (c.kind == CoreType::Slice)
        return GirFlat(m, c.elem) || (CoreHasConstruction(m.profile) && GirVariableElement(m, c.elem));
    if (GirArrayKind(c.kind)) return GirConstructible(m, t);
    return c.kind == CoreType::Struct && GirFlat(m, t);
}

// Types a variable, parameter or global may have.
inline bool GirStorable(const GirModule &m, GirTypeId t) {
    auto &c = m.Type(t);
    switch (c.kind) {
        case CoreType::Int: case CoreType::Bool: return true;
        case CoreType::Arr: case CoreType::VarArr: case CoreType::Grow: case CoreType::GrowShrink: case CoreType::Limited:
            return GirConstructible(m, t);
        case CoreType::Struct: return GirFlat(m, t);
        case CoreType::Ref:
            // Reference-to-slice is a parameter-only type, not a general slot type.
            return m.Type(c.elem).kind != CoreType::Slice && GirRefTarget(m, c.elem);
        case CoreType::Slice:
            return GirFlat(m, c.elem) || (CoreHasConstruction(m.profile) && GirVariableElement(m, c.elem));
        default: return false;
    }
}

// Types whose values a read may produce.
inline bool GirReadable(const GirModule &m, GirTypeId t) {
    auto &c = m.Type(t);
    if (c.kind == CoreType::Ref) return GirRefTarget(m, c.elem);
    if (c.kind == CoreType::Slice)
        return GirFlat(m, c.elem) || (CoreHasConstruction(m.profile) && GirVariableElement(m, c.elem));
    return GirFlat(m, t);
}

inline bool GirRefLike(const GirModule &m, GirTypeId t) {
    auto k = m.Type(t).kind;
    return k == CoreType::Ref || k == CoreType::Slice;
}

// An argument of type `a` may be passed where `p` is expected: equal, except
// that a mutable reference or slice may stand for a read-only one.
inline bool GirPassable(const GirModule &m, GirTypeId a, GirTypeId p) {
    auto &x = m.Type(a);
    auto &y = m.Type(p);
    if (CoreHasConstruction(m.profile) && GirNonfixed(m, p))
        return x.kind == CoreType::Ref && x.mut == CoreMut::Mut && x.elem == p;
    if (x.kind == y.kind && (x.kind == CoreType::Ref || x.kind == CoreType::Slice))
        return x.elem == y.elem && GirMutAtLeast(x.mut, y.mut);
    return a == p;
}

inline bool GirInRange(CoreIntTy t, const string &text) {
    // The text is a decimal integer; 20 digits fit in 128 bits.
    if (text.empty() || text.size() > 30) return false;
    __int128 v = 0;
    size_t i = text[0] == '-' ? 1 : 0;
    if (i == text.size()) return false;
    for (; i < text.size(); i++) {
        if (text[i] < '0' || text[i] > '9') return false;
        v = v * 10 + (text[i] - '0');
    }
    if (text[0] == '-') v = -v;
    auto bits = CoreIntBits(t);
    if (CoreIsUnsigned(t)) return v >= 0 && v < ((__int128)1 << bits);
    return v >= -((__int128)1 << (bits - 1)) && v < ((__int128)1 << (bits - 1));
}

inline bool GirSigned(CoreIntTy t) { return !CoreIsUnsigned(t); }

// Whether converting from one integer type to another preserves every value.
inline bool GirPreservesAll(CoreIntTy src, CoreIntTy dst) {
    auto lo = [](CoreIntTy t) { return CoreIsUnsigned(t) ? (__int128)0 : -((__int128)1 << (CoreIntBits(t) - 1)); };
    auto hi = [](CoreIntTy t) {
        return CoreIsUnsigned(t) ? ((__int128)1 << CoreIntBits(t)) - 1 : ((__int128)1 << (CoreIntBits(t) - 1)) - 1;
    };
    return lo(dst) <= lo(src) && hi(src) <= hi(dst);
}

class GirTyper {
public:
    explicit GirTyper(const GirTyEnv &e) : env(e) {}

    GirTyResult Of(const GirInst &i) {
        auto &m = env.m;
        switch (i.op) {
            case GirOp::Int:
                if (m.Type(i.ty).kind != CoreType::Int || !GirInRange(m.Type(i.ty).ity, i.text))
                    return GirTyErr(cat("constant ", i.text, " out of range for its type"));
                return GirTyOk(i.ty);
            case GirOp::Bool: return GirTyOk(m.BoolType());
            case GirOp::Unit: return GirTyOk(m.UnitType());
            case GirOp::Bin: {
                auto t = IntTy(i.a), u = IntTy(i.b);
                if (!t.ok()) return t;
                if (!u.ok()) return u;
                if (t.ty != i.ty || u.ty != i.ty) return GirTyErr("integer operation on operands of another type");
                return GirTyOk(i.ty);
            }
            case GirOp::Un: {
                auto t = IntTy(i.a);
                if (!t.ok()) return t;
                if (t.ty != i.ty) return GirTyErr("integer operation on an operand of another type");
                if (i.un == CoreUnOp::Neg && !GirSigned(m.Type(i.ty).ity))
                    return GirTyErr("negation of an unsigned integer");
                return GirTyOk(i.ty);
            }
            case GirOp::Cmp: {
                if (m.Type(i.ty).kind == CoreType::Bool) {
                    auto t = Data(i.a), u = Data(i.b);
                    if (!t.ok()) return t;
                    if (!u.ok()) return u;
                    if (t.ty != i.ty || u.ty != i.ty) return GirTyErr("boolean comparison of non-booleans");
                    if (i.cmp != CoreCmpOp::Eq && i.cmp != CoreCmpOp::Ne)
                        return GirTyErr("booleans are only compared for equality");
                    return GirTyOk(m.BoolType());
                }
                auto t = IntTy(i.a), u = IntTy(i.b);
                if (!t.ok()) return t;
                if (!u.ok()) return u;
                if (t.ty != i.ty || u.ty != i.ty) return GirTyErr("comparison of operands of another type");
                return GirTyOk(m.BoolType());
            }
            case GirOp::BoolCmp: {
                auto t = Data(i.a), u = Data(i.b);
                if (!t.ok()) return t;
                if (!u.ok()) return u;
                if (m.Type(t.ty).kind != CoreType::Bool || m.Type(u.ty).kind != CoreType::Bool)
                    return GirTyErr("boolean comparison of non-booleans");
                if (i.cmp != CoreCmpOp::Eq && i.cmp != CoreCmpOp::Ne)
                    return GirTyErr("booleans are only compared for equality");
                return GirTyOk(m.BoolType());
            }
            case GirOp::Not: {
                auto t = Data(i.a);
                if (!t.ok()) return t;
                if (m.Type(t.ty).kind != CoreType::Bool) return GirTyErr("boolean not of a non-boolean");
                return GirTyOk(m.BoolType());
            }
            case GirOp::Conv: {
                auto t = IntTy(i.a);
                if (!t.ok()) return t;
                if (t.ty != i.ty) return GirTyErr("conversion of an operand of another type");
                if (m.Type(i.ty2).kind != CoreType::Int || m.Type(i.ty).kind != CoreType::Int)
                    return GirTyErr("conversion between non-integers");
                if (i.conv == CoreConvKind::Widen && !GirPreservesAll(m.Type(i.ty).ity, m.Type(i.ty2).ity))
                    return GirTyErr("a widening that does not preserve every value");
                return GirTyOk(i.ty2);
            }
            case GirOp::Next: {
                auto t = IntTy(i.a);
                if (!t.ok()) return t;
                if (t.ty != i.ty) return GirTyErr("increment of an operand of another type");
                return GirTyOk(i.ty);
            }
            case GirOp::Slot:
                if (i.idx < 0 || i.idx >= (int)env.slots.size())
                    return GirTyErr(cat("slot ", i.idx, " outside the slot table"));
                return GirTyOk(m.RefType(env.slots[i.idx].kind == CoreVarKind::Var ||
                                         GirWholeOwnerBorrowUsesContents(m.Type(env.slots[i.idx].ty).kind)
                                             ? CoreMut::Mut : CoreMut::Const,
                                         env.slots[i.idx].ty));
            case GirOp::Global:
                if (i.idx < 0 || i.idx >= (int)m.globals.size())
                    return GirTyErr(cat("global ", i.idx, " outside the global table"));
                return GirTyOk(m.RefType(m.globals[i.idx].kind == CoreVarKind::Var ||
                                         GirWholeOwnerBorrowUsesContents(m.Type(m.globals[i.idx].ty).kind)
                                             ? CoreMut::Mut : CoreMut::Const,
                                         m.globals[i.idx].ty));
            case GirOp::Elem: {
                auto v = View(i.a);
                if (!v.ok()) return v;
                auto n = IntTy(i.b);
                if (!n.ok()) return n;
                return GirTyOk(m.RefType(m.Type(v.ty).mut, m.Type(v.ty).elem));
            }
            case GirOp::Freeze: {
                auto r = Ref(i.a);
                if (!r.ok()) return r;
                return GirTyOk(m.RefType(CoreMut::Const, m.Type(r.ty).elem));
            }
            case GirOp::Load: {
                auto r = Ref(i.a);
                if (!r.ok()) return r;
                return GirTyOk(m.Type(r.ty).elem);
            }
            case GirOp::Snap: {
                auto r = Ref(i.a);
                if (!r.ok()) return r;
                auto &pointee = m.Type(m.Type(r.ty).elem);
                if (!GirArrayKind(pointee.kind))
                    return GirTyErr("snapshot of a reference to something that is not an array");
                auto mut = i.snap == GirSnapshotMode::Owner ? CoreMut::Mut : m.Type(r.ty).mut;
                return GirTyOk(m.ViewType(mut, pointee.elem));
            }
            case GirOp::SliceView: {
                auto s = Data(i.a);
                if (!s.ok()) return s;
                if (m.Type(s.ty).kind != CoreType::Slice) return GirTyErr("view of a value that is not a slice");
                return GirTyOk(m.ViewType(m.Type(s.ty).mut, m.Type(s.ty).elem));
            }
            case GirOp::ViewLen: {
                auto v = View(i.a);
                if (!v.ok()) return v;
                return GirTyOk(m.IntType(CoreIntTy::I64));
            }
            case GirOp::ViewSlice: {
                auto v = View(i.a);
                if (!v.ok()) return v;
                if (!GirMutAtLeast(m.Type(v.ty).mut, i.mut)) return GirTyErr("a mutable slice of a read-only view");
                for (auto *b : { &i.lo, &i.hi })
                    if (b->kind != GirBound::None) {
                        auto n = IntTy(b->val);
                        if (!n.ok()) return n;
                    }
                return GirTyOk(m.SliceType(i.mut, m.Type(v.ty).elem));
            }
            case GirOp::ArrayLen: {
                auto r = Ref(i.a);
                if (!r.ok()) return r;
                auto k = m.Type(m.Type(r.ty).elem).kind;
                if (!GirArrayKind(k))
                    return GirTyErr("length of a reference to something that is not an array");
                return GirTyOk(m.IntType(CoreIntTy::I64));
            }
            case GirOp::Index: case GirOp::IndexProven: {
                auto v = View(i.a);
                if (!v.ok()) return v;
                auto n = IntTy(i.b);
                if (!n.ok()) return n;
                return GirTyOk(m.RefType(m.Type(v.ty).mut, m.Type(v.ty).elem));
            }
            case GirOp::Push: {
                auto r = Ref(i.a);
                if (!r.ok()) return r;
                auto &pointee = m.Type(m.Type(r.ty).elem);
                if (!GirOwnerKind(pointee.kind))
                    return GirTyErr("push to a reference that does not point at an owner array");
                if (pointee.kind != CoreType::Grow && !CoreHasShrink(m.profile))
                    return GirTyErr("shrink-profile push under core-pilot");
                auto v = Data(i.b);
                if (!v.ok()) return v;
                if (v.ty != pointee.elem) return GirTyErr("a pushed element of another type than the array's");
                return GirTyOk(m.RefType(CoreMut::Mut, pointee.elem));
            }
            case GirOp::Pop: {
                auto r = Ref(i.a);
                if (!r.ok()) return r;
                auto &owner = m.Type(m.Type(r.ty).elem);
                if (!CoreHasShrink(m.profile) || !GirOwnerKind(owner.kind))
                    return GirTyErr("pop from a reference that does not point at a shrink-profile owner array");
                return GirTyOk(owner.elem);
            }
            case GirOp::Call: {
                if (i.idx < 0 || i.idx >= (int)env.sigs.size())
                    return GirTyErr(cat("call of function ", i.idx, ", outside the function table"));
                auto &sig = env.sigs[i.idx];
                if (sig.first.size() != i.vals.size())
                    return GirTyErr(cat("call of function ", i.idx, " with ", i.vals.size(),
                                        " arguments, expected ", sig.first.size()));
                for (size_t k = 0; k < i.vals.size(); k++) {
                    auto a = Data(i.vals[k]);
                    if (!a.ok()) return a;
                    if (!GirPassable(m, a.ty, sig.first[k]))
                        return GirTyErr(cat("argument %", i.vals[k], " is not accepted by its parameter"));
                }
                if (sig.second.empty()) return GirTyOk(m.UnitType());
                if (sig.second.size() == 1) return GirTyOk(sig.second[0]);
                if (!CoreHasConstruction(m.profile)) return GirTyErr(cat("function ", i.idx, " has several results"));
                return GirTyOk(m.TupleType(sig.second));
            }
            case GirOp::Result: {
                auto pack = Val(i.a);
                if (!pack.ok()) return pack;
                auto &tuple = m.Type(pack.ty);
                if (tuple.kind != CoreType::Tuple || i.idx < 0 || i.idx >= (int)tuple.parts.size())
                    return GirTyErr("result projection outside a call pack");
                return GirTyOk(tuple.parts[i.idx]);
            }
            case GirOp::Render: {
                auto operand = Val(i.a);
                if (!operand.ok()) return operand;
                auto &type = m.Type(operand.ty);
                if (!CoreHasConstruction(m.profile) || m.low ||
                    (type.kind != CoreType::View && !GirFlat(m, operand.ty)))
                    return GirTyErr("render snapshot requires a fixed value or sampled view");
                return GirTyOk(m.ViewType(CoreMut::Const, m.IntType(CoreIntTy::U8)));
            }
            case GirOp::Bytes: {
                if (i.ty < 0 || i.ty >= (int)m.types.size()) return GirTyErr("static bytes type outside the table");
                auto &slice = m.Type(i.ty);
                if (slice.kind != CoreType::Slice || slice.mut != CoreMut::Const ||
                    m.Type(slice.elem).kind != CoreType::Int || m.Type(slice.elem).ity != CoreIntTy::U8)
                    return GirTyErr("static bytes require slice const u8");
                return GirTyOk(i.ty);
            }
            case GirOp::CallConstruct: {
                if (i.idx < 0 || i.idx >= (int)m.funcs.size()) return GirTyErr("construction callee outside the table");
                auto &callee = m.funcs[i.idx];
                if (i.vals.size() != callee.params.size()) return GirTyErr("construction call source argument count differs");
                for (size_t parameter = 0; parameter < i.vals.size(); parameter++) {
                    auto argument = Data(i.vals[parameter]);
                    if (!argument.ok()) return argument;
                    auto expected = callee.params[parameter];
                    if (GirNonfixed(m, expected)) {
                        auto &reference = m.Type(argument.ty);
                        if (reference.kind != CoreType::Ref || reference.mut != CoreMut::Mut || reference.elem != expected)
                            return GirTyErr("construction argument is not the owned parameter reference");
                    } else if (!GirPassable(m, argument.ty, expected)) return GirTyErr("construction call argument type differs");
                }
                vector<GirTypeId> results;
                size_t channel = 0;
                for (size_t position = 0; position < callee.results.size(); position++) {
                    auto type = callee.results[position];
                    if (!GirNonfixed(m, type)) { results.push_back(type); continue; }
                    if (channel >= i.vals2.size() || callee.resultProtocols.size() != callee.results.size())
                        return GirTyErr("construction call omits a result destination or descriptor");
                    auto destination = Val(i.vals2[channel++]);
                    if (!destination.ok()) return destination;
                    auto &carrier = m.Type(destination.ty);
                    if (carrier.kind != CoreType::Dest || carrier.elem != type ||
                        carrier.request != callee.resultProtocols[position].request)
                        return GirTyErr("construction result destination type or request differs");
                    results.push_back(m.CarrierType(CoreType::Built, type, carrier.request));
                }
                if (channel == 0 || channel != i.vals2.size()) return GirTyErr("construction call has no exact result channels");
                return GirTyOk(results.size() == 1 ? results[0] : m.TupleType(std::move(results)));
            }
            case GirOp::Arr: {
                auto &t = m.Type(i.ty);
                if (t.kind != CoreType::Arr && !GirOwnerKind(t.kind))
                    return GirTyErr("array literal of a type that is not an array");
                if ((t.kind == CoreType::GrowShrink || t.kind == CoreType::Limited) &&
                    !CoreHasShrink(m.profile))
                    return GirTyErr("shrink-profile literal under core-pilot");
                if (t.kind == CoreType::Arr && (int64_t)i.vals.size() != t.count)
                    return GirTyErr(cat("array literal of ", i.vals.size(), " elements for a type of ", t.count));
                if (t.kind == CoreType::Limited && (int64_t)i.vals.size() > t.count)
                    return GirTyErr(cat("limited literal of ", i.vals.size(), " elements exceeds capacity ", t.count));
                for (auto v : i.vals) {
                    auto e = Data(v);
                    if (!e.ok()) return e;
                    if (e.ty != t.elem) return GirTyErr("array element of another type than the array's");
                }
                return GirTyOk(i.ty);
            }
            case GirOp::Fill: {
                auto &t = m.Type(i.ty);
                if (t.kind != CoreType::Arr) return GirTyErr("fill of a type that is not a fixed array");
                auto e = Data(i.a);
                if (!e.ok()) return e;
                if (e.ty != t.elem) return GirTyErr("fill value of another type than the elements");
                return GirTyOk(i.ty);
            }
            case GirOp::Struct: {
                if (m.Type(i.ty).kind != CoreType::Struct)
                    return GirTyErr("record constructor of a type that is not a struct");
                auto sid = m.Type(i.ty).structid;
                if (sid < 0 || sid >= (int)m.structs.size())
                    return GirTyErr("record constructor with an unknown nominal struct id");
                auto &fields = m.structs[sid].fields;
                if (fields.size() != i.vals.size())
                    return GirTyErr(cat("record constructor of ", i.vals.size(), " fields for a type with ",
                                        fields.size()));
                for (size_t k = 0; k < fields.size(); k++) {
                    auto v = Data(i.vals[k]);
                    if (!v.ok()) return v;
                    if (v.ty != fields[k].type)
                        return GirTyErr(cat("record field ", k, " has another type than its declaration"));
                }
                return GirTyOk(i.ty);
            }
            case GirOp::Field: {
                auto r = Ref(i.a);
                if (!r.ok()) return r;
                auto &owner = m.Type(m.Type(r.ty).elem);
                if (owner.kind != CoreType::Struct || owner.structid < 0 ||
                    owner.structid >= (int)m.structs.size())
                    return GirTyErr("field address through a reference that does not point at a struct");
                auto &fields = m.structs[owner.structid].fields;
                if (i.idx < 0 || i.idx >= (int)fields.size())
                    return GirTyErr(cat("field ", i.idx, " outside the struct's field table"));
                auto mut = fields[i.idx].binding == CoreVarKind::Var ? CoreMut::Mut : CoreMut::Const;
                return GirTyOk(m.RefType(mut, fields[i.idx].type));
            }
            case GirOp::DestAdapt: {
                auto input = Val(i.a);
                if (!input.ok()) return input;
                auto carrier = m.Type(input.ty);
                if (carrier.kind != CoreType::Dest || i.ty < 0 || i.ty >= (int)m.types.size() ||
                    !GirNonfixed(m, i.ty) || !GirConstructible(m, i.ty) ||
                    !GirArrayKind(m.Type(carrier.elem).kind) || !GirArrayKind(m.Type(i.ty).kind) ||
                    m.Type(carrier.elem).elem != m.Type(i.ty).elem ||
                    (i.request != CoreRequest::Value && i.request != CoreRequest::ElementRun))
                    return GirTyErr("destination adaptation changes elements or has no receiving protocol");
                return GirTyOk(m.CarrierType(CoreType::Dest, i.ty, i.request));
            }
            case GirOp::DestAdaptFinish: {
                auto input = Val(i.a);
                if (!input.ok()) return input;
                auto carrier = m.Type(input.ty);
                if (carrier.kind != CoreType::Built && carrier.kind != CoreType::Cancelled)
                    return GirTyErr("destination adaptation restoration requires a closed producer carrier");
                auto original = AdaptationOrigin(i.a);
                if (!original.ok()) return original;
                auto receiving = m.Type(original.ty);
                return GirTyOk(m.CarrierType(carrier.kind, receiving.elem, receiving.request));
            }
            case GirOp::DestPublishRef: {
                auto completed = Val(i.a);
                if (!completed.ok()) return completed;
                auto &carrier = m.Type(completed.ty);
                if (carrier.kind != CoreType::Built || carrier.request != CoreRequest::Value)
                    return GirTyErr("push publication requires a completed value destination");
                return GirTyOk(m.RefType(CoreMut::Mut, carrier.elem));
            }
            case GirOp::DestOpen: {
                if (m.low || m.profile != CoreProfile::Construction)
                    return GirTyErr("construction destination under an earlier profile or stage");
                if (i.ty < 0 || i.ty >= (int)m.types.size())
                    return GirTyErr("destination type outside the type table");
                GirTypeId receiverType = -1;
                CoreRequest receiverRequest = CoreRequest::Value;
                if (auto slot = get_if<GirDestSlotReceiver>(&i.destReceiver)) {
                    if (slot->slot < 0 || slot->slot >= (int)env.slots.size())
                        return GirTyErr("destination slot outside the slot table");
                    receiverType = env.slots[slot->slot].ty;
                } else if (auto global = get_if<GirDestGlobalReceiver>(&i.destReceiver)) {
                    if (global->global < 0 || global->global >= (int)m.globals.size())
                        return GirTyErr("destination global outside the global table");
                    receiverType = m.globals[global->global].ty;
                } else if (auto argument = get_if<GirDestArgReceiver>(&i.destReceiver)) {
                    if (argument->function < 0 || argument->function >= (int)m.funcs.size() ||
                        argument->parameter < 0 || argument->parameter >= (int)m.funcs[argument->function].params.size())
                        return GirTyErr("destination call parameter outside the signature");
                    receiverType = m.funcs[argument->function].params[argument->parameter];
                } else {
                    int value = -1;
                    if (auto whole = get_if<GirDestWholeReceiver>(&i.destReceiver)) value = whole->reference;
                    if (auto push = get_if<GirDestPushReceiver>(&i.destReceiver)) value = push->reference;
                    if (auto append = get_if<GirDestAppendReceiver>(&i.destReceiver)) {
                        value = append->reference;
                        receiverRequest = CoreRequest::ElementRun;
                    }
                    auto reference = Ref(value);
                    if (!reference.ok()) return reference;
                    if (m.Type(reference.ty).mut != CoreMut::Mut)
                        return GirTyErr("construction receiver is read-only");
                    receiverType = m.Type(reference.ty).elem;
                    if (holds_alternative<GirDestPushReceiver>(i.destReceiver)) {
                        if (!GirOwnerKind(m.Type(receiverType).kind)) return GirTyErr("push receiver is not an owner array");
                        receiverType = m.Type(receiverType).elem;
                    }
                }
                if (!GirNonfixed(m, i.ty) || !GirConstructible(m, i.ty) ||
                    !GirConstructible(m, receiverType) || i.request != receiverRequest)
                    return GirTyErr("destination receiving type or request is not constructible");
                if (receiverType != i.ty && (!GirArrayKind(m.Type(receiverType).kind) ||
                    !GirArrayKind(m.Type(i.ty).kind) || m.Type(receiverType).elem != m.Type(i.ty).elem))
                    return GirTyErr("destination producer and receiver have different elements");
                if (i.knownCount) {
                    auto count = IntTy(*i.knownCount);
                    if (!count.ok()) return count;
                    if (count.ty != m.IntType(CoreIntTy::I64))
                        return GirTyErr("destination element count is not i64");
                }
                CoreType result;
                result.kind = CoreType::Dest;
                result.elem = i.ty;
                result.request = i.request;
                return GirTyOk(m.Intern(result));
            }
            case GirOp::DestFinish: case GirOp::DestAbandon: {
                auto dest = Val(i.a);
                if (!dest.ok()) return dest;
                auto &type = m.Type(dest.ty);
                if (type.kind != CoreType::Dest &&
                    !(i.op == GirOp::DestAbandon && type.kind == CoreType::Built))
                    return GirTyErr("construction completion or abandonment has no owned carrier");
                CoreType result;
                result.kind = i.op == GirOp::DestFinish ? CoreType::Built : CoreType::Cancelled;
                result.elem = type.elem;
                result.request = type.request;
                return GirTyOk(m.Intern(result));
            }
            case GirOp::DestChild: {
                auto parent = Val(i.a);
                if (!parent.ok()) return parent;
                auto &carrier = m.Type(parent.ty);
                if (carrier.kind != CoreType::Dest || m.Type(carrier.elem).elem != i.ty ||
                    !GirNonfixed(m, i.ty) || !GirVariableElement(m, i.ty))
                    return GirTyErr("nested destination does not match the next variable element");
                return GirTyOk(m.CarrierType(CoreType::Dest, i.ty, CoreRequest::Value));
            }
            case GirOp::DestNamed:
                if (i.idx < 0 || i.idx >= (int)env.slots.size() || !GirNonfixed(m, env.slots[i.idx].ty))
                    return GirTyErr("named result does not name a nonfixed slot");
                return GirTyOk(m.CarrierType(CoreType::Built, env.slots[i.idx].ty, CoreRequest::Value));
            case GirOp::ResultExitDest: case GirOp::TargetDest:
                if (i.ty < 0 || i.ty >= (int)m.types.size() || !GirNonfixed(m, i.ty) ||
                    (i.request != CoreRequest::Value && i.request != CoreRequest::ElementRun))
                    return GirTyErr("exit destination has no nonfixed result descriptor");
                if (i.op == GirOp::TargetDest) {
                    if (i.idx < 0 || i.idx >= (int)m.targets.size() || m.targets[i.idx].members.empty())
                        return GirTyErr("exit target is outside the target table");
                    auto &member = m.funcs[m.targets[i.idx].members[0]];
                    if (i.idx2 < 0 || i.idx2 >= (int)member.results.size() || member.results[i.idx2] != i.ty ||
                        member.resultProtocols.size() != member.results.size() ||
                        member.resultProtocols[i.idx2].request != i.request)
                        return GirTyErr("exit destination differs from its target result descriptor");
                }
                return GirTyOk(m.CarrierType(CoreType::Dest, i.ty, i.request));
            case GirOp::DestAbandonNamed: {
                auto replacement = Val(i.a);
                if (!replacement.ok()) return replacement;
                auto &carrier = m.Type(replacement.ty);
                if (carrier.kind != CoreType::Built || i.idx < 0 || i.idx >= (int)env.slots.size() ||
                    env.slots[i.idx].ty != carrier.elem)
                    return GirTyErr("named abandonment does not match the replacement completion");
                return GirTyOk(m.CarrierType(CoreType::Cancelled, carrier.elem, carrier.request));
            }
            case GirOp::DestArg: {
                auto completed = Val(i.a);
                if (!completed.ok()) return completed;
                auto &carrier = m.Type(completed.ty);
                if (carrier.kind != CoreType::Built || carrier.request != CoreRequest::Value)
                    return GirTyErr("owned argument requires a value completion");
                return GirTyOk(m.RefType(CoreMut::Mut, carrier.elem));
            }
            case GirOp::DestValue: case GirOp::DestStage: case GirOp::DestRelocate: case GirOp::DestFit: {
                auto input = Val(i.a);
                if (!input.ok()) return input;
                auto carrier = m.Type(input.ty);
                auto open = i.op == GirOp::DestValue || i.op == GirOp::DestStage;
                if (carrier.kind != (open ? CoreType::Dest : CoreType::Built))
                    return GirTyErr("construction adapter has the wrong carrier state");
                if (i.op == GirOp::DestValue) {
                    if (carrier.request != CoreRequest::ElementRun) return GirTyErr("value adapter does not consume an element run");
                    carrier.request = CoreRequest::Value;
                }
                if (i.op == GirOp::DestRelocate) {
                    if (i.reason == GirEventReason::HeaderRemoval) {
                        if (carrier.request != CoreRequest::Value) return GirTyErr("header removal requires a value completion");
                        carrier.request = CoreRequest::ElementRun;
                    } else if (i.reason != GirEventReason::ExitValue) return GirTyErr("unknown destination relocation reason");
                }
                return GirTyOk(m.Intern(carrier));
            }
            // The low stage: scalars and addresses.
            case GirOp::PtrEq: {
                auto left = PtrOf(i.a), right = PtrOf(i.b);
                if (!left.ok()) return left;
                if (!right.ok()) return right;
                return GirTyOk(m.BoolType());
            }
            case GirOp::SourceTargetEnter: return GirTyOk(m.PtrType());
            case GirOp::SourceTargetGet: {
                auto token = PtrOf(i.a);
                if (!token.ok()) return token;
                return GirTyOk(m.PtrType());
            }
            case GirOp::SourceNew: {
                auto storage = IntTy(i.a);
                if (!storage.ok()) return storage;
                if (storage.ty != m.IntType(CoreIntTy::I64)) return GirTyErr("source storage identity is not i64");
                for (auto path : i.vals) {
                    auto index = IntTy(path);
                    if (!index.ok()) return index;
                    if (index.ty != storage.ty) return GirTyErr("source path index is not i64");
                }
                return GirTyOk(m.PtrType());
            }
            case GirOp::SourceChild: {
                auto source = PtrOf(i.a), index = IntTy(i.b);
                if (!source.ok()) return source;
                if (!index.ok()) return index;
                if (index.ty != m.IntType(CoreIntTy::I64)) return GirTyErr("source child index is not i64");
                return GirTyOk(m.PtrType());
            }
            case GirOp::SourceParam: case GirOp::SourceEnter: case GirOp::SourceGlobal: return GirTyOk(m.PtrType());
            case GirOp::SourceCallPush:
                for (auto source : i.vals) if (source >= 0) { auto pointer = PtrOf(source); if (!pointer.ok()) return pointer; }
                return GirTyOk(m.PtrType());
            case GirOp::SourceCallGet: {
                auto token = PtrOf(i.a);
                if (!token.ok()) return token;
                return GirTyOk(m.PtrType());
            }
            case GirOp::PtrOffset: {
                auto p = PtrOf(i.a), n = Data(i.b);
                if (!p.ok()) return p;
                if (!n.ok()) return n;
                if (n.ty != m.IntType(CoreIntTy::I64)) return GirTyErr("an index that is not an i64");
                return GirTyOk(m.PtrType());
            }
            case GirOp::PLoad: {
                auto p = PtrOf(i.a);
                if (!p.ok()) return p;
                auto k = m.Type(i.ty).kind;
                if (k != CoreType::Int && k != CoreType::Bool && k != CoreType::Ptr)
                    return GirTyErr("a load of something that is not a scalar");
                return GirTyOk(i.ty);
            }
            case GirOp::FrameAddr:
                if (!env.members || i.idx < 0 || i.idx >= (int)env.members->size())
                    return GirTyErr(cat("frame member ", i.idx, " outside the frame"));
                return GirTyOk(m.PtrType());
            case GirOp::LocalGet:
                if (!env.members || i.idx < 0 || i.idx >= (int)env.members->size() ||
                    ((*env.members)[i.idx].kind != GirMember::Scalar &&
                     (*env.members)[i.idx].kind != GirMember::Dynamic))
                    return GirTyErr(cat("frame member ", i.idx, " is not a scalar of the frame"));
                return GirTyOk((*env.members)[i.idx].kind == GirMember::Dynamic ? m.PtrType() : (*env.members)[i.idx].ty);
            case GirOp::StackAt: {
                auto b = Data(i.a);
                if (!b.ok()) return b;
                if (b.ty != m.IntType(CoreIntTy::I64)) return GirTyErr("a stack base that is not an i64");
                return GirTyOk(m.PtrType());
            }
            case GirOp::StackMark: case GirOp::HdrBase: {
                auto p = PtrOf(i.a);
                if (!p.ok()) return p;
                return GirTyOk(m.PtrType());
            }
            case GirOp::GlobalAddr: case GirOp::GlobalStack:
                if (i.idx < 0 || i.idx >= (int)m.lowglobals.size())
                    return GirTyErr(cat("global ", i.idx, " outside the global table"));
                return GirTyOk(m.PtrType());
            case GirOp::HdrLen: {
                auto p = PtrOf(i.a);
                if (!p.ok()) return p;
                return GirTyOk(m.IntType(CoreIntTy::I64));
            }
            case GirOp::StaticBytes: return GirTyOk(m.PtrType());
            case GirOp::ReturnFlagGet: return GirTyOk(m.IntType(CoreIntTy::I64));
            case GirOp::TargetLoad:
                if (i.idx < 0 || i.idx >= (int)m.lowtargets.size() || i.idx2 < 0 ||
                    i.idx2 >= (int)m.lowtargets[i.idx].cells.size())
                    return GirTyErr("target cell outside the target table");
                return GirTyOk(m.lowtargets[i.idx].cells[i.idx2]);
            case GirOp::TraceId:
                if ((uint8_t)i.trace > (uint8_t)GirTraceKind::Destination)
                    return GirTyErr("unknown construction trace id kind");
                return GirTyOk(m.IntType(CoreIntTy::I64));
            case GirOp::Format: {
                auto scalar = Data(i.a), pointer = PtrOf(i.b);
                if (!scalar.ok()) return scalar;
                if (!pointer.ok()) return pointer;
                auto &type = m.Type(scalar.ty);
                switch (i.format) {
                    case GirFormatKind::Int:
                        if (type.kind != CoreType::Int || CoreIsUnsigned(type.ity))
                            return GirTyErr("signed formatting requires a signed integer");
                        break;
                    case GirFormatKind::Uint:
                        if (type.kind != CoreType::Int || !CoreIsUnsigned(type.ity))
                            return GirTyErr("unsigned formatting requires an unsigned integer");
                        break;
                    case GirFormatKind::Bool:
                        if (type.kind != CoreType::Bool) return GirTyErr("boolean formatting requires bool");
                        break;
                    default: return GirTyErr("unknown text formatting kind");
                }
                return GirTyOk(m.IntType(CoreIntTy::I64));
            }
            default: return GirTyErr("not an instruction that defines a value");
        }
    }

    GirTyResult Val(int v) {
        if (v < 0 || v >= (int)env.vals.size() || env.vals[v] < 0)
            return GirTyErr(cat("value %", v, " has no type"));
        return GirTyOk(env.vals[v]);
    }
    GirTyResult Data(int v) {
        auto t = Val(v);
        if (!t.ok()) return t;
        auto kind = env.m.Type(t.ty).kind;
        if (kind == CoreType::View)
            return GirTyErr(cat("value %", v, " is a view where a data value is required"));
        if (kind == CoreType::Dest || kind == CoreType::Built || kind == CoreType::Cancelled)
            return GirTyErr(cat("value %", v, " is a construction carrier where a data value is required"));
        return t;
    }
    GirTyResult IntTy(int v) {
        auto t = Data(v);
        if (!t.ok()) return t;
        if (env.m.Type(t.ty).kind != CoreType::Int) return GirTyErr(cat("value %", v, " is not an integer"));
        return t;
    }
    GirTyResult PtrOf(int v) {
        auto t = Data(v);
        if (!t.ok()) return t;
        if (env.m.Type(t.ty).kind != CoreType::Ptr) return GirTyErr(cat("value %", v, " is not an address"));
        return t;
    }
    GirTyResult Ref(int v) {
        auto t = Data(v);
        if (!t.ok()) return t;
        if (env.m.Type(t.ty).kind != CoreType::Ref) return GirTyErr(cat("value %", v, " is not a reference"));
        return t;
    }
    GirTyResult View(int v) {
        auto t = Val(v);
        if (!t.ok()) return t;
        if (env.m.Type(t.ty).kind != CoreType::View) return GirTyErr(cat("value %", v, " is not a view"));
        return t;
    }

private:
    GirTyResult AdaptationOrigin(int value) const {
        if (!env.blocks) return GirTyErr("destination adaptation has no control-flow lineage");
        map<int, set<int>> origins;
        map<pair<int, int>, set<int>> packed;
        for (auto &block : *env.blocks) for (auto &inst : block.insts)
            if (inst.op == GirOp::DestAdapt) origins[inst.res].insert(inst.a);
        bool changed = true;
        auto merge = [&](set<int> &to, const set<int> &from) {
            auto before = to.size();
            to.insert(from.begin(), from.end());
            changed |= before != to.size();
        };
        while (changed) {
            changed = false;
            for (auto &block : *env.blocks) for (auto &inst : block.insts) {
                switch (inst.op) {
                    case GirOp::DestFinish: case GirOp::DestAbandon: case GirOp::DestValue:
                    case GirOp::DestStage: case GirOp::DestFit: case GirOp::DestRelocate:
                        merge(origins[inst.res], origins[inst.a]); break;
                    case GirOp::CallConstruct: {
                        auto &callee = env.m.funcs[inst.idx];
                        size_t destination = 0;
                        for (size_t result = 0; result < callee.results.size(); result++) {
                            if (!GirNonfixed(env.m, callee.results[result])) continue;
                            if (destination >= inst.vals2.size()) break;
                            auto &from = origins[inst.vals2[destination++]];
                            if (callee.results.size() == 1) merge(origins[inst.res], from);
                            else merge(packed[{ inst.res, (int)result }], from);
                        }
                        break;
                    }
                    case GirOp::Result: merge(origins[inst.res], packed[{ inst.a, inst.idx }]); break;
                    case GirOp::Br: case GirOp::CondBr: {
                        auto edge = [&](int target, const vector<int> &values) {
                            if (target < 0 || target >= (int)env.blocks->size()) return;
                            auto &parameters = env.blocks->at(target).params;
                            for (size_t position = 0; position < min(parameters.size(), values.size()); position++)
                                merge(origins[parameters[position].first], origins[values[position]]);
                        };
                        edge(inst.idx, inst.vals);
                        if (inst.op == GirOp::CondBr) edge(inst.idx2, inst.vals2);
                        break;
                    }
                    case GirOp::Invoke: {
                        auto &callee = env.m.funcs[inst.idx];
                        size_t destination = 0;
                        for (size_t result = 0; result < callee.results.size(); result++) {
                            if (!GirNonfixed(env.m, callee.results[result])) continue;
                            if (destination >= inst.vals2.size()) break;
                            auto &from = origins[inst.vals2[destination++]];
                            merge(origins[env.blocks->at(inst.a).params[result].first], from);
                        }
                        for (auto &escape : inst.escapes) {
                            auto &target = env.m.funcs[env.m.targets[escape.target].members[0]];
                            auto &parameters = env.blocks->at(escape.block).params;
                            for (size_t position = 0; position < inst.vals2.size(); position++)
                                merge(origins[parameters[target.results.size() + position].first], origins[inst.vals2[position]]);
                        }
                        auto forwarded = [&](int target, size_t offset, const vector<int> &values) {
                            auto &parameters = env.blocks->at(target).params;
                            for (size_t position = 0; position < values.size(); position++)
                                merge(origins[parameters[offset + position].first], origins[values[position]]);
                        };
                        forwarded(inst.a, callee.results.size(), inst.forwarded);
                        for (auto &escape : inst.escapes) {
                            auto &target = env.m.funcs[env.m.targets[escape.target].members[0]];
                            forwarded(escape.block, target.results.size() + inst.vals2.size(), escape.forwarded);
                        }
                        break;
                    }
                    default: break;
                }
            }
        }
        auto &found = origins[value];
        GirTypeId original = -1;
        for (auto source : found) {
            if (source < 0 || source >= (int)env.vals.size() || env.vals[source] < 0)
                return GirTyErr("destination adaptation lineage has no receiving type");
            auto type = env.vals[source];
            if (original >= 0 && original != type)
                return GirTyErr("destination adaptation merges different receiving protocols");
            original = type;
        }
        if (original < 0 || env.m.Type(original).kind != CoreType::Dest)
            return GirTyErr("closed producer has no matching destination adaptation");
        return GirTyOk(original);
    }
    const GirTyEnv &env;
};

}  // namespace goose
