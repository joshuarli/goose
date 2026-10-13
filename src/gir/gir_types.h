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

// What a reference may point to.
inline bool GirRefTarget(const GirModule &m, GirTypeId t) {
    auto &c = m.Type(t);
    if (c.kind == CoreType::Int || c.kind == CoreType::Bool) return true;
    if (c.kind == CoreType::Slice) return GirFlat(m, c.elem);
    if (c.kind == CoreType::Arr || GirOwnerKind(c.kind)) return GirFlat(m, c.elem);
    return c.kind == CoreType::Struct && GirFlat(m, t);
}

// Types a variable, parameter or global may have.
inline bool GirStorable(const GirModule &m, GirTypeId t) {
    auto &c = m.Type(t);
    switch (c.kind) {
        case CoreType::Int: case CoreType::Bool: return true;
        case CoreType::Arr: case CoreType::Grow: case CoreType::GrowShrink: case CoreType::Limited:
            return GirFlat(m, c.elem);
        case CoreType::Struct: return GirFlat(m, t);
        case CoreType::Ref:
            // Reference-to-slice is a parameter-only type, not a general slot type.
            return m.Type(c.elem).kind != CoreType::Slice && GirRefTarget(m, c.elem);
        case CoreType::Slice: return GirFlat(m, c.elem);
        default: return false;
    }
}

// Types whose values a read may produce.
inline bool GirReadable(const GirModule &m, GirTypeId t) {
    auto &c = m.Type(t);
    if (c.kind == CoreType::Ref) return GirRefTarget(m, c.elem);
    if (c.kind == CoreType::Slice) return GirFlat(m, c.elem);
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
                if (pointee.kind != CoreType::Arr && !GirOwnerKind(pointee.kind))
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
                if (k != CoreType::Arr && !GirOwnerKind(k))
                    return GirTyErr("length of a reference to something that is not an array");
                return GirTyOk(m.IntType(CoreIntTy::I64));
            }
            case GirOp::Index: {
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
                if (pointee.kind != CoreType::Grow && m.profile != CoreProfile::Shrink)
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
                if (m.profile != CoreProfile::Shrink || !GirOwnerKind(owner.kind))
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
                return GirTyErr(cat("function ", i.idx, " has several results"));
            }
            case GirOp::Arr: {
                auto &t = m.Type(i.ty);
                if (t.kind != CoreType::Arr && !GirOwnerKind(t.kind))
                    return GirTyErr("array literal of a type that is not an array");
                if ((t.kind == CoreType::GrowShrink || t.kind == CoreType::Limited) &&
                    m.profile != CoreProfile::Shrink)
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
            // The low stage: scalars and addresses.
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
                    (*env.members)[i.idx].kind != GirMember::Scalar)
                    return GirTyErr(cat("frame member ", i.idx, " is not a scalar of the frame"));
                return GirTyOk((*env.members)[i.idx].ty);
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
        if (env.m.Type(t.ty).kind == CoreType::View)
            return GirTyErr(cat("value %", v, " is a view where a data value is required"));
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
    const GirTyEnv &env;
};

}  // namespace goose
