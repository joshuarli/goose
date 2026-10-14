import Goose.GIR.Validate
import Goose.GIR.Eval
import Goose.GIR.Lemmas

/-!
What acceptance by `validate` establishes about a module.

The statements here are about the module, not about a run. They name the
invariants the checks stand for, each stated without reference to how the
checker computes it:

* every block ends in exactly one terminator;
* every instruction that defines a value is typed by the typing rules from
  the types of its operands, and the type recorded for its result is that type;
* every instruction that can abort or stands for a statement carries an origin;
* each function's summary contains the effects its body has, as the effect
  analysis computes them.

Acceptance does not establish that dominance holds or that scopes balance:
those checks run iterative analyses (dominator sets, the scopes entered at each
block) whose soundness is not proved here. It does not establish that a
reference stays valid, which no check of the validator looks at: a module can
be accepted and yet read a slot after its scope was left, and `run` then
faults.
-/

namespace Goose.GIR

open Goose.Core

/-- The functions of a module: the implementations, then the initializers. -/
def Module.allFuncs (m : Module) : List Func :=
  m.funcs.toList ++ m.globals.toList.map (·.init)

def TerminatedBlocks (f : Func) : Prop :=
  ∀ b ∈ f.blocks, b.terms.length = 1 ∧ b.lastTerm?.isSome = true

def TypedDefs (m : Module) (f : Func) : Prop :=
  ∀ b ∈ f.blocks, ∀ r op, Inst.def r op ∈ b.insts →
    ∃ t, op.resultTy { m.tyEnv f with vals := f.valueTypes m } = .ok t ∧
      (f.valueTypes m)[r]? = some (some t)

def OriginsPresent (profile : ArtifactProfile) (f : Func) : Prop :=
  ∀ b ∈ f.blocks, ∀ i ∈ b.insts, i.needsOriginIn profile = true → i.origin.isSome = true

/-- The effects are within what the summary declares. -/
def EffectsWithin (e : Core.Eff) (s : SummaryAnn) : Prop :=
  match s with
  | .unknown => True
  | .known sm =>
    e.unknown = false ∧
    (∀ t ∈ e.reads, t ∈ sm.reads) ∧ (∀ t ∈ e.writes, t ∈ sm.writes) ∧
    (∀ t ∈ e.grows, t ∈ sm.grows) ∧ (∀ t ∈ e.shrinks, t ∈ sm.shrinks) ∧
    (∀ t ∈ e.rebinds, t ∈ sm.rebinds) ∧
    (e.aborts = true → sm.aborts = true) ∧ (e.outputs = true → sm.outputs = true)

theorem omittedShrink_not_within {e : Core.Eff} {s : Summary} {t : Target}
    (ht : t ∈ e.shrinks) (hnot : t ∉ s.shrinks) :
    ¬ EffectsWithin e (.known s) := by
  intro h
  simp only [EffectsWithin] at h
  rcases h with ⟨_, _, _, _, hshrinks, _, _, _⟩
  exact hnot (hshrinks t ht)

example : ¬ EffectsWithin ({ shrinks := [.param 0] } : Core.Eff)
    (.known ⟨[], [], [], [], [], false, false⟩) := by
  apply omittedShrink_not_within (t := Target.param 0)
  · simp
  · simp

theorem bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

theorem checkAll_mem {ε : Type} {xs : List α} {f : α → Except ε Unit}
    (h : checkAll xs f = .ok ()) {x : α} (hx : x ∈ xs) : f x = .ok () := checkAll_ok h x hx

theorem validate_stages {m : Module} (h : validate m = .ok ()) :
    (checkAll m.infos fun i => checkTypes m i.label i.f i.vt) = .ok () ∧
    (checkAll m.infos fun i => checkCfg i.label i.f i.vt) = .ok () ∧
    (checkAll (List.range m.funcs.size)
      (checkSummaryOf m m.implTypes (resultRoots m m.implTypes) m.rootCount)) = .ok () ∧
    (checkAll m.infos fun i => checkOrigins m.profile i.label i.f) = .ok () := by
  unfold validate at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, ht, h⟩ := bind_ok h
  obtain ⟨_, hc, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, hs, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  exact ⟨ht, hc, hs, h⟩

theorem asCheck_ok {c : Code} {label : String} {α : Type} {r : Except String α} {a : α}
    (h : asCheck c label r = .ok a) : r = .ok a := by
  cases r with
  | error e => simp [asCheck, violation] at h
  | ok b => simp [asCheck] at h; rw [h]

theorem exists_zipIdx {α : Type} (l : List α) (n : Nat) {b : α} (hb : b ∈ l) :
    ∃ i, (b, i) ∈ l.zipIdx n := by
  induction l generalizing n with
  | nil => simp at hb
  | cons a as ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨n, by simp [List.zipIdx_cons]⟩
    · obtain ⟨i, hi⟩ := ih (n + 1) hb
      exact ⟨i, by simp [List.zipIdx_cons, hi]⟩

theorem mem_infos {m : Module} {f : Func} (hf : f ∈ m.allFuncs) :
    ∃ i ∈ m.infos, i.f = f ∧ i.vt = f.valueTypes m := by
  simp only [Module.allFuncs, List.mem_append, List.mem_map] at hf
  rcases hf with hf | ⟨g, hg, rfl⟩
  · refine ⟨FnInfo.mk s!"function {f.name}" f (f.valueTypes m), ?_, rfl, rfl⟩
    simp only [Module.infos, Module.labelled, List.map_append, List.mem_append, List.map_map, List.mem_map]
    exact Or.inl ⟨f, hf, rfl⟩
  · refine ⟨FnInfo.mk s!"initializer of global {g.name}" g.init (g.init.valueTypes m), ?_, rfl, rfl⟩
    simp only [Module.infos, Module.labelled, List.map_append, List.mem_append, List.map_map, List.mem_map]
    exact Or.inr ⟨g, hg, rfl⟩

theorem terminated_of_cfg {label : String} {f : Func} {vt : Array (Option VTy)}
    (h : checkCfg label f vt = .ok ()) : TerminatedBlocks f := by
  unfold checkCfg at h
  obtain ⟨_, h1, _⟩ := bind_ok h
  intro b hb
  obtain ⟨i, hi⟩ := exists_zipIdx f.blocks.toList 0 (Array.mem_toList_iff.mpr hb)
  have := checkAll_mem h1 hi
  simp only [] at this
  by_cases ht : b.terms.length = 1
  · refine ⟨ht, ?_⟩
    cases hl : b.lastTerm? with
    | some t => rfl
    | none =>
      simp [hl, violation, bind, Except.bind] at this
      split at this <;> cases this
  · simp [ht, violation, bind, Except.bind] at this

theorem typed_of_types {m : Module} {label : String} {f : Func} {vt : Array (Option VTy)}
    (hvt : vt = f.valueTypes m) (h : checkTypes m label f vt = .ok ()) : TypedDefs m f := by
  subst hvt
  unfold checkTypes at h
  have hin := asCheck_ok h
  obtain ⟨_, _, hin⟩ := bind_ok hin
  obtain ⟨_, _, hin⟩ := bind_ok hin
  obtain ⟨_, _, hin⟩ := bind_ok hin
  obtain ⟨_, hb, _⟩ := bind_ok hin
  intro b hb' r op hop
  have := checkAll_mem (checkAll_mem hb (Array.mem_toList_iff.mpr hb')) hop
  simp only [checkInstTypes] at this
  obtain ⟨t, ht, hrest⟩ := bind_ok this
  refine ⟨t, ht, ?_⟩
  by_cases hh : (f.valueTypes m)[r]? = some (some t)
  · exact hh
  · exfalso
    simp [hh, bind, Except.bind] at hrest

theorem origins_of {profile : ArtifactProfile} {label : String} {f : Func}
    (h : checkOrigins profile label f = .ok ()) : OriginsPresent profile f := by
  unfold checkOrigins at h
  intro b hb i hi hn
  have := checkAll_mem (checkAll_mem h (Array.mem_toList_iff.mpr hb)) hi
  simp only [checkOrigin] at this
  by_cases ho : i.origin.isSome = true
  · exact ho
  · have hno : i.origin.isNone = true := by simpa using ho
    simp [hn, hno, violation] at this

theorem within_of {f : Func} {what : String} {found declared : List Target}
    (h : f.targetsWithin what found declared = .ok ()) : ∀ t ∈ found, t ∈ declared := by
  intro t ht
  unfold Func.targetsWithin at h
  cases hf : found.find? (fun t => !declared.contains t) with
  | some u => rw [hf] at h; simp [throw, throwThe, MonadExceptOf.throw] at h
  | none =>
    have := List.find?_eq_none.mp hf t ht
    simpa using this

theorem flag_of {msg : String} {found declared : Bool}
    (h : Func.flagWithin msg found declared = .ok ()) : found = true → declared = true := by
  intro hf
  by_cases hd : declared = true
  · exact hd
  · simp [Func.flagWithin, hf, hd, throw, throwThe, MonadExceptOf.throw] at h

theorem within_of_closed {f : Func} {e : Core.Eff} (h : f.summaryClosed e = .ok ()) :
    EffectsWithin e f.summary := by
  unfold Func.summaryClosed at h
  unfold EffectsWithin
  cases hs : f.summary with
  | unknown => trivial
  | known s =>
    rw [hs] at h
    simp only [] at h
    obtain ⟨_, hu, h⟩ := bind_ok h
    obtain ⟨_, h1, h⟩ := bind_ok h
    obtain ⟨_, h2, h⟩ := bind_ok h
    obtain ⟨_, h3, h⟩ := bind_ok h
    obtain ⟨_, h4, h⟩ := bind_ok h
    obtain ⟨_, h5, h⟩ := bind_ok h
    obtain ⟨_, h6, h7⟩ := bind_ok h
    refine ⟨?_, within_of h1, within_of h2, within_of h3, within_of h4, within_of h5,
      flag_of h6, flag_of h7⟩
    cases hk : e.unknown with
    | false => rfl
    | true => simp [Func.noUnknownCallee, hk, throw, throwThe, MonadExceptOf.throw] at hu

theorem summary_of {m : Module} {res : Array (List RootRef)} {k : Nat} {f : Func}
    (hf : m.funcs[k]? = some f)
    (h : checkSummaryOf m m.implTypes res m.rootCount k = .ok ()) :
    EffectsWithin (f.effects m (f.provenance res (m.implTypes[k]?.getD #[]) m.rootCount)) f.summary := by
  unfold checkSummaryOf at h
  rw [hf] at h
  obtain ⟨_, _, h⟩ := bind_ok h
  exact within_of_closed (asCheck_ok h)

/-- **Acceptance by `validate`.** Every block of every function ends in exactly one
terminator; every defining instruction is typed by the typing rules from the types of
its operands; every instruction that can abort or stands for a statement has an origin;
and each implementation's summary contains the effects the analysis finds in its body.
Dominance, scope balance and reference lifetime are not consequences proved here. -/
theorem validate_sound (m : Module) (h : validate m = .ok ()) :
    (∀ f ∈ m.allFuncs, TerminatedBlocks f ∧ TypedDefs m f ∧ OriginsPresent m.profile f) ∧
    (∀ (k : Nat) (f : Func), m.funcs[k]? = some f →
      EffectsWithin (f.effects m (f.provenance (resultRoots m m.implTypes) (m.implTypes[k]?.getD #[])
        m.rootCount)) f.summary) := by
  obtain ⟨ht, hc, hs, ho⟩ := validate_stages h
  refine ⟨fun f hf => ?_, fun k f hk => ?_⟩
  · obtain ⟨i, hi, rfl, hvt⟩ := mem_infos hf
    exact ⟨terminated_of_cfg (checkAll_mem hc hi), typed_of_types hvt (checkAll_mem ht hi),
      origins_of (profile := m.profile) (checkAll_mem ho hi)⟩
  · have hlt : k ∈ List.range m.funcs.size := by
      simp only [List.mem_range]
      cases Nat.lt_or_ge k m.funcs.size with
      | inl hlt => exact hlt
      | inr hge => simp [Array.getElem?_eq_none hge] at hk
    exact summary_of hk (checkAll_mem hs hlt)

end Goose.GIR

namespace Goose.GIR

open Goose.Core

/-! ### Typed operands do not fault -/

/-- The cell of a value holds a value of the scalar type. -/
def CellOf (fr : Frame) (v : ValueId) : VTy → Prop
  | .data (.int t) => ∃ n, fr.vals[v]? = some (.val (.int t n))
  | .data .bool => ∃ b, fr.vals[v]? = some (.val (.bool b))
  | .data .unit => fr.vals[v]? = some (.val .unit)
  | _ => False

theorem valTy_of {env : TyEnv} {v : ValueId} {t : VTy} (h : env.valTy v = .ok t) :
    env.vals[v]? = some (some t) := by
  unfold TyEnv.valTy at h
  cases hv : env.vals[v]? with
  | none => simp [hv, tyErr] at h
  | some o =>
    cases o with
    | none => simp [hv, tyErr] at h
    | some u => simp [hv] at h; subst h; rfl

theorem dataTy_of {env : TyEnv} {v : ValueId} {t : Ty} (h : env.dataTy v = .ok t) :
    env.vals[v]? = some (some (.data t)) := by
  unfold TyEnv.dataTy at h
  obtain ⟨vt, hvt, h⟩ := bind_ok h
  cases vt with
  | data d =>
    simp only [pure, Except.pure] at h
    cases h
    exact valTy_of hvt
  | view m e => simp [tyErr] at h

theorem intTy_of {env : TyEnv} {v : ValueId} {t : IntTy} (h : env.intTy v = .ok t) :
    env.vals[v]? = some (some (.data (.int t))) := by
  unfold TyEnv.intTy at h
  obtain ⟨d, hd, h⟩ := bind_ok h
  cases d with
  | int u =>
    simp only [pure, Except.pure] at h
    cases h
    exact dataTy_of hd
  | _ => simp [tyErr] at h

theorem evalBin_error {p : NumProfile} {o : BinOp} {t : IntTy} {a b : Int} {k : NumAbort}
    (h : evalBin p o t a b = .error k) : o.mayAbort = true := by
  cases o <;> simp [evalBin, BinOp.mayAbort] at h ⊢

theorem evalUn_error {p : NumProfile} {o : UnOp} {t : IntTy} {a : Int} {k : NumAbort}
    (h : evalUn p o t a = .error k) : unMayAbort o = true := by
  cases o <;> simp [evalUn, unMayAbort] at h ⊢

theorem evalConv_error {p : NumProfile} {c : ConvKind} {s d : IntTy} {a : Int} {k : NumAbort}
    (h : evalConv p c s d a = .error k) : convMayAbort c = true := by
  cases c <;> simp [evalConv, convMayAbort] at h ⊢

/-- The cell holds a value of the type the validator derived for it. -/
def Typed (env : TyEnv) (fr : Frame) (v : ValueId) : Prop :=
  ∃ vt, env.vals[v]? = some (some vt) ∧ CellOf fr v vt

theorem typed_int {env : TyEnv} {fr : Frame} {v : ValueId} {t : IntTy}
    (hty : env.intTy v = .ok t) (h : Typed env fr v) : ∃ n, fr.vals[v]? = some (.val (.int t n)) := by
  obtain ⟨vt, hv, hc⟩ := h
  rw [intTy_of hty] at hv
  cases hv
  exact hc

theorem typed_bool {env : TyEnv} {fr : Frame} {v : ValueId}
    (hty : env.dataTy v = .ok .bool) (h : Typed env fr v) : ∃ b, fr.vals[v]? = some (.val (.bool b)) := by
  obtain ⟨vt, hv, hc⟩ := h
  rw [dataTy_of hty] at hv
  cases hv
  exact hc


/-- Running the operation finishes, or aborts with an origin. -/
def Safe (cx : FnCtx) (fr : Frame) (op : Op) : Prop :=
  ∀ s, (∃ x s1, execPure cx fr op s = .ok x s1) ∨ ∃ k o s1, execPure cx fr op s = .stop (.abort k o) s1

theorem cond_of_unless {c : Bool} {msg : String}
    (h : (if c = true then pure () else tyErr msg : TyR Unit) = .ok ()) : c = true := by
  by_cases hc : c = true
  · exact hc
  · simp [hc, tyErr] at h

theorem bin_safe {cx : FnCtx} {fr : Frame} {env : TyEnv} {o : BinOp} {t : IntTy} {a b : ValueId}
    {org : Option OriginId} {r : VTy}
    (hty : (Op.bin o t a b org).resultTy env = .ok r) (ha : Typed env fr a) (hb : Typed env fr b)
    (horg : o.mayAbort = true → org.isSome = true) : Safe cx fr (.bin o t a b org) := by
  unfold Op.resultTy at hty
  obtain ⟨x, hx, hty⟩ := bind_ok hty
  obtain ⟨y, hy, hty⟩ := bind_ok hty
  have hxy : (decide (x = t) && decide (y = t)) = true := by
    by_cases hc : (decide (x = t) && decide (y = t)) = true
    · exact hc
    · exfalso
      simp [hc, tyErr, bind, Except.bind] at hty
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hxy
  obtain ⟨rfl, rfl⟩ := hxy
  obtain ⟨n, hn⟩ := typed_int hx ha
  obtain ⟨m, hm⟩ := typed_int hy hb
  intro s
  simp only [execPure, getVal_of hn, getVal_of hm, Goose.Core.expectInt, Goose.Core.expectSameTy,
    ↓reduceIte, bind_assoc, pure_bind]
  cases hev : evalBin cx.cfg.profile o y n m with
  | ok v => left; exact ⟨_, _, rfl⟩
  | error k =>
    right
    cases org with
    | none => simp [evalBin_error hev] at horg
    | some o' => exact ⟨_, _, _, rfl⟩


theorem un_safe {cx : FnCtx} {fr : Frame} {env : TyEnv} {o : UnOp} {t : IntTy} {a : ValueId}
    {org : Option OriginId} {r : VTy}
    (hty : (Op.un o t a org).resultTy env = .ok r) (ha : Typed env fr a)
    (horg : unMayAbort o = true → org.isSome = true) : Safe cx fr (.un o t a org) := by
  unfold Op.resultTy at hty
  obtain ⟨x, hx, hty⟩ := bind_ok hty
  have hxt : x = t := by
    by_cases hc : x = t
    · exact hc
    · exfalso
      simp [hc, tyErr, bind, Except.bind] at hty
  subst hxt
  obtain ⟨n, hn⟩ := typed_int hx ha
  intro s
  simp only [execPure, getVal_of hn, Goose.Core.expectInt, bind_assoc, pure_bind]
  cases hev : evalUn cx.cfg.profile o x n with
  | ok v => left; exact ⟨_, _, rfl⟩
  | error k =>
    right
    cases org with
    | none => simp [evalUn_error hev] at horg
    | some o' => exact ⟨_, _, _, rfl⟩

theorem cmp_safe {cx : FnCtx} {fr : Frame} {env : TyEnv} {o : CmpOp} {t : IntTy} {a b : ValueId}
    {r : VTy} (hty : (Op.cmp o t a b).resultTy env = .ok r) (ha : Typed env fr a)
    (hb : Typed env fr b) : Safe cx fr (.cmp o t a b) := by
  unfold Op.resultTy at hty
  obtain ⟨x, hx, hty⟩ := bind_ok hty
  obtain ⟨y, hy, hty⟩ := bind_ok hty
  have hxy : (decide (x = t) && decide (y = t)) = true := by
    by_cases hc : (decide (x = t) && decide (y = t)) = true
    · exact hc
    · exfalso
      simp [hc, tyErr, bind, Except.bind] at hty
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hxy
  obtain ⟨rfl, rfl⟩ := hxy
  obtain ⟨n, hn⟩ := typed_int hx ha
  obtain ⟨m, hm⟩ := typed_int hy hb
  intro s
  simp only [execPure, getVal_of hn, getVal_of hm, Goose.Core.expectComparable, Goose.Core.expectSameTy,
    ↓reduceIte, bind_assoc, pure_bind]
  left
  exact ⟨_, _, rfl⟩

theorem boolNot_safe {cx : FnCtx} {fr : Frame} {env : TyEnv} {a : ValueId} {r : VTy}
    (hty : (Op.boolNot a).resultTy env = .ok r) (ha : Typed env fr a) : Safe cx fr (.boolNot a) := by
  unfold Op.resultTy at hty
  obtain ⟨x, hx, hty⟩ := bind_ok hty
  have hxb : x = .bool := by
    by_cases hc : x = .bool
    · exact hc
    · exfalso
      simp [hc, tyErr, bind, Except.bind] at hty
  subst hxb
  obtain ⟨b, hb⟩ := typed_bool hx ha
  intro s
  simp only [execPure, getVal_of hb, Goose.Core.expectBool, bind_assoc, pure_bind]
  left
  exact ⟨_, _, rfl⟩

theorem conv_safe {cx : FnCtx} {fr : Frame} {env : TyEnv} {k : ConvKind} {src dst : IntTy}
    {a : ValueId} {org : Option OriginId} {r : VTy}
    (hty : (Op.conv k src dst a org).resultTy env = .ok r) (ha : Typed env fr a)
    (horg : convMayAbort k = true → org.isSome = true) : Safe cx fr (.conv k src dst a org) := by
  unfold Op.resultTy at hty
  obtain ⟨x, hx, hty⟩ := bind_ok hty
  have hxs : x = src := by
    by_cases hc : x = src
    · exact hc
    · exfalso
      simp [hc, tyErr, bind, Except.bind] at hty
  subst hxs
  obtain ⟨n, hn⟩ := typed_int hx ha
  intro s
  simp only [execPure, getVal_of hn, Goose.Core.expectInt, bind_assoc, pure_bind]
  cases hev : evalConv cx.cfg.profile k x dst n with
  | ok v => left; exact ⟨_, _, rfl⟩
  | error e =>
    right
    cases org with
    | none => simp [evalConv_error hev] at horg
    | some o' => exact ⟨_, _, _, rfl⟩


/-- The operations the typed-operand theorem covers: constants, integer arithmetic, comparison,
boolean negation and integer conversion. -/
def scalarOp : Op → Bool
  | .constInt .. | .constBool _ | .constUnit | .bin .. | .un .. | .cmp .. | .boolNot _ | .conv .. => true
  | _ => false

/-- **Typed operands do not fault.** In an accepted module, every scalar instruction run on a
frame whose operand cells hold values of the types the validator derived either finishes or
aborts at an origin: it never faults on a mismatched shape, an unbound operand or a missing
origin. -/
theorem validated_scalar_safe (m : Module) (h : validate m = .ok ()) :
    ∀ f ∈ m.allFuncs, ∀ b ∈ f.blocks, ∀ r op, Inst.def r op ∈ b.insts → scalarOp op = true →
      ∀ (cx : FnCtx) (fr : Frame),
        (∀ v ∈ op.uses, Typed { m.tyEnv f with vals := f.valueTypes m } fr v) → Safe cx fr op := by
  intro f hf b hb r op hop hsc cx fr hty
  obtain ⟨_, htd, hor⟩ := (validate_sound m h).1 f hf
  obtain ⟨t, hrt, _⟩ := htd b hb r op hop
  have hnorg := hor b hb (.def r op) hop
  cases op with
  | constInt t0 n =>
    intro s; left; exact ⟨_, _, rfl⟩
  | constBool bb => intro s; left; exact ⟨_, _, rfl⟩
  | constUnit => intro s; left; exact ⟨_, _, rfl⟩
  | bin o t0 a b' org =>
    exact bin_safe hrt (hty a (by simp [Op.uses])) (hty b' (by simp [Op.uses]))
      (fun hm => by
        have hneeds : Inst.needsOriginIn m.profile (.def r (.bin o t0 a b' org)) = true := by
          simpa [Inst.needsOriginIn, Inst.needsOrigin] using hm
        simpa [Inst.origin, Op.origin] using hnorg hneeds)
  | un o t0 a org =>
    exact un_safe hrt (hty a (by simp [Op.uses]))
      (fun hm => by
        have hneeds : Inst.needsOriginIn m.profile (.def r (.un o t0 a org)) = true := by
          simpa [Inst.needsOriginIn, Inst.needsOrigin] using hm
        simpa [Inst.origin, Op.origin] using hnorg hneeds)
  | cmp o t0 a b' => exact cmp_safe hrt (hty a (by simp [Op.uses])) (hty b' (by simp [Op.uses]))
  | boolNot a => exact boolNot_safe hrt (hty a (by simp [Op.uses]))
  | conv k s0 d a org =>
    exact conv_safe hrt (hty a (by simp [Op.uses]))
      (fun hm => by
        have hneeds : Inst.needsOriginIn m.profile (.def r (.conv k s0 d a org)) = true := by
          simpa [Inst.needsOriginIn, Inst.needsOrigin] using hm
        simpa [Inst.origin, Op.origin] using hnorg hneeds)
  | _ => simp [scalarOp] at hsc

end Goose.GIR
