import Goose.GIR.Validate

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

def OriginsPresent (f : Func) : Prop :=
  ∀ b ∈ f.blocks, ∀ i ∈ b.insts, i.needsOrigin = true → i.origin.isSome = true

/-- The effects are within what the summary declares. -/
def EffectsWithin (e : Core.Eff) (s : SummaryAnn) : Prop :=
  match s with
  | .unknown => True
  | .known sm =>
    e.unknown = false ∧
    (∀ t ∈ e.reads, t ∈ sm.reads) ∧ (∀ t ∈ e.writes, t ∈ sm.writes) ∧
    (∀ t ∈ e.grows, t ∈ sm.grows) ∧ (∀ t ∈ e.rebinds, t ∈ sm.rebinds) ∧
    (e.aborts = true → sm.aborts = true) ∧ (e.outputs = true → sm.outputs = true)

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
    (checkAll m.infos fun i => checkOrigins i.label i.f) = .ok () := by
  unfold validate at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, ht, h⟩ := bind_ok h
  obtain ⟨_, hc, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, hs, h⟩ := bind_ok h
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

theorem origins_of {label : String} {f : Func} (h : checkOrigins label f = .ok ()) : OriginsPresent f := by
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
    obtain ⟨_, h5, h6⟩ := bind_ok h
    refine ⟨?_, within_of h1, within_of h2, within_of h3, within_of h4, flag_of h5, flag_of h6⟩
    cases hk : e.unknown with
    | false => rfl
    | true => simp [Func.noUnknownCallee, hk, throw, throwThe, MonadExceptOf.throw] at hu

theorem summary_of {m : Module} {res : Array (List RootRef)} {k : Nat} {f : Func}
    (hf : m.funcs[k]? = some f)
    (h : checkSummaryOf m m.implTypes res m.rootCount k = .ok ()) :
    EffectsWithin (f.effects m (f.provenance res (m.implTypes[k]?.getD #[]) m.rootCount)) f.summary := by
  unfold checkSummaryOf at h
  rw [hf] at h
  exact within_of_closed (asCheck_ok h)

/-- **Acceptance by `validate`.** Every block of every function ends in exactly one
terminator; every defining instruction is typed by the typing rules from the types of
its operands; every instruction that can abort or stands for a statement has an origin;
and each implementation's summary contains the effects the analysis finds in its body.
Dominance, scope balance and reference lifetime are not consequences proved here. -/
theorem validate_sound (m : Module) (h : validate m = .ok ()) :
    (∀ f ∈ m.allFuncs, TerminatedBlocks f ∧ TypedDefs m f ∧ OriginsPresent f) ∧
    (∀ (k : Nat) (f : Func), m.funcs[k]? = some f →
      EffectsWithin (f.effects m (f.provenance (resultRoots m m.implTypes) (m.implTypes[k]?.getD #[])
        m.rootCount)) f.summary) := by
  obtain ⟨ht, hc, hs, ho⟩ := validate_stages h
  refine ⟨fun f hf => ?_, fun k f hk => ?_⟩
  · obtain ⟨i, hi, rfl, hvt⟩ := mem_infos hf
    exact ⟨terminated_of_cfg (checkAll_mem hc hi), typed_of_types hvt (checkAll_mem ht hi),
      origins_of (checkAll_mem ho hi)⟩
  · have hlt : k ∈ List.range m.funcs.size := by
      simp only [List.mem_range]
      cases Nat.lt_or_ge k m.funcs.size with
      | inl hlt => exact hlt
      | inr hge => simp [Array.getElem?_eq_none hge] at hk
    exact summary_of hk (checkAll_mem hs hlt)

end Goose.GIR
