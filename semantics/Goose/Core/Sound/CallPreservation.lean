import Goose.Core.Sound.Protection
import Goose.Core.Sound.Retain

/-!
Calls preserve the caller's demanded bindings and the values already sampled
by surrounding computations. Shrink may invalidate other interior locations.
-/

namespace Goose.Core.Sound
open Goose.Core Goose.Proofs.Memory

/-- A demanded binding remains present with its declared type. Its value may
change through a typed write, owner mutation or permitted slice rebinding. -/
def PreservesRootTypes (m : Module) (G : Nat)
    (observed : RootInst → Ty → Prop) (s s' : Store) : Prop :=
  ∀ r T, observed r T →
    ∀ v, s.roots[r]? = some v → HasTy m G s v T →
      ∃ v', s'.roots[r]? = some v' ∧ HasTy m G s' v' T

theorem PreservesRootTypes.refl {m : Module} {G : Nat}
    {observed : RootInst → Ty → Prop} (s : Store) :
    PreservesRootTypes m G observed s s :=
  fun _ _ _ v hv ht => ⟨v, hv, ht⟩

theorem PreservesRootTypes.trans {m : Module} {G : Nat}
    {observed : RootInst → Ty → Prop} {s₀ s₁ s₂ : Store}
    (h₁ : PreservesRootTypes m G observed s₀ s₁)
    (h₂ : PreservesRootTypes m G observed s₁ s₂) :
    PreservesRootTypes m G observed s₀ s₂ := by
  intro r T hr v hv ht
  obtain ⟨v₁, hv₁, ht₁⟩ := h₁ r T hr v hv ht
  exact h₂ r T hr v₁ hv₁ ht₁

/-- Preserving a larger demand also preserves any subset needed afterward. -/
theorem PreservesRootTypes.restrict {m : Module} {G : Nat}
    {observed subset : RootInst → Ty → Prop} {s s' : Store}
    (h : PreservesRootTypes m G observed s s')
    (hsub : ∀ r T, subset r T → observed r T) :
    PreservesRootTypes m G subset s s' :=
  fun r T hr => h r T (hsub r T hr)

/-- A sampled operand keeps its own typing, even when a variable that once
held it is rebound. This observes the value rather than its former holder. -/
def PreservesValues (m : Module) (G : Nat)
    (observed : Val → Ty → Prop) (s s' : Store) : Prop :=
  ∀ v T, observed v T → HasTy m G s v T → HasTy m G s' v T

theorem PreservesValues.refl {m : Module} {G : Nat}
    {observed : Val → Ty → Prop} (s : Store) : PreservesValues m G observed s s :=
  fun _ _ _ h => h

theorem PreservesValues.trans {m : Module} {G : Nat}
    {observed : Val → Ty → Prop} {s₀ s₁ s₂ : Store}
    (h₁ : PreservesValues m G observed s₀ s₁)
    (h₂ : PreservesValues m G observed s₁ s₂) :
    PreservesValues m G observed s₀ s₂ :=
  fun v T hv ht => h₂ v T hv (h₁ v T hv ht)

/-- Only operands still retained by the surrounding computation need typing. -/
theorem PreservesValues.restrict {m : Module} {G : Nat}
    {observed subset : Val → Ty → Prop} {s s' : Store}
    (h : PreservesValues m G observed s s')
    (hsub : ∀ v T, subset v T → observed v T) : PreservesValues m G subset s s' :=
  fun v T hv => h v T (hsub v T hv)

/-- Bindings and sampled values are separate observations: writes may change
the former while the latter must remain usable with the same runtime value. -/
structure Observation where
  roots : RootInst → Ty → Prop
  values : Val → Ty → Prop

/-- A computation with no inherited caller bindings or sampled operands. -/
def Observation.empty : Observation :=
  ⟨fun _ _ => False, fun _ _ => False⟩

/-- A nested call inherits its caller's observations as well as observations
already inherited by that caller. Both sets must remain usable. -/
def Observation.union (a b : Observation) : Observation :=
  ⟨fun r T => a.roots r T ∨ b.roots r T, fun v T => a.values v T ∨ b.values v T⟩

/-- Content annotations may include roots that cannot hold a resizable owner.
The declaration types observed at call entry classify local storage throughout
the call; globals use their module declarations. -/
def OwnerCap (m : Module) (observation : Observation) : RootInst → Prop
  | .global g => ∃ gl, m.globals[g]? = some gl ∧
      ∃ E, gl.ty = .grow E ∨ gl.ty = .growshrink E
  | r@(.local ..) => ∃ T, observation.roots r T ∧
      ∃ E, T = .grow E ∨ T = .growshrink E

theorem OwnerCap.mono {m : Module} {observation observation' : Observation}
    (included : ∀ r T, observation.roots r T → observation'.roots r T)
    {r : RootInst} (capability : OwnerCap m observation r) :
    OwnerCap m observation' r := by
  cases r with
  | global g => exact capability
  | «local» a si x =>
    obtain ⟨T, observed, owner⟩ := capability
    exact ⟨T, included _ T observed, owner⟩

/-- Every possible parameter root has an external storage classification.
Extra annotation roots may be absent, but cannot become new external bindings.
Inherited slice holders use their separate slice invariant; other reference
roots may be harmless extras in a returned value's declared roots. -/
def ClassifiedParameters (m : Module) (P : Nat → RootInst → Prop)
    (D : RootInst → Ty → Prop) (observation : Observation) (store : Store) : Prop :=
  ∀ i r, P i r → match r with
    | .global g => ∃ gl, m.globals[g]? = some gl
    | r@(.local ..) => (∃ T, observation.roots r T) ∨ (∃ E, D r E) ∨
        (∃ v, store.roots[r]? = some v ∧ IsRef v) ∨ store.roots[r]? = none

theorem ClassifiedParameters.advance {m : Module} {P : Nat → RootInst → Prop}
    {D : RootInst → Ty → Prop} {observation : Observation} {s s' : St}
    {instances : List Nat}
    (classified : ClassifiedParameters m P D observation s.store)
    (footprint : Footprint instances (fun r => ∃ E, D r E) s s')
    (outside : ∀ i a si x, P i (.local a si x) → si ∉ instances) :
    ClassifiedParameters m P D observation s'.store := by
  intro i r hr
  cases r with
  | global g => exact classified i _ hr
  | «local» a si x =>
    rcases classified i _ hr with observed | slices | ⟨v, present, reference⟩ | absent
    · exact Or.inl observed
    · exact Or.inr (Or.inl slices)
    · by_cases slice : ∃ E, D (.local a si x) E
      · exact Or.inr (Or.inl slice)
      · refine Or.inr (Or.inr (Or.inl ⟨v, ?_, reference⟩))
        exact footprint.keep _ v present reference (by
          intro a' si' x' equal
          cases equal
          exact outside i _ _ _ hr) slice
    · right; right; right
      cases hv : s'.store.roots[RootInst.local a si x]? with
      | none => rfl
      | some v => exact False.elim ((footprint.dom _ (by simp [hv])) absent)

theorem ClassifiedParameters.mono {m : Module} {P P' : Nat → RootInst → Prop}
    {D D' : RootInst → Ty → Prop} {observation observation' : Observation} {store : Store}
    (classified : ClassifiedParameters m P D observation store)
    (parameters : ∀ i r, P' i r → P i r)
    (roots : ∀ r T, observation.roots r T → observation'.roots r T)
    (slices : ∀ r E, D r E → D' r E) :
    ClassifiedParameters m P' D' observation' store := by
  intro i r hr
  cases r with
  | global g => exact classified i _ (parameters i _ hr)
  | «local» a si x =>
    rcases classified i _ (parameters i _ hr) with ⟨T, observed⟩ | ⟨E, slice⟩ | reference | absent
    · exact Or.inl ⟨T, roots _ T observed⟩
    · exact Or.inr (Or.inl ⟨E, slices _ E slice⟩)
    · exact Or.inr (Or.inr (Or.inl reference))
    · exact Or.inr (Or.inr (Or.inr absent))

theorem Frame.classifiedParameters_advance {m : Module} {W : World} {tenv : TEnv}
    {penv : PEnv} {env : Env} {s s' : St} {future : List VarId}
    {observation : Observation}
    (frame : Frame m W tenv penv env s future)
    (classified : ClassifiedParameters m W.P W.D observation s.store)
    (footprint : Footprint (insts env) (Dset W) s s') :
    ClassifiedParameters m W.P W.D observation s'.store := by
  apply classified.advance footprint
  intro i a si x parameter member
  obtain ⟨scope, present, instanceEq⟩ := List.mem_map.1 member
  have below := (frame.below scope present).1
  rw [instanceEq] at below
  exact (Nat.not_le_of_gt (frame.pAge i a si x parameter)) below

theorem ClassifiedParameters.advanceS {m : Module} {W : World} {tenv : TEnv}
    {penv : PEnv} {env : Env} {s s' : St} {future : List VarId}
    {observation : Observation}
    (classified : ClassifiedParameters m W.P W.D observation s.store)
    (frame : Frame m W tenv penv env s future)
    (footprint : FootprintS env (Dset W) s s') :
    ClassifiedParameters m W.P W.D observation s'.store := by
  intro i r hr
  cases r with
  | global g => exact classified i _ hr
  | «local» a si x =>
    rcases classified i _ hr with observed | slices | ⟨v, present, reference⟩ | absent
    · exact Or.inl observed
    · exact Or.inr (Or.inl slices)
    · by_cases slice : Dset W (.local a si x)
      · exact Or.inr (Or.inl slice)
      · refine Or.inr (Or.inr (Or.inl ⟨v, ?_, reference⟩))
        apply footprint.keep _ v present reference ?_ slice
        intro a' si' x' equal member
        cases equal
        obtain ⟨scope, present, instanceEq⟩ := List.mem_map.1 member
        have below := (frame.below scope present).1
        rw [instanceEq] at below
        exact (Nat.not_le_of_gt (frame.pAge i _ _ _ hr)) below
    · right; right; right
      cases hv : s'.store.roots[RootInst.local a si x]? with
      | none => rfl
      | some v =>
        have present : s'.store.roots[RootInst.local a si x]? ≠ none := by simp [hv]
        rcases footprint.dom _ present with old | ⟨y, lv, top, rest, scopes, lookup, equal⟩
        · exact False.elim (old absent)
        · cases equal
          have below := (frame.below (lv.scope, si) (by simp [scopes])).1
          exact False.elim ((Nat.not_le_of_gt (frame.pAge i _ _ _ hr)) below)

/-- An inherited observation carries full declared typing, which held-value
validity alone cannot establish for scalars, owners or typed references. -/
structure Observed (m : Module) (G : Nat) (observation : Observation) (s : Store) : Prop where
  roots : ∀ r T, observation.roots r T →
    ∃ v, s.roots[r]? = some v ∧ HasTy m G s v T
  values : ∀ v T, observation.values v T → HasTy m G s v T

theorem Observed.empty (m : Module) (G : Nat) (s : Store) :
    Observed m G Observation.empty s :=
  ⟨fun _ _ h => False.elim h, fun _ _ h => False.elim h⟩

/-- Dropping observations leaves the typing of all remaining observations. -/
theorem Observed.restrict {m : Module} {G : Nat} {o subset : Observation} {s : Store}
    (h : Observed m G o s)
    (hroots : ∀ r T, subset.roots r T → o.roots r T)
    (hvalues : ∀ v T, subset.values v T → o.values v T) : Observed m G subset s :=
  ⟨fun r T hr => h.roots r T (hroots r T hr),
    fun v T hv => h.values v T (hvalues v T hv)⟩

theorem Observed.union {m : Module} {G : Nat} {a b : Observation} {s : Store}
    (ha : Observed m G a s) (hb : Observed m G b s) : Observed m G (a.union b) s :=
  ⟨fun r T hr => hr.elim (ha.roots r T) (hb.roots r T),
    fun v T hv => hv.elim (ha.values v T) (hb.values v T)⟩

/-- The same caller observations can be threaded through a callee's changing
local demand when each transition preserves their bindings and operands. -/
theorem Observed.advance {m : Module} {G : Nat} {observation : Observation} {s s' : Store}
    (h : Observed m G observation s)
    (hroots : PreservesRootTypes m G observation.roots s s')
    (hvalues : PreservesValues m G observation.values s s') :
    Observed m G observation s' := by
  constructor
  · intro r T hr
    obtain ⟨v, hv, ht⟩ := h.roots r T hr
    exact hroots r T hr v hv ht
  · intro v T hv
    exact hvalues v T hv (h.values v T hv)

private theorem HasTy.resizable_ownerTy {m : Module} {G : Nat} {store : Store}
    {element : Ty} {values : Array Val} {T : Ty}
    (typed : HasTy m G store (.resizable element values) T) :
    ∃ E, T = .grow E ∨ T = .growshrink E := by
  cases T <;> simp_all [HasTy, FlatTy]

theorem ClassifiedParameters.localOwner {m : Module} {G : Nat}
    {P : Nat → RootInst → Prop} {D : RootInst → Ty → Prop}
    {observation : Observation} {store : Store} {a : ActId} {si : ScopeInst}
    {x : VarId} {i : Nat} {E : Ty}
    (classified : ClassifiedParameters m P D observation store)
    (observed : Observed m G observation store)
    (slices : ∀ r E, D r E → ∃ v, store.roots[r]? = some v ∧
      HasTy m G store v (.slice .mutable E))
    (parameter : P i (.local a si x))
    (owner : LocTy store ⟨.local a si x, []⟩ (.grow E)) :
    OwnerCap m observation (.local a si x) := by
  obtain ⟨v, hread, hflat⟩ := owner
  obtain ⟨stored, hstored, hget⟩ := (read_ok_iff _ _ _).1 hread
  simp only [get_nil, Option.some.injEq] at hget
  subst v
  cases stored <;> simp only [FlatTy] at hflat
  rename_i element values
  rcases classified i _ parameter with ⟨T, hT⟩ | ⟨sliceE, hD⟩ | ⟨value, hv, reference⟩ | absent
  · obtain ⟨value, hv, ht⟩ := observed.roots _ T hT
    rw [hstored] at hv
    cases hv
    exact ⟨T, hT, ht.resizable_ownerTy⟩
  · obtain ⟨value, hv, ht⟩ := slices _ sliceE hD
    rw [hstored] at hv
    cases hv
    simp [HasTy] at ht
  · rw [hstored] at hv
    cases hv
    simp [IsRef] at reference
  · rw [hstored] at absent
    cases absent

theorem OwnerCap.globalOfLocTy {m : Module} {G : Nat} {observation : Observation}
    {state : St} {demand : RootInst → Prop} {g : Nat} {E : Ty} {gl : Global}
    (invariant : StoreInv m G state demand)
    (declaration : m.globals[g]? = some gl) (initialized : g < G)
    (owner : LocTy state.store ⟨.global g, []⟩ (.grow E)) :
    OwnerCap m observation (.global g) := by
  obtain ⟨v, hread, hflat⟩ := owner
  obtain ⟨w, hread', hflat'⟩ := invariant.globals g gl initialized declaration
  rw [hread] at hread'
  cases hread'
  cases v <;> simp only [FlatTy] at hflat
  rename_i element values
  refine ⟨gl, declaration, ?_⟩
  cases ht : gl.ty <;> simp_all [FlatTy]

theorem ClassifiedParameters.globalOwner {m : Module} {G : Nat}
    {P : Nat → RootInst → Prop} {D : RootInst → Ty → Prop} {observation : Observation}
    {state : St} {demand : RootInst → Prop} {i g : Nat} {E : Ty}
    (classified : ClassifiedParameters m P D observation state.store)
    (invariant : StoreInv m G state demand)
    (initialized : g < G) (parameter : P i (.global g))
    (owner : LocTy state.store ⟨.global g, []⟩ (.grow E)) :
    OwnerCap m observation (.global g) := by
  obtain ⟨gl, declaration⟩ := classified i _ parameter
  exact OwnerCap.globalOfLocTy invariant declaration initialized owner

theorem OwnerCap.not_localLimited {m : Module} {G : Nat}
    {observation : Observation} {store : Store} {a : ActId} {si : ScopeInst}
    {x : VarId} {E : Ty} {capacity : Nat}
    (observed : Observed m G observation store)
    (limited : LocTy store ⟨.local a si x, []⟩ (.limited E capacity)) :
    ¬ OwnerCap m observation (.local a si x) := by
  obtain ⟨v, hread, hflat⟩ := limited
  obtain ⟨stored, hstored, hget⟩ := (read_ok_iff _ _ _).1 hread
  simp only [get_nil, Option.some.injEq] at hget
  subst v
  cases stored <;> simp only [FlatTy] at hflat
  intro capability
  obtain ⟨T, hT, element, howner⟩ := capability
  obtain ⟨value, hv, ht⟩ := observed.roots _ T hT
  rw [hstored] at hv
  cases hv
  rcases howner with rfl | rfl <;> simp [HasTy, FlatTy] at ht

theorem OwnerCap.not_globalLimited {m : Module} {G : Nat} {observation : Observation}
    {state : St} {demand : RootInst → Prop} {g : Nat} {gl : Global}
    {E : Ty} {capacity : Nat}
    (invariant : StoreInv m G state demand)
    (declaration : m.globals[g]? = some gl) (initialized : g < G)
    (limited : LocTy state.store ⟨.global g, []⟩ (.limited E capacity)) :
    ¬ OwnerCap m observation (.global g) := by
  obtain ⟨v, hread, hflat⟩ := limited
  obtain ⟨w, hread', hflat'⟩ := invariant.globals g gl initialized declaration
  rw [hread] at hread'
  cases hread'
  cases v <;> simp only [FlatTy] at hflat
  intro capability
  obtain ⟨other, hother, element, howner⟩ := capability
  rw [declaration] at hother
  cases hother
  rcases howner with ht | ht <;> rw [ht] at hflat' <;> simp [FlatTy] at hflat'

/-- Inherited roots precede the callee's first scope instance. Globals survive
every local scope, while local roots must belong to an earlier instance. -/
def BeforeBase (base : Nat) : RootInst → Prop
  | .global _ => True
  | .local _ si _ => si < base

theorem BeforeBase.mono {base base' : Nat} {r : RootInst}
    (hbase : base ≤ base') (h : BeforeBase base r) : BeforeBase base' r := by
  cases r with
  | global _ => trivial
  | «local» _ si _ => exact Nat.lt_of_lt_of_le h hbase

/-- Globals remain live independently of local caller demand. Observed local
bindings are live even when the callee has no variable naming them. -/
def ObservationDemand (o : Observation) : RootInst → Prop
  | .global _ => True
  | r@(.local ..) => ∃ T, o.roots r T

/-- Caller observations must outlive the callee and their interior aliases
must avoid the explicitly chosen shrink footprint. Full typing alone does not
protect a newly rebound reference whose runtime targets have changed. -/
structure ObservedSafe (m : Module) (W : World) (shrinking : RootInst → Prop)
    (o : Observation) (s : Store) : Prop where
  typed : Observed m W.G o s
  rootsOlder : ∀ r T, o.roots r T → BeforeBase W.base r
  valuesOlder : ∀ v T, o.values v T → ∀ r, Targets v r → BeforeBase W.base r
  rootsProtected : ∀ r T v, o.roots r T → s.roots[r]? = some v →
    T.interiorTarget?.isSome = true →
    ∀ target, Targets v target → ¬ shrinking target
  valuesProtected : ∀ v T, o.values v T → T.interiorTarget?.isSome = true →
    ∀ target, Targets v target → ¬ shrinking target

theorem ObservedSafe.empty (m : Module) (W : World) (shrinking : RootInst → Prop) (s : Store) :
    ObservedSafe m W shrinking Observation.empty s :=
  ⟨Observed.empty _ _ _, fun _ _ h => False.elim h, fun _ _ h => False.elim h,
    fun _ _ _ h => False.elim h, fun _ _ h => False.elim h⟩

/-- Restriction keeps both typing and the age and protection obligations of
the bindings and sampled operands still required by the caller. -/
theorem ObservedSafe.restrict {m : Module} {W : World} {o subset : Observation} {s : Store}
    {shrinking : RootInst → Prop} (h : ObservedSafe m W shrinking o s)
    (hroots : ∀ r T, subset.roots r T → o.roots r T)
    (hvalues : ∀ v T, subset.values v T → o.values v T) : ObservedSafe m W shrinking subset s :=
  ⟨h.typed.restrict hroots hvalues,
    fun r T hr => h.rootsOlder r T (hroots r T hr),
    fun v T hv => h.valuesOlder v T (hvalues v T hv),
    fun r T v hr => h.rootsProtected r T v (hroots r T hr),
    fun v T hv => h.valuesProtected v T (hvalues v T hv)⟩

theorem ObservedSafe.union {m : Module} {W : World} {a b : Observation} {s : Store}
    {shrinking : RootInst → Prop}
    (ha : ObservedSafe m W shrinking a s) (hb : ObservedSafe m W shrinking b s) :
    ObservedSafe m W shrinking (a.union b) s :=
  ⟨ha.typed.union hb.typed,
    fun r T hr => hr.elim (ha.rootsOlder r T) (hb.rootsOlder r T),
    fun v T hv => hv.elim (ha.valuesOlder v T) (hb.valuesOlder v T),
    fun r T v hr => hr.elim (ha.rootsProtected r T v) (hb.rootsProtected r T v),
    fun v T hv => hv.elim (ha.valuesProtected v T) (hb.valuesProtected v T)⟩

/-- A later activation base preserves the age of inherited observations while
their typing and protection against the chosen shrink footprint stay fixed. -/
theorem ObservedSafe.base_mono {m : Module} {W : World} {o : Observation} {s : Store}
    {shrinking : RootInst → Prop} {base : Nat}
    (h : ObservedSafe m W shrinking o s) (hbase : W.base ≤ base) :
    ObservedSafe m { W with base := base } shrinking o s :=
  { h with
    rootsOlder := fun r T hr => BeforeBase.mono hbase (h.rootsOlder r T hr)
    valuesOlder := fun v T hv r ht => BeforeBase.mono hbase (h.valuesOlder v T hv r ht) }

/-- Protection against a larger shrink footprint also excludes every root in
a narrower footprint, independently of the world's parameter interpretation. -/
theorem ObservedSafe.weakenShrinking {m : Module} {W : World} {o : Observation} {s : Store}
    {shrinking shrinking' : RootInst → Prop} (h : ObservedSafe m W shrinking o s)
    (hmay : ∀ r, shrinking' r → shrinking r) : ObservedSafe m W shrinking' o s :=
  { h with
    rootsProtected := fun r T v hr hv hi target ht hshrink =>
      h.rootsProtected r T v hr hv hi target ht (hmay target hshrink)
    valuesProtected := fun v T hv hi target ht hshrink =>
      h.valuesProtected v T hv hi target ht (hmay target hshrink) }

private theorem HasTy.interior_isRef {m : Module} {G : Nat} {store : Store}
    {v : Val} {T : Ty} (typed : HasTy m G store v T)
    (interior : T.interiorTarget?.isSome = true) : IsRef v := by
  cases T <;> simp only [Ty.interiorTarget?] at interior
  case ref mu target =>
    obtain ⟨location, rfl, _⟩ := typed
    trivial
  case slice mu element =>
    obtain ⟨location, start, count, rfl, _⟩ := typed
    trivial
  all_goals cases interior

theorem Frame.beforeBase_not_insts {m : Module} {W : World} {tenv : TEnv}
    {penv : PEnv} {env : Env} {s : St} {future : List VarId}
    (frame : Frame m W tenv penv env s future) {r : RootInst}
    (older : BeforeBase W.base r) :
    ∀ a si x, r = .local a si x → si ∉ insts env := by
  intro a si x equal member
  subst r
  obtain ⟨scope, present, instanceEq⟩ := List.mem_map.1 member
  have below := (frame.below scope present).1
  change si < W.base at older
  rw [instanceEq] at below
  exact (Nat.not_le_of_gt older) below

/-- A call may rebind inherited mutable slices, but every other older
reference observation keeps its original value. Rebound slices stay within
the caller's allowed content roots, which its whole computation protects. -/
theorem Frame.observedSafe_outerPreserved {m : Module} {W : World} {tenv : TEnv}
    {penv : PEnv} {env : Env} {s s' : St} {future : List VarId}
    {observation : Observation} {shrinking : RootInst → Prop}
    (frame : Frame m W tenv penv env s future)
    (hprotected : ShrinkProtected W.D W.A shrinking)
    (source : ObservedSafe m W shrinking observation s.store)
    (footprint : Footprint (insts env) (Dset W) s s')
    (roots : PreservesRootTypes m W.G observation.roots s.store s'.store)
    (values : PreservesValues m W.G observation.values s.store s'.store)
    (slices : ∀ r E, W.D r E → ∃ v, s'.store.roots[r]? = some v ∧
      HasTy m W.G s'.store v (.slice .mutable E) ∧
        ∀ target, Targets v target → W.A r target) :
    ObservedSafe m W shrinking observation s'.store := by
  refine ⟨source.typed.advance roots values, source.rootsOlder, source.valuesOlder, ?_,
    source.valuesProtected⟩
  intro r T v observed present interior target targetPresent
  by_cases demanded : Dset W r
  · obtain ⟨E, demanded⟩ := demanded
    obtain ⟨slice, slicePresent, _, allowed⟩ := slices r E demanded
    rw [present] at slicePresent
    cases slicePresent
    intro mayShrink
    exact hprotected r E target demanded (allowed target targetPresent) target mayShrink rfl
  · obtain ⟨original, originalPresent, originalTyped⟩ := source.typed.roots r T observed
    have kept := footprint.keep r original originalPresent
      (originalTyped.interior_isRef interior)
      (frame.beforeBase_not_insts (source.rootsOlder r T observed)) demanded
    rw [present] at kept
    cases kept
    exact source.rootsProtected r T v observed originalPresent interior target targetPresent

/-- Globals, observed caller bindings and inherited mutable slice holders
stay live while the callee's own local demand changes. -/
def CallDemand (observation : Observation) (D : RootInst → Ty → Prop) : RootInst → Prop :=
  fun r => (∃ g, r = RootInst.global g) ∨
    (∃ T, observation.roots r T) ∨ (∃ E, D r E)

/-- Removing inherited slice holders from call demand preserves the invariant
for all globals and observed caller bindings without rebuilding store facts. -/
theorem StoreInv.observationDemand {m : Module} {G : Nat} {s : St} {o : Observation}
    {D : RootInst → Ty → Prop} (h : StoreInv m G s (CallDemand o D)) :
    StoreInv m G s (ObservationDemand o) := by
  apply h.changeDemand
  intro r hr
  cases r with
  | global g => exact Or.inl (Or.inl ⟨g, rfl⟩)
  | «local» a si x => exact Or.inl (Or.inr (Or.inl hr))

/-- A caller frame already supplies global liveness and unconditional store
age and freshness. Explicit typing supplies validity for its inherited demand. -/
theorem Frame.callDemand {m : Module} {W : World} {tenv : TEnv} {penv : PEnv}
    {env : Env} {s : St} {future : List VarId} {observation : Observation}
    {D : RootInst → Ty → Prop}
    (frame : Frame m W tenv penv env s future)
    (observed : Observed m W.G observation s.store)
    (slices : ∀ r E, D r E →
      ∃ v, s.store.roots[r]? = some v ∧ HasTy m W.G s.store v (.slice .mutable E)) :
    StoreInv m W.G s (CallDemand observation D) := by
  refine ⟨?_, frame.inv.age, frame.inv.fresh, frame.inv.globals⟩
  intro r v hv hd
  rcases hd with ⟨g, rfl⟩ | ⟨T, hr⟩ | ⟨E, hr⟩
  · exact frame.inv.live _ v hv trivial
  · obtain ⟨v', hv', ht⟩ := observed.roots r T hr
    rw [hv] at hv'
    cases hv'
    exact ht.held
  · obtain ⟨v', hv', ht⟩ := slices r E hr
    rw [hv] at hv'
    cases hv'
    exact ht.held

/-- Caller demand covers continuation bindings, initialized value storage and
inherited mutable slice holders. Value storage keeps its declared type even
when later code uses it only through a reference or slice. -/
def CallerRootTypes (W : World) (tenv : TEnv) (env : Env)
    (source : Store) (future : List VarId) (r : RootInst) (T : Ty) : Prop :=
  ((∃ x lv si, x ∈ tenv.visible ∧ x ∈ future ∧
    env.vars[x]? = some lv ∧ env.scopes.lookup lv.scope = some si ∧
    r = RootInst.local env.act si x ∧ T = lv.ty) ∨
    (StorageRootTypes env r T ∧ source.roots[r]? ≠ none)) ∨
  (∃ E, W.D r E ∧ T = .slice .mutable E)

/-- A root preservation result also covers initialized value storage. Its
source-value premise establishes initialization without observing absent roots. -/
theorem CallerRootTypes.preservesStorage {m : Module} {W : World} {tenv : TEnv}
    {env : Env} {future : List VarId} {source target : Store}
    (h : PreservesRootTypes m W.G (CallerRootTypes W tenv env source future) source target) :
    PreservesRootTypes m W.G (StorageRootTypes env) source target := by
  intro r T hstorage v hv ht
  exact h r T (Or.inl (Or.inr ⟨hstorage, by simp [hv]⟩)) v hv ht

/-- A completed call preserves caller observations and its root footprint.
Typed interior locations that nobody observes may disappear during shrink. -/
structure CallTransition (m : Module) (G : Nat)
    (roots : RootInst → Ty → Prop) (values : Val → Ty → Prop)
    (mutableSlices : RootInst → Prop) (s s' : St) : Prop where
  footprint : Footprint [] mutableSlices s s'
  rootsTyped : PreservesRootTypes m G roots s.store s'.store
  valuesTyped : PreservesValues m G values s.store s'.store

theorem CallTransition.refl {m : Module} {G : Nat}
    {roots : RootInst → Ty → Prop} {values : Val → Ty → Prop}
    {mutableSlices : RootInst → Prop} (s : St) :
    CallTransition m G roots values mutableSlices s s :=
  ⟨Footprint.refl _ _ _, PreservesRootTypes.refl _, PreservesValues.refl _⟩

theorem CallTransition.trans {m : Module} {G : Nat}
    {roots : RootInst → Ty → Prop} {values : Val → Ty → Prop}
    {mutableSlices : RootInst → Prop} {s₀ s₁ s₂ : St}
    (h₁ : CallTransition m G roots values mutableSlices s₀ s₁)
    (h₂ : CallTransition m G roots values mutableSlices s₁ s₂) :
    CallTransition m G roots values mutableSlices s₀ s₂ :=
  ⟨h₁.footprint.trans h₂.footprint, h₁.rootsTyped.trans h₂.rootsTyped,
    h₁.valuesTyped.trans h₂.valuesTyped⟩

/-- A completed call also preserves any narrower set of caller observations. -/
theorem CallTransition.restrict {m : Module} {G : Nat}
    {roots roots' : RootInst → Ty → Prop} {values values' : Val → Ty → Prop}
    {mutableSlices : RootInst → Prop} {s s' : St}
    (h : CallTransition m G roots values mutableSlices s s')
    (hr : ∀ r T, roots' r T → roots r T)
    (hv : ∀ v T, values' v T → values v T) :
    CallTransition m G roots' values' mutableSlices s s' :=
  ⟨h.footprint, h.rootsTyped.restrict hr, h.valuesTyped.restrict hv⟩

section CallObservations
variable {m : Module}

private theorem AliasAt.limited_slice {W : World} {env : Env} {store : Store}
    {alias : RetainedAlias} {mu : Mutability} {element : Ty} {capacity : Nat}
    {location : Loc} {start len : Nat}
    (aliasType : alias.ty = .ref mu (.limited element capacity))
    (realized : AliasAt m W env store alias (.ref location))
    (physical : SliceTy store location start len element) :
    HasTy m W.G store (.slice location start len) (.slice .readOnly element) := by
  have typed := realized.1
  rw [aliasType] at typed
  obtain ⟨target, equal, ordinary | header⟩ := typed
  · have flat : element.flat = true := by
      simpa [Ty.refTarget, Ty.storable] using ordinary.1
    exact ⟨location, start, len, rfl, flat, physical⟩
  · simp [Ty.isSlice] at header

/-- Limited-owner aliases also retain physical runs sampled before their
visible length changes. These values are tied to the alias's declared element
type and its actual header realization. -/
def callRetainedValues (W : World) (env : Env) (retained : List RetainedAlias)
    (store : Store) (v : Val) (T : Ty) : Prop :=
  (∃ alias, alias ∈ retained ∧ T = alias.ty ∧ AliasAt m W env store alias v) ∨
  (∃ alias mu element capacity location start len,
    alias ∈ retained ∧ alias.ty = .ref mu (.limited element capacity) ∧
    AliasAt m W env store alias (.ref location) ∧ SliceTy store location start len element ∧
    v = .slice location start len ∧ T = .slice .readOnly element)

/-- A call observes continuation bindings and the values realizing retained
aliases at entry. Slice-reference aliases observe the stored slice contents;
their runtime reference to the header is not an interior slice value. -/
def callObservation (inherited : Observation) (W : World) (tenv : TEnv) (env : Env)
    (continuation : List VarId) (retained : List RetainedAlias) (store : Store) : Observation :=
  inherited.union ⟨CallerRootTypes W tenv env store continuation,
    callRetainedValues (m := m) W env retained store⟩

theorem callObservation_safe {W : World} {tenv : TEnv} {penv : PEnv} {env : Env}
    {s : St} {future continuation : List VarId} {retained : List RetainedAlias}
    {inherited : Observation} {shrinking : RootInst → Prop}
    (frame : Frame m W tenv penv env s future)
    (futureSubset : ∀ x, x ∈ continuation → x ∈ future)
    (outer : ObservedSafe m { W with base := s.nextScope } shrinking inherited s.store)
    (rootsProtected : ∀ r T v, CallerRootTypes W tenv env s.store continuation r T →
      s.store.roots[r]? = some v → T.interiorTarget?.isSome = true →
      ∀ target, Targets v target → ¬ shrinking target)
    (valuesProtected : ∀ v T, callRetainedValues (m := m) W env retained s.store v T →
      T.interiorTarget?.isSome = true → ∀ target, Targets v target → ¬ shrinking target) :
    ObservedSafe m { W with base := s.nextScope } shrinking
      (callObservation (m := m) inherited W tenv env continuation retained s.store) s.store := by
  have scopeMember {sc si : Nat} (lookup : env.scopes.lookup sc = some si) :
      (sc, si) ∈ env.scopes := by
    obtain ⟨before, after, equal, _⟩ := List.lookup_eq_some_iff.mp lookup
    rw [equal]
    exact List.mem_append_right _ List.mem_cons_self
  apply outer.union
  constructor
  · constructor
    · intro r T hr
      rcases hr with (⟨x, lv, si, hx, hf, hvar, hscope, rfl, rfl⟩ |
        ⟨⟨x, lv, si, hvar, hscope, rfl, hnonref, rfl⟩, hinitialized⟩) |
        ⟨element, hd, rfl⟩
      · obtain ⟨lv', si', v, hvar', hscope', _, hv, ht⟩ :=
          frame.vis x hx (futureSubset x hf)
        rw [hvar] at hvar'
        cases hvar'
        rw [hscope] at hscope'
        cases hscope'
        exact ⟨v, hv, ht⟩
      · have hstorage : StorageRootTypes env (.local env.act si x) lv.ty :=
          ⟨x, lv, si, hvar, hscope, rfl, hnonref, rfl⟩
        cases hv : s.store.roots[RootInst.local env.act si x]? with
        | none => exact False.elim (hinitialized hv)
        | some v =>
          simpa [hv] using
            (LocTy.hasTyRoot (m := m) (G := W.G) (frame.storage _ _ hstorage v hv) hnonref)
      · obtain ⟨v, hv, ht, _⟩ := frame.sa r element hd
        exact ⟨v, hv, ht⟩
    · intro v T hvalue
      rcases hvalue with ⟨alias, _, rfl, realized⟩ |
        ⟨alias, mu, element, capacity, location, start, len, _, aliasType, realized, physical,
          rfl, rfl⟩
      · exact realized.1
      · exact AliasAt.limited_slice aliasType realized physical
  · intro r T hr
    rcases hr with (⟨x, lv, si, _, _, _, hscope, rfl, _⟩ |
      ⟨⟨x, lv, si, _, hscope, rfl, _, _⟩, _⟩) | ⟨element, hd, _⟩
    · exact (frame.below _ (scopeMember hscope)).2
    · exact (frame.below _ (scopeMember hscope)).2
    · obtain ⟨a, si, x, rfl, hbefore⟩ := frame.dOut r element hd
      exact Nat.lt_of_lt_of_le hbefore frame.base_le
  · intro v T hvalue target htarget
    have roots : ∃ annotation, Gam env W.P annotation target := by
      rcases hvalue with ⟨alias, _, _, realized⟩ |
        ⟨alias, mu, element, capacity, location, start, len, _, _, realized, _, rfl, _⟩
      · exact ⟨alias.roots, realized.2 target htarget⟩
      · exact ⟨alias.roots, realized.2 target htarget⟩
    obtain ⟨annotation, roots⟩ := roots
    cases target with
    | global _ => trivial
    | «local» a si x =>
      obtain ⟨q, _, hq⟩ := roots
      cases q with
      | «local» y =>
        obtain ⟨lv, scope, _, hscope, equal⟩ := hq
        cases equal
        exact (frame.below _ (scopeMember hscope)).2
      | global g => cases hq
      | param i => exact Nat.lt_of_lt_of_le (frame.pAge i a si x hq) frame.base_le
  · exact rootsProtected
  · exact valuesProtected

theorem callObservation_retainsAliases {W : World} {tenv : TEnv} {env : Env}
    {continuation : List VarId} {retained : List RetainedAlias} {inherited : Observation}
    {s s' : Store}
    (values : PreservesValues m W.G
      (callObservation (m := m) inherited W tenv env continuation retained s).values s s') :
    RetainsAliases m W env s s' retained := by
  intro alias hmem
  constructor
  · intro v hvalue
    exact ⟨values v alias.ty (Or.inr (Or.inl ⟨alias, hmem, rfl, hvalue⟩)) hvalue.1, hvalue.2⟩
  · intro mu element capacity location start len aliasType realized physical
    have sourceTyped := AliasAt.limited_slice aliasType realized physical
    have targetTyped := values (.slice location start len) (.slice .readOnly element)
      (Or.inr (Or.inr ⟨alias, mu, element, capacity, location, start, len, hmem, aliasType,
        realized, physical, rfl, rfl⟩)) sourceTyped
    obtain ⟨target, first, count, equal, _, physical⟩ := targetTyped
    obtain ⟨rfl, rfl, rfl⟩ := Val.slice.inj equal
    exact physical


/-- Adding the caller's current bindings cannot give an older root a new owner
capability. The inherited mutable slice arm also grants no owner capability. -/
theorem OwnerCap.callObservation_beforeBase {W : World} {tenv : TEnv} {penv : PEnv}
    {env : Env} {s : St} {future continuation : List VarId}
    {retained : List RetainedAlias} {inherited : Observation} {root : RootInst}
    (frame : Frame m W tenv penv env s future)
    (before : BeforeBase W.base root)
    (capability : OwnerCap m
      (callObservation (m := m) inherited W tenv env continuation retained s.store) root) :
    OwnerCap m inherited root := by
  have scopeLower {sc si : Nat} (lookup : env.scopes.lookup sc = some si) : W.base ≤ si := by
    obtain ⟨earlier, later, equal, _⟩ := List.lookup_eq_some_iff.mp lookup
    apply (frame.below (sc, si) _).1
    rw [equal]
    exact List.mem_append_right _ List.mem_cons_self
  cases root with
  | global _ => exact capability
  | «local» a si x =>
    obtain ⟨T, observed, element, ownerType⟩ := capability
    rcases observed with inheritedRoot | callerRoot
    · exact ⟨T, inheritedRoot, element, ownerType⟩
    · rcases callerRoot with
        (⟨y, lv, instanceId, _, _, _, scope, equal, _⟩ |
          ⟨⟨y, lv, instanceId, _, scope, equal, _, _⟩, _⟩) | ⟨E, _, typeEq⟩
      · cases equal
        exact False.elim ((Nat.not_le_of_gt before) (scopeLower scope))
      · cases equal
        exact False.elim ((Nat.not_le_of_gt before) (scopeLower scope))
      · rw [typeEq] at ownerType
        rcases ownerType with ownerType | ownerType <;> cases ownerType

/-- An inherited mutable slice's allowed targets are older than the caller's
own active scope instances. -/
theorem Frame.allowed_beforeBase {W : World} {tenv : TEnv} {penv : PEnv}
    {env : Env} {s : St} {future : List VarId} {holder target : RootInst} {element : Ty}
    (frame : Frame m W tenv penv env s future)
    (slice : W.D holder element) (allowed : W.A holder target) :
    BeforeBase W.base target := by
  obtain ⟨activation, instanceId, variableId, equal, before⟩ := frame.dOut holder element slice
  have older := frame.aOlder holder target allowed
  rw [equal] at older
  cases target with
  | global _ => trivial
  | «local» _ scope _ =>
    change scope ≤ instanceId at older
    exact Nat.lt_of_le_of_lt older before

end CallObservations

end Goose.Core.Sound
