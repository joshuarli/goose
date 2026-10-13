import Goose.Core.Sound.Frame

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

/-- An inherited observation carries full declared typing, which held-value
validity alone cannot establish for scalars, owners or typed references. -/
structure Observed (m : Module) (G : Nat) (observation : Observation) (s : Store) : Prop where
  roots : ∀ r T, observation.roots r T →
    ∃ v, s.roots[r]? = some v ∧ HasTy m G s v T
  values : ∀ v T, observation.values v T → HasTy m G s v T

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

/-- Globals, observed caller bindings and inherited mutable slice holders
stay live while the callee's own local demand changes. -/
def CallDemand (observation : Observation) (D : RootInst → Ty → Prop) : RootInst → Prop :=
  fun r => (∃ g, r = RootInst.global g) ∨
    (∃ T, observation.roots r T) ∨ (∃ E, D r E)

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

/-- Caller demand covers visible future bindings and inherited mutable slice
holders. The latter stay usable even when no local variable names them. -/
def CallerRootTypes (W : World) (tenv : TEnv) (env : Env)
    (future : List VarId) (r : RootInst) (T : Ty) : Prop :=
  (∃ x lv si, x ∈ tenv.visible ∧ x ∈ future ∧
    env.vars[x]? = some lv ∧ env.scopes.lookup lv.scope = some si ∧
    r = RootInst.local env.act si x ∧ T = lv.ty) ∨
  (∃ E, W.D r E ∧ T = .slice .mutable E)

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

end Goose.Core.Sound
