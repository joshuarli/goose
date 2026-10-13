import Goose.Core.Sound.Frame

/-!
Retention relates one static alias to the same runtime value before and after
a store transition. Its algebra is independent of the operation that changed
the store.
-/

namespace Goose.Core.Sound
open Goose.Core Goose.Proofs.Memory

/-- A runtime value realizes an alias when its type and declared roots agree. -/
def AliasAt (m : Module) (W : World) (env : Env) (s : Store)
    (alias : RetainedAlias) (v : Val) : Prop :=
  HasTy m W.G s v alias.ty ∧
    ∀ r, Targets v r → Gam env W.P alias.roots r

/-- One alias keeps the same runtime realization across a store transition. -/
def RetainsAlias (m : Module) (W : World) (env : Env) (s s' : Store)
    (alias : RetainedAlias) : Prop :=
  ∀ v, AliasAt m W env s alias v → AliasAt m W env s' alias v

/-- Every alias in a list keeps its runtime realization across a transition. -/
def RetainsAliases (m : Module) (W : World) (env : Env) (s s' : Store)
    (aliases : List RetainedAlias) : Prop :=
  ∀ alias, alias ∈ aliases → RetainsAlias m W env s s' alias

theorem RetainsAlias.refl {m : Module} {W : World} {env : Env} {s : Store}
    {alias : RetainedAlias} : RetainsAlias m W env s s alias := by
  intro v h
  exact h

theorem RetainsAlias.trans {m : Module} {W : World} {env : Env} {s s' s'' : Store}
    {alias : RetainedAlias} (h₁ : RetainsAlias m W env s s' alias)
    (h₂ : RetainsAlias m W env s' s'' alias) : RetainsAlias m W env s s'' alias := by
  intro v h
  exact h₂ v (h₁ v h)

theorem RetainsAliases.refl {m : Module} {W : World} {env : Env} {s : Store}
    {aliases : List RetainedAlias} : RetainsAliases m W env s s aliases := by
  intro alias _
  exact RetainsAlias.refl

theorem RetainsAliases.trans {m : Module} {W : World} {env : Env} {s s' s'' : Store}
    {aliases : List RetainedAlias} (h₁ : RetainsAliases m W env s s' aliases)
    (h₂ : RetainsAliases m W env s' s'' aliases) :
    RetainsAliases m W env s s'' aliases := by
  intro alias hmem
  exact RetainsAlias.trans (h₁ alias hmem) (h₂ alias hmem)

/-- A retention proof for a larger list restricts to any sublist. -/
theorem RetainsAliases.subset {m : Module} {W : World} {env : Env} {s s' : Store}
    {aliases subset : List RetainedAlias} (h : RetainsAliases m W env s s' aliases)
    (hsub : ∀ alias, alias ∈ subset → alias ∈ aliases) :
    RetainsAliases m W env s s' subset := by
  intro alias hmem
  exact h alias (hsub alias hmem)

/-- Expression and argument values already carry the realization payload. -/
theorem AliasAt.ofValue {m : Module} {W : World} {env : Env} {s : Store}
    {alias : RetainedAlias} {v : Val}
    (hty : HasTy m W.G s v alias.ty)
    (hroots : ∀ r, Targets v r → Gam env W.P alias.roots r) :
    AliasAt m W env s alias v :=
  ⟨hty, hroots⟩

private theorem RootIn.root_ne_of_no_overlap {env : Env} {P : Nat → RootInst → Prop}
    {q q' : RootRef} {r r' : RootInst}
    (paramAway : ∀ i x lv si, env.vars[x]? = some lv → env.scopes.lookup lv.scope = some si →
      ¬ P i (.local env.act si x))
    (hdisjoint : rootsMayOverlap q q' = false)
    (hq : RootIn env P r q) (hq' : RootIn env P r' q') : r ≠ r' := by
  cases q with
  | «local» x =>
    cases q' with
    | «local» y =>
      change (x == y) = false at hdisjoint
      change (∃ lv si, env.vars[x]? = some lv ∧ env.scopes.lookup lv.scope = some si ∧
        r = .local env.act si x) at hq
      change (∃ lv si, env.vars[y]? = some lv ∧ env.scopes.lookup lv.scope = some si ∧
        r' = .local env.act si y) at hq'
      rcases hq with ⟨lv, si, hv, hs, rfl⟩
      rcases hq' with ⟨lv', si', hv', hs', hr'⟩
      have hxy : x ≠ y := by simpa using hdisjoint
      intro heq
      have hsame : RootInst.local env.act si x = RootInst.local env.act si' y :=
        heq.trans hr'
      injection hsame with _ _ hxy'
      exact hxy hxy'
    | global g =>
      change (∃ lv si, env.vars[x]? = some lv ∧ env.scopes.lookup lv.scope = some si ∧
        r = .local env.act si x) at hq
      change r' = .global g at hq'
      rcases hq with ⟨lv, si, hv, hs, rfl⟩
      intro heq
      rw [hq'] at heq
      cases heq
    | param i =>
      change P i r' at hq'
      rcases hq with ⟨lv, si, hv, hs, rfl⟩
      intro heq
      rw [← heq] at hq'
      exact paramAway i x lv si hv hs (by simpa using hq')
  | global g =>
    cases q' with
    | «local» x =>
      change (∃ lv si, env.vars[x]? = some lv ∧ env.scopes.lookup lv.scope = some si ∧
        r' = .local env.act si x) at hq'
      change r = .global g at hq
      rcases hq' with ⟨lv, si, hv, hs, rfl⟩
      intro heq
      rw [hq] at heq
      cases heq
    | global g' =>
      change (g == g') = false at hdisjoint
      change r = .global g at hq
      change r' = .global g' at hq'
      have hgg' : g ≠ g' := by simpa using hdisjoint
      intro heq
      rw [hq, hq'] at heq
      injection heq with heqIds
      exact hgg' heqIds
    | param i => simp [rootsMayOverlap] at hdisjoint
  | param i =>
    cases q' with
    | «local» x =>
      change (∃ lv si, env.vars[x]? = some lv ∧ env.scopes.lookup lv.scope = some si ∧
        r' = .local env.act si x) at hq'
      change P i r at hq
      rcases hq' with ⟨lv, si, hv, hs, rfl⟩
      intro heq
      have hparam : P i (.local env.act si x) := by
        rw [heq] at hq
        exact hq
      exact paramAway i x lv si hv hs hparam
    | global _ => simp [rootsMayOverlap] at hdisjoint
    | param _ => simp [rootsMayOverlap] at hdisjoint

/-- Static roots with no possible overlap denote distinct runtime roots. A
parameter cannot denote a local of the current activation because frame scopes
start at or above the activation base, while parameter roots are older. -/
theorem Gam.root_ne_of_no_overlap {m : Module} {W : World} {tenv : TEnv} {penv : PEnv}
    {env : Env} {s : St} {roots roots' : List RootRef} {r r' : RootInst}
    (hframe : Frame m W tenv penv env s)
    (hdisjoint : DemandRootsDisjoint roots roots')
    (h : Gam env W.P roots r) (h' : Gam env W.P roots' r') : r ≠ r' := by
  have paramAway : ∀ i x lv si, env.vars[x]? = some lv → env.scopes.lookup lv.scope = some si →
      ¬ W.P i (.local env.act si x) := by
    intro i x lv si _ hlookup hparam
    obtain ⟨before, after, hscopes, _⟩ := List.lookup_eq_some_iff.mp hlookup
    have hmember : (lv.scope, si) ∈ env.scopes := by
      rw [hscopes]
      exact List.mem_append_right _ List.mem_cons_self
    obtain ⟨hbase, _⟩ := hframe.below (lv.scope, si) hmember
    exact (Nat.not_lt_of_ge hbase) (hframe.pAge i env.act si x hparam)
  obtain ⟨q, hq, hroot⟩ := h
  obtain ⟨q', hq', hroot'⟩ := h'
  exact RootIn.root_ne_of_no_overlap paramAway (hdisjoint q hq q' hq') hroot hroot'

end Goose.Core.Sound
