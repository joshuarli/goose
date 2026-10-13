import Goose.Core.Sound.AccessReplay

namespace Goose.Core.Sound
open Goose.Core Goose.Proofs.Memory

/-- Argument roots name declared globals. A reference holder in an open caller
scope must still be visible so its binding can classify its stored value. -/
def ArgumentRootDeclarations (m : Module) (tenv : TEnv) (env : Env)
    (ars : List (List RootRef)) : Prop :=
  ∀ (i : Nat) (q : RootRef), q ∈ ars[i]?.getD [] → match q with
    | .global g => ∃ gl, m.globals[g]? = some gl
    | .local x => ∀ lv si, env.vars[x]? = some lv →
        env.scopes.lookup lv.scope = some si → lv.ty.isRefLike = true → x ∈ tenv.visible
    | .param _ => True

theorem ArgumentRootDeclarations.included
    {m : Module} {tenv : TEnv} {env : Env} {actual expected : List (List RootRef)}
    (declarations : ArgumentRootDeclarations m tenv env expected)
    (included : RootListsIncluded actual expected) :
    ArgumentRootDeclarations m tenv env actual := by
  intro i q member
  cases ha : actual[i]? with
  | none => simp [ha] at member
  | some roots =>
    obtain ⟨expectedRoots, he, subset⟩ := included i roots ha
    exact declarations i q (by simpa [he] using subset q (by simpa [ha] using member))

/-- Existing non-reference storage is observed by declaration type; visible
reference holders are classified from the frame's stored binding. -/
theorem Frame.classifiedArgumentRoots
    {m : Module} {W : World} {tenv : TEnv} {penv : PEnv} {env : Env} {s : St}
    {future : List VarId} {ars : List (List RootRef)}
    {oldObs newObs : Observation} {newD : RootInst → Ty → Prop}
    (frame : Frame m W tenv penv env s future)
    (declarations : ArgumentRootDeclarations m tenv env ars)
    (inherited : ClassifiedParameters m W.P W.D oldObs s.store)
    (roots : ∀ r T, oldObs.roots r T → newObs.roots r T)
    (storage : ∀ r T, StorageRootTypes env r T → s.store.roots[r]? ≠ none →
      newObs.roots r T)
    (slices : ∀ r E, W.D r E → newD r E) :
    ClassifiedParameters m (fun i r => Gam env W.P (ars[i]?.getD []) r)
      newD newObs s.store := by
  intro i r parameter
  obtain ⟨q, member, denotes⟩ := parameter
  cases q with
  | global g =>
    change r = .global g at denotes
    subst r
    exact declarations i _ member
  | param j =>
    exact (inherited.mono (fun _ _ h => h) roots slices) j r denotes
  | «local» x =>
    obtain ⟨lv, si, hvar, hscope, rfl⟩ := denotes
    cases href : lv.ty.isRefLike with
    | false =>
      cases present : s.store.roots[RootInst.local env.act si x]? with
      | none => exact Or.inr (Or.inr (Or.inr present))
      | some v =>
        exact Or.inl ⟨lv.ty, storage _ _
          ⟨x, lv, si, hvar, hscope, rfl, href, rfl⟩ (by simp [present])⟩
    | true =>
      have visible := declarations i _ member lv si hvar hscope href
      obtain ⟨lv', si', v, hvar', hscope', _, present, reference⟩ :=
        frame.bindings x visible
      have sameVar : lv' = lv := Option.some.inj (hvar'.symm.trans hvar)
      subst lv'
      have sameScope : si' = si := Option.some.inj (hscope'.symm.trans hscope)
      subst si'
      exact Or.inr (Or.inr (Or.inl ⟨v, present, reference href⟩))

end Goose.Core.Sound
