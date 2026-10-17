import Goose.Lower.Validation.Typing
import Goose.Core.Sound.Module

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound

theorem checkOwnerRun_fresh {env : TEnv} {expr : Expr} {ty : Ty} {start finish : Nat}
    (checked : checkOwnerRun env expr ty start = .ok ((), finish))
    (shrink : env.mod.profile = .shrink) (owner : ty.ownerElem?.isSome = true) :
    expr.freshOwner = true := by
  cases fresh : expr.freshOwner
  · simp only [checkOwnerRun, shrink, owner, fresh, Bool.not_false, Bool.and_self, beq_self_eq_true, ↓reduceIte] at checked
    change (Except.error _ : Core.V (Unit × Nat)) = .ok _ at checked
    cases checked
  · rfl

theorem accepted_replacement_roots_disjoint {module : Core.Module}
    (accepted : Core.validate module = .ok ()) (shrink : module.profile = .shrink)
    {owner : Nat} (ownerBound : owner < module.contexts.size + module.globals.size)
    {expected : List DemandExpectedPoint} (walk : DemandNode.expectedPoints module owner = .ok expected)
    {occurrence : DemandExpectedPoint} (member : occurrence ∈ expected)
    {request : DemandWholeCheck} (requested : request ∈ occurrence.wholeChecks) :
    DemandRootsDisjoint request.forbidden.roots request.checkedRoots := by
  obtain ⟨plans, derived, wellFormed⟩ := (validate_modOk module accepted).demandPlans
  have bound : owner < plans.size := by
    rw [wellFormed.1, shrink]
    exact ownerBound
  have selected : plans[owner]? = some plans[owner] := by simp [bound]
  obtain ⟨approvals, _⟩ := deriveModuleDemand_ok_approvals module plans derived
  obtain ⟨⟨walked, known, facts⟩⟩ := approvals owner plans[owner] selected
  have same : walked = expected := Except.ok.inj (known.down.symm.trans walk)
  subst walked
  obtain ⟨approval, _, _, forbidden, roots, _⟩ := facts.wholeRootsAt occurrence member request requested
  rw [← forbidden, ← roots]
  exact approval.disjoint

theorem accepted_replacement_place_disjoint {module : Core.Module}
    (accepted : Core.validate module = .ok ()) (shrink : module.profile = .shrink)
    {owner : Nat} (ownerBound : owner < module.contexts.size + module.globals.size)
    {expected : List DemandExpectedPoint} (walk : DemandNode.expectedPoints module owner = .ok expected)
    {occurrence : DemandExpectedPoint} (member : occurrence ∈ expected)
    {path : List Nat} {place : Place} {access : AccessEnv} {forbidden : DemandOwner}
    (source : DemandExpectedSourceAt module owner path (.place place) .place occurrence)
    (accessAt : demandAccess? module owner = some access) (inherited : forbidden ∈ occurrence.forbidden) :
    ∃ roots, access.placeRoots place = .ok roots ∧ DemandRootsDisjoint forbidden.roots roots := by
  obtain ⟨roots, checked, request, requested, sameOwner, sameRoots⟩ :=
    source.placeWholeRootsRequest accessAt inherited
  have disjoint := accepted_replacement_roots_disjoint accepted shrink ownerBound walk member requested
  exact ⟨roots, checked, by simpa [sameOwner, sameRoots] using disjoint⟩

end Goose.Lower.Validation
