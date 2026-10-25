import Goose.Lower.Validation.PermissionPreservationFresh
import Goose.Lower.Validation.PermissionPreservationTargets

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem borrowTo_ordinary_fresh_binding {le : LEnv} {first : Nat} {before after : LS}
    {owner value : ValueId} {referent : Ty}
    (evidence : FreshWritableEvidence le first before owner)
    (typed : before.vals[owner]? = some (some (.data (.ref .mutable referent))))
    (ordinary : BindingTarget .pilot referent)
    (run : borrowTo .mutable owner le before = (value, after)) :
    FreshWritableEvidence le first after value := by
  cases referent <;> try (simp [BindingTarget] at ordinary)
  all_goals
    simp [borrowTo, bind_run, valTy_of_recorded typed, freezeTo, pure_run] at run
    obtain ⟨rfl, rfl⟩ := run
    exact evidence

theorem FreshContentsEvidence.ownerBorrow_permissions {le : LEnv} {first : Nat} {before after : LS}
    {owner value : ValueId} {current : BlockId}
    (evidence : FreshContentsEvidence le first before owner)
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current)
    (run : emitDef (.ownerBorrow owner) le before = (value, after)) :
    FreshWritableEvidence le first after value ∧ FreshContentsEvidence le first after value :=
  ⟨evidence.emitDef_binding_dependency checked bounded live run (fun _ permitted => permitted),
    evidence.emitDef_dependency checked bounded live run (fun _ permitted => permitted)⟩

theorem borrowTo_owner_fresh_permissions {le : LEnv} {first : Nat} {before after : LS}
    {owner value : ValueId} {referent : Ty} {current : BlockId}
    (evidence : FreshContentsEvidence le first before owner)
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current) (profile : le.mod.profile = .shrink)
    (typed : before.vals[owner]? = some (some (.data (.ref .mutable referent))))
    (resizable : (∃ element, referent = .grow element) ∨ (∃ element, referent = .growshrink element) ∨
        (∃ element capacity, referent = .limited element capacity))
    (run : borrowTo .mutable owner le before = (value, after)) :
    FreshWritableEvidence le first after value ∧ FreshContentsEvidence le first after value := by
  rcases resizable with ⟨element, rfl⟩ | ⟨element, rfl⟩ | ⟨element, capacity, rfl⟩ <;>
    simp [borrowTo, bind_run, valTy_of_recorded typed, profile] at run <;>
    exact evidence.ownerBorrow_permissions checked bounded live run

theorem lowerExpr_ref_owner_fresh_permissions_of_place {le : LEnv} {first : Nat} {place : Place}
    {before middle after : LS} {owner value : ValueId} {referent : Ty} {current : BlockId}
    (placeRun : lowerPlace place le before = (owner, middle))
    (evidence : FreshContentsEvidence le first middle owner)
    (checked : middle.DenseDefinitions) (bounded : LiveBound middle)
    (live : middle.cur = some current) (profile : le.mod.profile = .shrink)
    (typed : middle.vals[owner]? = some (some (.data (.ref .mutable referent))))
    (resizable : (∃ element, referent = .grow element) ∨ (∃ element, referent = .growshrink element) ∨
        (∃ element capacity, referent = .limited element capacity))
    (run : lowerExpr (.ref .mutable place) le before = (value, after)) :
    FreshWritableEvidence le first after value ∧ FreshContentsEvidence le first after value := by
  simp only [lowerExpr, bind_run, placeRun] at run
  exact borrowTo_owner_fresh_permissions evidence checked bounded live profile typed resizable run

#print axioms borrowTo_ordinary_fresh_binding
#print axioms FreshContentsEvidence.ownerBorrow_permissions
#print axioms borrowTo_owner_fresh_permissions
#print axioms lowerExpr_ref_owner_fresh_permissions_of_place

end Goose.Lower.Validation
