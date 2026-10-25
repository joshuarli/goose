import Goose.Lower.Validation.PermissionPreservationContents

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem borrowTo_owner_permissions {le : LEnv} {before after : LS}
    {owner value : ValueId} {referent : Ty} {current : BlockId}
    (evidence : ContentsEvidence le before owner)
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current) (profile : le.mod.profile = .shrink)
    (typed : before.vals[owner]? = some (some (.data (.ref .mutable referent))))
    (resizable : (∃ element, referent = .grow element) ∨ (∃ element, referent = .growshrink element) ∨
        (∃ element capacity, referent = .limited element capacity))
    (run : borrowTo .mutable owner le before = (value, after)) :
    WritableEvidence le after value ∧ ContentsEvidence le after value := by
  rcases resizable with ⟨element, rfl⟩ | ⟨element, rfl⟩ | ⟨element, capacity, rfl⟩ <;>
    simp [borrowTo, bind_run, valTy_of_recorded typed, profile] at run <;>
    exact ⟨evidence.ownerBorrow_binding checked bounded live run,
      evidence.ownerBorrow_contents checked bounded live run⟩

theorem lowerExpr_ref_owner_permissions_of_place {le : LEnv} {place : Place}
    {before middle after : LS} {owner value : ValueId} {referent : Ty} {current : BlockId}
    (placeRun : lowerPlace place le before = (owner, middle))
    (evidence : ContentsEvidence le middle owner)
    (checked : middle.DenseDefinitions) (bounded : LiveBound middle)
    (live : middle.cur = some current) (profile : le.mod.profile = .shrink)
    (typed : middle.vals[owner]? = some (some (.data (.ref .mutable referent))))
    (resizable : (∃ element, referent = .grow element) ∨ (∃ element, referent = .growshrink element) ∨
        (∃ element capacity, referent = .limited element capacity))
    (run : lowerExpr (.ref .mutable place) le before = (value, after)) :
    WritableEvidence le after value ∧ ContentsEvidence le after value := by
  simp only [lowerExpr, bind_run, placeRun] at run
  exact borrowTo_owner_permissions evidence checked bounded live profile typed resizable run

theorem lowerArg_byRef_owner_permissions_of_place {le : LEnv} {place : Place}
    {before middle after : LS} {owner value : ValueId} {referent : Ty} {current : BlockId}
    (placeRun : lowerPlace place le before = (owner, middle))
    (evidence : ContentsEvidence le middle owner)
    (checked : middle.DenseDefinitions) (bounded : LiveBound middle)
    (live : middle.cur = some current) (profile : le.mod.profile = .shrink)
    (typed : middle.vals[owner]? = some (some (.data (.ref .mutable referent))))
    (resizable : (∃ element, referent = .grow element) ∨ (∃ element, referent = .growshrink element) ∨
        (∃ element capacity, referent = .limited element capacity))
    (run : lowerArg (.byRef .mutable place) le before = (value, after)) :
    WritableEvidence le after value ∧ ContentsEvidence le after value := by
  simp only [lowerArg, bind_run, placeRun] at run
  exact borrowTo_owner_permissions evidence checked bounded live profile typed resizable run

#print axioms borrowTo_owner_permissions
#print axioms lowerExpr_ref_owner_permissions_of_place
#print axioms lowerArg_byRef_owner_permissions_of_place

end Goose.Lower.Validation
