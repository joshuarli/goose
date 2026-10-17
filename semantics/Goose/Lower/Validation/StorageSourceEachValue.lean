import Goose.Lower.Validation.StorageSourceOutputs
import Goose.Lower.Validation.StorageSourceControl

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem StorageAt.eachElemValue (le : LEnv) (before : LS) (slot : SlotId) (byReference : Bool) (element : ValueId)
    (loaded : before.cur.isSome = true → ∀ value, StorageAuthority le.mod.profile before.vals (.def value (.load element))) :
    StorageAt le before (Goose.Lower.eachElemValue slot byReference element) := by
  cases byReference with
  | false => exact StorageAt.emitDef _ loaded
  | true =>
    unfold Goose.Lower.eachElemValue
    simp only [ite_true]
    apply (StorageAt.read _ _).bind
    simp only [read_apply]
    split
    · rename_i destination row
      cases destination.ty <;> first | exact StorageAt.pure _ _ _ | exact StorageAt.borrowTo _ _ _ _
    · exact StorageAt.pure _ _ _

end Goose.Lower.Validation
