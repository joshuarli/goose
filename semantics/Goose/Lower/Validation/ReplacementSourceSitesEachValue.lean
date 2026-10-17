import Goose.Lower.Validation.ReplacementSourceSitesOutputs
import Goose.Lower.Validation.ReplacementSourceSitesControl

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem ReplacementSitesAt.eachElemValue (le : LEnv) (before : LS) (slot : SlotId) (byReference : Bool) (element : ValueId)
    (loaded : before.cur.isSome = true → ∀ value, NotReplacement (.def value (.load element))) :
    ReplacementSitesAt le before (Goose.Lower.eachElemValue slot byReference element) := by
  cases byReference with
  | false => exact ReplacementSitesAt.emitDef _ loaded
  | true =>
    unfold Goose.Lower.eachElemValue
    simp only [ite_true]
    apply (ReplacementSitesAt.read _ _).bind
    simp only [read_apply]
    split
    · rename_i destination row
      cases destination.ty <;> first | exact ReplacementSitesAt.pure _ _ _ | exact ReplacementSitesAt.borrowTo _ _ _ _
    · exact ReplacementSitesAt.pure _ _ _

end Goose.Lower.Validation
