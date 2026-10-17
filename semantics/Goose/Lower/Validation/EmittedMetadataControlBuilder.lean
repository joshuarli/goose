import Goose.Lower.Validation.EmittedMetadataActions
import Goose.Lower.Validation.EmittedTypingControl

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem EmittedMetadata.recordValueRootRecipe {le : LEnv} {before : LS}
    (checked : EmittedMetadata le before) (value : ValueId) (sourceScope : ScopeId) :
    EmittedMetadata le (Goose.Lower.recordValueRootRecipe value sourceScope le before).2 := by
  apply checked.of_preserving (types_recordValueRootRecipe value sourceScope le before _ _ rfl)
  intro inst member
  have same : (Goose.Lower.recordValueRootRecipe value sourceScope le before).2.insts = before.insts := by
    rw [recordValueRootRecipe_run]
    rfl
  exact Or.inl (same ▸ member)

theorem EmittedMetadata.patchBrs {le : LEnv} {before : LS} (checked : EmittedMetadata le before)
    (target : BlockId) (incoming : List (BlockId × ValueId)) :
    EmittedMetadata le (Goose.Lower.patchBrs target incoming le before).2 := by
  induction incoming generalizing before with
  | nil => exact checked
  | cons pair rest ih =>
    exact ih (checked.patchTerm pair.1 (.br target [pair.2]) (.br target [pair.2]))

theorem EmittedMetadata.patchBrs0 {le : LEnv} {before : LS} (checked : EmittedMetadata le before)
    (target : BlockId) (incoming : List BlockId) :
    EmittedMetadata le (Goose.Lower.patchBrs0 target incoming le before).2 := by
  induction incoming generalizing before with
  | nil => exact checked
  | cons block rest ih =>
    exact ih (checked.patchTerm block (.br target []) (.br target []))

theorem EmittedMetadata.joinValue {le : LEnv} {before : LS} (checked : EmittedMetadata le before)
    (yes no : Option BlockId) (left right : ValueId) :
    EmittedMetadata le (Goose.Lower.joinValue yes left no right le before).2 := by
  unfold Goose.Lower.joinValue
  split
  · exact checked.setCur none
  · simp only [bind_run, valTy_run, setCur_run, pure_run]
    exact (((checked.newBlock _).patchBrs _ _).setCur _)

theorem EmittedMetadata.joinArms {le : LEnv} {before : LS} (checked : EmittedMetadata le before)
    (yes no : Option BlockId) :
    EmittedMetadata le (Goose.Lower.joinArms yes no le before).2 := by
  unfold Goose.Lower.joinArms
  split
  · exact checked.setCur none
  · exact (((checked.newBlock []).patchBrs0 _ _).setCur _)

theorem EmittedMetadata.fork {le : LEnv} {before : LS} (checked : EmittedMetadata le before)
    (condition : ValueId)
    (conditionAt : before.cur.isSome = true → before.vals[condition]? = some (some (.data .bool))) :
    EmittedMetadata le (Goose.Lower.fork condition le before).2 := by
  unfold Goose.Lower.fork
  simp only [bind_run, newBlock0_run, pure_run]
  apply EmittedMetadata.emitTerm ((checked.newBlock []).newBlock [])
  intro active
  exact .condbr (conditionAt active)

theorem EmittedMetadata.scFork {le : LEnv} {before : LS} (checked : EmittedMetadata le before)
    (isAnd : Bool) (condition : ValueId)
    (conditionAt : before.cur.isSome = true → before.vals[condition]? = some (some (.data .bool))) :
    EmittedMetadata le (Goose.Lower.scFork isAnd condition le before).2 := by
  have retained := (types_newBlock [] le before _ _ rfl).trans
    (types_newBlock [.data .bool] le (Goose.Lower.newBlock [] le before).2 _ _ rfl)
  cases isAnd <;> unfold Goose.Lower.scFork <;>
    simp only [bind_run, Bool.false_eq_true, reduceIte, pure_run]
  all_goals
    apply EmittedMetadata.emitTerm ((checked.newBlock []).newBlock [.data .bool])
    intro active
    exact .condbr (retained condition (.data .bool) (conditionAt active))

end Goose.Lower.Validation
