import Goose.Lower.Validation.StorageSourceCoercions

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem StorageAt.patchBrs (le : LEnv) (before : LS) (target : BlockId) (incoming : List (BlockId × ValueId)) :
    StorageAt le before (Goose.Lower.patchBrs target incoming) := by
  induction incoming generalizing before with
  | nil => exact StorageAt.pure _ _ _
  | cons pair rest ih => exact (StorageAt.patchTerm _ _ _ _).bind (ih _)

theorem StorageAt.patchBrs0 (le : LEnv) (before : LS) (target : BlockId) (incoming : List BlockId) :
    StorageAt le before (Goose.Lower.patchBrs0 target incoming) := by
  induction incoming generalizing before with
  | nil => exact StorageAt.pure _ _ _
  | cons block rest ih => exact (StorageAt.patchTerm _ _ _ _).bind (ih _)

theorem StorageAt.joinValue (le : LEnv) (before : LS) (yes : Option BlockId) (yesValue : ValueId)
    (no : Option BlockId) (noValue : ValueId) :
    StorageAt le before (Goose.Lower.joinValue yes yesValue no noValue) := by
  unfold Goose.Lower.joinValue
  split
  · exact (StorageAt.setCur _ _ _).bind (StorageAt.pure _ _ _)
  · exact (StorageAt.valTy _ _ _).bind ((StorageAt.newBlock _ _ _).bind
      ((StorageAt.patchBrs _ _ _ _).bind ((StorageAt.setCur _ _ _).bind (StorageAt.pure _ _ _))))

theorem StorageAt.recordValueRootRecipe (le : LEnv) (before : LS) (value : ValueId)
    (sourceScope : ScopeId) : StorageAt le before (recordValueRootRecipe value sourceScope) := by
  intro checked
  rw [recordValueRootRecipe_run]
  exact checked

theorem StorageAt.joinArms (le : LEnv) (before : LS) (yes no : Option BlockId) :
    StorageAt le before (Goose.Lower.joinArms yes no) := by
  unfold Goose.Lower.joinArms
  split
  · exact StorageAt.setCur _ _ _
  · exact (StorageAt.newBlock _ _ _).bind ((StorageAt.patchBrs0 _ _ _ _).bind (StorageAt.setCur _ _ _))

theorem StorageAt.fork (le : LEnv) (before : LS) (condition : ValueId) :
    StorageAt le before (Goose.Lower.fork condition) := by
  unfold Goose.Lower.fork
  exact (StorageAt.newBlock _ _ _).bind ((StorageAt.newBlock _ _ _).bind
    ((StorageAt.emitTerm _ _ _).bind (StorageAt.pure _ _ _)))

theorem StorageAt.scFork (le : LEnv) (before : LS) (isAnd : Bool) (condition : ValueId) :
    StorageAt le before (Goose.Lower.scFork isAnd condition) := by
  cases isAnd <;> unfold Goose.Lower.scFork
  all_goals exact (StorageAt.newBlock _ _ _).bind ((StorageAt.newBlock _ _ _).bind
    ((StorageAt.emitTerm _ _ _).bind (StorageAt.pure _ _ _)))

theorem StorageAt.leaveAll (le : LEnv) (before : LS) (scopes : List ScopeId) :
    StorageAt le before (Goose.Lower.leaveAll scopes) := by
  induction scopes generalizing before with
  | nil => exact StorageAt.pure _ _ _
  | cons scope rest ih => exact (StorageAt.emitEffect _ (by intros; trivial)).bind (ih _)

theorem StorageAt.leaveTo (le : LEnv) (before : LS) (depth : Nat) :
    StorageAt le before (Goose.Lower.leaveTo depth) := by
  unfold Goose.Lower.leaveTo
  exact (StorageAt.get _ _).bind (StorageAt.leaveAll _ _ _)

theorem StorageAt.initSlots (le : LEnv) (before : LS) (slots : List (SlotId × ValueId × OriginId)) :
    StorageAt le before (Goose.Lower.initSlots slots) := by
  induction slots generalizing before with
  | nil => exact StorageAt.pure _ _ _
  | cons triple rest ih => exact (StorageAt.emitEffect _ (by intros; trivial)).bind (ih _)

theorem StorageAt.pushScope (le : LEnv) (before : LS) (scope : ScopeId) :
    StorageAt le before (Goose.Lower.pushScope scope) := fun checked => checked

theorem StorageAt.popScope (le : LEnv) (before : LS) :
    StorageAt le before Goose.Lower.popScope := fun checked => checked

theorem StorageAt.inScope {le : LEnv} {before : LS} (scope : ScopeId) {body : B α}
    (child : StorageAt le (Goose.Lower.pushScope scope le before).2 body) :
    StorageAt le before (Goose.Lower.inScope scope body) := by
  unfold Goose.Lower.inScope
  exact (StorageAt.pushScope _ _ _).bind (child.bind
    ((StorageAt.popScope _ _).bind (StorageAt.pure _ _ _)))

theorem StorageAt.growOwner (le : LEnv) (before : LS) (owner : ValueId) :
    StorageAt le before (Goose.Lower.growOwner owner) := by
  unfold Goose.Lower.growOwner
  apply (StorageAt.valTy _ _ _).bind
  cases (Goose.Lower.valTy owner le before).1 with
  | data ty => cases ty <;> exact StorageAt.pure _ _ _
  | view _ _ => exact StorageAt.pure _ _ _

theorem StorageAt.regrowOf (le : LEnv) (before : LS) (owner : Option ValueId) :
    StorageAt le before (Goose.Lower.regrowOf owner) := by
  cases owner with
  | none => exact StorageAt.pure _ _ _
  | some owner => exact StorageAt.growOwner _ _ _

theorem StorageAt.eachSampled (le : LEnv) (before : LS) (regrow : Bool) (view : ValueId) :
    StorageAt le before (Goose.Lower.eachSampled regrow view) := by
  cases regrow
  · exact StorageAt.emitDef _ (by intros; trivial)
  · exact StorageAt.pure _ _ _

theorem StorageAt.eachLen (le : LEnv) (before : LS) (regrow : Bool) (owner : Option ValueId) (sampled : ValueId) :
    StorageAt le before (Goose.Lower.eachLen regrow owner sampled) := by
  cases regrow
  · exact StorageAt.pure _ _ _
  · exact StorageAt.emitDef _ (by intros; trivial)

theorem StorageAt.isLive (le : LEnv) (before : LS) : StorageAt le before Goose.Lower.isLive := by
  unfold Goose.Lower.isLive
  exact (StorageAt.curBlock _ _).bind (StorageAt.pure _ _ _)

theorem StorageAt.rangeBack (le : LEnv) (before : LS) (type : IntTy) (value : ValueId) (header : BlockId) :
    StorageAt le before (Goose.Lower.rangeBack type value header) := by
  unfold Goose.Lower.rangeBack
  apply (StorageAt.isLive _ _).bind
  split
  · exact (StorageAt.emitDef _ (by intros; trivial)).bind (StorageAt.emitTerm _ _ _)
  · exact StorageAt.pure _ _ _

end Goose.Lower.Validation
