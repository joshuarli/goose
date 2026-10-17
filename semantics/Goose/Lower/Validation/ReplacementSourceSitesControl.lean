import Goose.Lower.Validation.ReplacementSourceSitesCoercions

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem ReplacementSitesAt.patchBrs (le : LEnv) (before : LS) (target : BlockId) (incoming : List (BlockId × ValueId)) :
    ReplacementSitesAt le before (Goose.Lower.patchBrs target incoming) := by
  induction incoming generalizing before with
  | nil => exact ReplacementSitesAt.pure _ _ _
  | cons pair rest ih => exact (ReplacementSitesAt.patchTerm _ _ _ _).bind (ih _)

theorem ReplacementSitesAt.patchBrs0 (le : LEnv) (before : LS) (target : BlockId) (incoming : List BlockId) :
    ReplacementSitesAt le before (Goose.Lower.patchBrs0 target incoming) := by
  induction incoming generalizing before with
  | nil => exact ReplacementSitesAt.pure _ _ _
  | cons block rest ih => exact (ReplacementSitesAt.patchTerm _ _ _ _).bind (ih _)

theorem ReplacementSitesAt.joinValue (le : LEnv) (before : LS) (yes : Option BlockId) (yesValue : ValueId)
    (no : Option BlockId) (noValue : ValueId) :
    ReplacementSitesAt le before (Goose.Lower.joinValue yes yesValue no noValue) := by
  unfold Goose.Lower.joinValue
  split
  · exact (ReplacementSitesAt.setCur _ _ _).bind (ReplacementSitesAt.pure _ _ _)
  · exact (ReplacementSitesAt.valTy _ _ _).bind ((ReplacementSitesAt.newBlock _ _ _).bind
      ((ReplacementSitesAt.patchBrs _ _ _ _).bind ((ReplacementSitesAt.setCur _ _ _).bind (ReplacementSitesAt.pure _ _ _))))

theorem ReplacementSitesAt.joinArms (le : LEnv) (before : LS) (yes no : Option BlockId) :
    ReplacementSitesAt le before (Goose.Lower.joinArms yes no) := by
  unfold Goose.Lower.joinArms
  split
  · exact ReplacementSitesAt.setCur _ _ _
  · exact (ReplacementSitesAt.newBlock _ _ _).bind ((ReplacementSitesAt.patchBrs0 _ _ _ _).bind (ReplacementSitesAt.setCur _ _ _))

theorem ReplacementSitesAt.fork (le : LEnv) (before : LS) (condition : ValueId) :
    ReplacementSitesAt le before (Goose.Lower.fork condition) := by
  unfold Goose.Lower.fork
  exact (ReplacementSitesAt.newBlock _ _ _).bind ((ReplacementSitesAt.newBlock _ _ _).bind
    ((ReplacementSitesAt.emitTerm _ _ _).bind (ReplacementSitesAt.pure _ _ _)))

theorem ReplacementSitesAt.scFork (le : LEnv) (before : LS) (isAnd : Bool) (condition : ValueId) :
    ReplacementSitesAt le before (Goose.Lower.scFork isAnd condition) := by
  cases isAnd <;> unfold Goose.Lower.scFork
  all_goals exact (ReplacementSitesAt.newBlock _ _ _).bind ((ReplacementSitesAt.newBlock _ _ _).bind
    ((ReplacementSitesAt.emitTerm _ _ _).bind (ReplacementSitesAt.pure _ _ _)))

theorem ReplacementSitesAt.leaveAll (le : LEnv) (before : LS) (scopes : List ScopeId) :
    ReplacementSitesAt le before (Goose.Lower.leaveAll scopes) := by
  induction scopes generalizing before with
  | nil => exact ReplacementSitesAt.pure _ _ _
  | cons scope rest ih => exact (ReplacementSitesAt.emitEffect _ (by intros; trivial)).bind (ih _)

theorem ReplacementSitesAt.leaveTo (le : LEnv) (before : LS) (depth : Nat) :
    ReplacementSitesAt le before (Goose.Lower.leaveTo depth) := by
  unfold Goose.Lower.leaveTo
  exact (ReplacementSitesAt.get _ _).bind (ReplacementSitesAt.leaveAll _ _ _)

theorem ReplacementSitesAt.initSlots (le : LEnv) (before : LS) (slots : List (SlotId × ValueId × OriginId)) :
    ReplacementSitesAt le before (Goose.Lower.initSlots slots) := by
  induction slots generalizing before with
  | nil => exact ReplacementSitesAt.pure _ _ _
  | cons triple rest ih => exact (ReplacementSitesAt.emitEffect _ (by intros; trivial)).bind (ih _)

theorem ReplacementSitesAt.pushScope (le : LEnv) (before : LS) (scope : ScopeId) :
    ReplacementSitesAt le before (Goose.Lower.pushScope scope) := fun checked => checked.of_emits (.of_blocks rfl) (.refl _)

theorem ReplacementSitesAt.popScope (le : LEnv) (before : LS) :
    ReplacementSitesAt le before Goose.Lower.popScope := fun checked => checked.of_emits (.of_blocks rfl) (.refl _)

theorem ReplacementSitesAt.inScope {le : LEnv} {before : LS} (scope : ScopeId) {body : B α}
    (child : ReplacementSitesAt le (Goose.Lower.pushScope scope le before).2 body) :
    ReplacementSitesAt le before (Goose.Lower.inScope scope body) := by
  unfold Goose.Lower.inScope
  exact (ReplacementSitesAt.pushScope _ _ _).bind (child.bind
    ((ReplacementSitesAt.popScope _ _).bind (ReplacementSitesAt.pure _ _ _)))

theorem ReplacementSitesAt.growOwner (le : LEnv) (before : LS) (owner : ValueId) :
    ReplacementSitesAt le before (Goose.Lower.growOwner owner) := by
  unfold Goose.Lower.growOwner
  apply (ReplacementSitesAt.valTy _ _ _).bind
  cases (Goose.Lower.valTy owner le before).1 with
  | data ty => cases ty <;> exact ReplacementSitesAt.pure _ _ _
  | view _ _ => exact ReplacementSitesAt.pure _ _ _

theorem ReplacementSitesAt.regrowOf (le : LEnv) (before : LS) (owner : Option ValueId) :
    ReplacementSitesAt le before (Goose.Lower.regrowOf owner) := by
  cases owner with
  | none => exact ReplacementSitesAt.pure _ _ _
  | some owner => exact ReplacementSitesAt.growOwner _ _ _

theorem ReplacementSitesAt.eachSampled (le : LEnv) (before : LS) (regrow : Bool) (view : ValueId) :
    ReplacementSitesAt le before (Goose.Lower.eachSampled regrow view) := by
  cases regrow
  · exact ReplacementSitesAt.emitDef _ (by intros; trivial)
  · exact ReplacementSitesAt.pure _ _ _

theorem ReplacementSitesAt.eachLen (le : LEnv) (before : LS) (regrow : Bool) (owner : Option ValueId) (sampled : ValueId) :
    ReplacementSitesAt le before (Goose.Lower.eachLen regrow owner sampled) := by
  cases regrow
  · exact ReplacementSitesAt.pure _ _ _
  · exact ReplacementSitesAt.emitDef _ (by intros; trivial)

theorem ReplacementSitesAt.isLive (le : LEnv) (before : LS) : ReplacementSitesAt le before Goose.Lower.isLive := by
  unfold Goose.Lower.isLive
  exact (ReplacementSitesAt.curBlock _ _).bind (ReplacementSitesAt.pure _ _ _)

theorem ReplacementSitesAt.rangeBack (le : LEnv) (before : LS) (type : IntTy) (value : ValueId) (header : BlockId) :
    ReplacementSitesAt le before (Goose.Lower.rangeBack type value header) := by
  unfold Goose.Lower.rangeBack
  apply (ReplacementSitesAt.isLive _ _).bind
  split
  · exact (ReplacementSitesAt.emitDef _ (by intros; trivial)).bind (ReplacementSitesAt.emitTerm _ _ _)
  · exact ReplacementSitesAt.pure _ _ _

end Goose.Lower.Validation
