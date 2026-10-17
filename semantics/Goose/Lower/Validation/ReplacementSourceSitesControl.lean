import Goose.Lower.Validation.ReplacementSourceSitesCoercions
import Goose.Lower.Validation.ReplacementSourceSitesFree

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

variable {targets : List BlockId}

theorem ReplacementSitesAt.joinValue (le : LEnv) (before : LS) (yes : Option BlockId) (yesValue : ValueId)
    (no : Option BlockId) (noValue : ValueId) :
    ReplacementSitesAt (targets := targets) le before (Goose.Lower.joinValue yes yesValue no noValue) :=
  (ReplacementSitesFree.joinValue le before yes yesValue no noValue).at

theorem ReplacementSitesAt.joinArms (le : LEnv) (before : LS) (yes no : Option BlockId) :
    ReplacementSitesAt (targets := targets) le before (Goose.Lower.joinArms yes no) :=
  (ReplacementSitesFree.joinArms le before yes no).at

theorem ReplacementSitesAt.fork (le : LEnv) (before : LS) (condition : ValueId) :
    ReplacementSitesAt (targets := targets) le before (Goose.Lower.fork condition) :=
  (ReplacementSitesFree.fork le before condition).at

theorem ReplacementSitesAt.scFork (le : LEnv) (before : LS) (isAnd : Bool) (condition : ValueId) :
    ReplacementSitesAt (targets := targets) le before (Goose.Lower.scFork isAnd condition) :=
  (ReplacementSitesFree.scFork le before isAnd condition).at

theorem ReplacementSitesAt.leaveAll (le : LEnv) (before : LS) (scopes : List ScopeId) :
    ReplacementSitesAt (targets := targets) le before (Goose.Lower.leaveAll scopes) := by
  induction scopes generalizing before with
  | nil => exact ReplacementSitesAt.pure _ _ _
  | cons scope rest ih => exact (ReplacementSitesAt.emitEffect _ (by intros; trivial)).bind (ih _)

theorem ReplacementSitesAt.leaveTo (le : LEnv) (before : LS) (depth : Nat) :
    ReplacementSitesAt (targets := targets) le before (Goose.Lower.leaveTo depth) := by
  unfold Goose.Lower.leaveTo
  exact (ReplacementSitesAt.get _ _).bind (ReplacementSitesAt.leaveAll _ _ _)

theorem ReplacementSitesAt.initSlots (le : LEnv) (before : LS) (slots : List (SlotId × ValueId × OriginId)) :
    ReplacementSitesAt (targets := targets) le before (Goose.Lower.initSlots slots) := by
  induction slots generalizing before with
  | nil => exact ReplacementSitesAt.pure _ _ _
  | cons triple rest ih => exact (ReplacementSitesAt.emitEffect _ (by intros; trivial)).bind (ih _)

theorem ReplacementSitesAt.pushScope (le : LEnv) (before : LS) (scope : ScopeId) :
    ReplacementSitesAt (targets := targets) le before (Goose.Lower.pushScope scope)  := fun _ checked => ⟨.refl _, checked.of_emits (.of_blocks rfl) (.refl _) (.of_blocks rfl)⟩

theorem ReplacementSitesAt.popScope (le : LEnv) (before : LS) :
    ReplacementSitesAt (targets := targets) le before Goose.Lower.popScope  := fun _ checked => ⟨.refl _, checked.of_emits (.of_blocks rfl) (.refl _) (.of_blocks rfl)⟩

theorem ReplacementSitesAt.inScope {le : LEnv} {before : LS} (scope : ScopeId) {body : B α}
    (child : ReplacementSitesAt (targets := targets) le (Goose.Lower.pushScope scope le before).2 body) :
    ReplacementSitesAt (targets := targets) le before (Goose.Lower.inScope scope body) := by
  unfold Goose.Lower.inScope
  exact (ReplacementSitesAt.pushScope _ _ _).bind (child.bind
    ((ReplacementSitesAt.popScope _ _).bind (ReplacementSitesAt.pure _ _ _)))

theorem ReplacementSitesAt.growOwner (le : LEnv) (before : LS) (owner : ValueId) :
    ReplacementSitesAt (targets := targets) le before (Goose.Lower.growOwner owner) := by
  unfold Goose.Lower.growOwner
  apply (ReplacementSitesAt.valTy _ _ _).bind
  cases (Goose.Lower.valTy owner le before).1 with
  | data ty => cases ty <;> exact ReplacementSitesAt.pure _ _ _
  | view _ _ => exact ReplacementSitesAt.pure _ _ _

theorem ReplacementSitesAt.regrowOf (le : LEnv) (before : LS) (owner : Option ValueId) :
    ReplacementSitesAt (targets := targets) le before (Goose.Lower.regrowOf owner) := by
  cases owner with
  | none => exact ReplacementSitesAt.pure _ _ _
  | some owner => exact ReplacementSitesAt.growOwner _ _ _

theorem ReplacementSitesAt.eachSampled (le : LEnv) (before : LS) (regrow : Bool) (view : ValueId) :
    ReplacementSitesAt (targets := targets) le before (Goose.Lower.eachSampled regrow view) := by
  cases regrow
  · exact ReplacementSitesAt.emitDef _ (by intros; trivial)
  · exact ReplacementSitesAt.pure _ _ _

theorem ReplacementSitesAt.eachLen (le : LEnv) (before : LS) (regrow : Bool) (owner : Option ValueId) (sampled : ValueId) :
    ReplacementSitesAt (targets := targets) le before (Goose.Lower.eachLen regrow owner sampled) := by
  cases regrow
  · exact ReplacementSitesAt.pure _ _ _
  · exact ReplacementSitesAt.emitDef _ (by intros; trivial)

theorem ReplacementSitesAt.isLive (le : LEnv) (before : LS) : ReplacementSitesAt (targets := targets) le before Goose.Lower.isLive := by
  unfold Goose.Lower.isLive
  exact (ReplacementSitesAt.curBlock _ _).bind (ReplacementSitesAt.pure _ _ _)

theorem ReplacementSitesAt.rangeBack (le : LEnv) (before : LS) (type : IntTy) (value : ValueId) (header : BlockId) (allowed : header ∈ targets) :
    ReplacementSitesAt (targets := targets) le before (Goose.Lower.rangeBack type value header) := by
  unfold Goose.Lower.rangeBack
  apply (ReplacementSitesAt.isLive _ _).bind
  split
  · exact (ReplacementSitesAt.emitDef _ (by intros; trivial)).bind
      (ReplacementSitesAt.emitTerm _ _ _ (by simpa [Term.successors] using Or.inl allowed))
  · exact ReplacementSitesAt.pure _ _ _

end Goose.Lower.Validation
