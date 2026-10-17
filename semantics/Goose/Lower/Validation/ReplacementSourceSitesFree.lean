import Goose.Lower.Validation.ReplacementSourceSitesActions
import Goose.Lower.GeneratedIntervalFramesFunctions

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

variable {root : DemandNode} {targets : List BlockId}

theorem ReplacementSitesFree.of_runs {le : LEnv} {before : LS} {action : B α}
    (emitted : EmitsOnlyRun NotReplacement action) (types : TypeRun action)
    (frames : GeneratedTargetFrameRun none action) :
    ReplacementSitesFree (root := root) (targets := targets) le before action := by
  intro checked
  have emitted := emitted le before _ _ rfl
  exact ⟨emitted.extension, checked.of_emits emitted (types le before _ _ rfl) (.of_run frames rfl)⟩

theorem ReplacementSitesFree.of_interval_runs {le : LEnv} {before : LS} {action : B α}
    (emitted : EmitsOnlyRun NotReplacement action) (types : TypeRun action)
    (frames : GeneratedIntervalFrameRun none targets action) :
    ReplacementSitesFree (root := root) (targets := targets) le before action := by
  intro checked
  have emitted := emitted le before _ _ rfl
  refine ⟨emitted.extension, checked.of_emits emitted (types le before _ _ rfl) ?_⟩
  intro cleared captured extension avoids framed
  exact (frames cleared captured le before _ _ extension trivial
    (by simpa [LoopBuilderFrameTargets] using avoids) framed rfl).1

private theorem emits_unchanged (action : B α)
    (same : ∀ le before, (action le before).2.blocks = before.blocks) : EmitsOnlyRun NotReplacement action := by
  intro le before result after run
  have same := same le before
  rw [run] at same
  exact .of_blocks same

theorem ReplacementSitesFree.recordValueRootRecipe (le : LEnv) (before : LS) (value : ValueId)
    (sourceScope : ScopeId) :
    ReplacementSitesFree (root := root) (targets := targets) le before
      (Goose.Lower.recordValueRootRecipe value sourceScope) := by
  refine .of_runs ?_ (types_recordValueRootRecipe value sourceScope)
    (generatedTargetFrame_recordValueRootRecipe none value sourceScope)
  apply emits_unchanged
  intro env state
  rw [recordValueRootRecipe_run]

private theorem emits_newBlock (types : List VTy) : EmitsOnlyRun NotReplacement (newBlock types) := by
  intro le before result after run
  rw [newBlock_run_general] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact (EmitsOnly.newBlock before _).trans (.of_blocks rfl)

private theorem emits_setCur (current : Option BlockId) : EmitsOnlyRun NotReplacement (setCur current) := by
  intro le before result after run
  cases run
  exact .of_blocks rfl

private theorem emits_patchTerm (block : BlockId) (term : Term) : EmitsOnlyRun NotReplacement (patchTerm block term) := by
  intro le before result after run
  rw [patchTerm_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact .append before block (.term term) trivial

private theorem emits_valTy (value : ValueId) : EmitsOnlyRun NotReplacement (valTy value) := by
  intro le before result after run
  have same := valTy_run value le before
  rw [run] at same
  change after = before at same
  rw [same]
  exact .refl _ _

private theorem emits_patchBrs (target : BlockId) (incoming : List (BlockId × ValueId)) :
    EmitsOnlyRun NotReplacement (patchBrs target incoming) := by
  induction incoming with
  | nil => exact .pure _ _
  | cons pair rest ih => exact (emits_patchTerm _ _).bind (fun _ => ih)

private theorem emits_patchBrs0 (target : BlockId) (incoming : List BlockId) :
    EmitsOnlyRun NotReplacement (patchBrs0 target incoming) := by
  induction incoming with
  | nil => exact .pure _ _
  | cons block rest ih => exact (emits_patchTerm _ _).bind (fun _ => ih)

theorem ReplacementSitesFree.fork (le : LEnv) (before : LS) (condition : ValueId) :
    ReplacementSitesFree (root := root) (targets := targets) le before (Goose.Lower.fork condition) := by
  refine .of_runs ?_ (types_fork condition) (generatedTargetFrame_fork none condition)
  unfold Goose.Lower.fork
  exact (emits_newBlock _).bind fun _ => (emits_newBlock _).bind fun _ =>
    (emitsOnly_emitTerm _ trivial).bind fun _ => .pure _ _

theorem ReplacementSitesFree.scFork (le : LEnv) (before : LS) (isAnd : Bool) (condition : ValueId) :
    ReplacementSitesFree (root := root) (targets := targets) le before (Goose.Lower.scFork isAnd condition) := by
  refine .of_runs ?_ (types_scFork isAnd condition) (generatedTargetFrame_scFork none isAnd condition)
  cases isAnd <;> unfold Goose.Lower.scFork
  all_goals exact (emits_newBlock _).bind fun _ => (emits_newBlock _).bind fun _ =>
    (emitsOnly_emitTerm _ trivial).bind fun _ => .pure _ _

theorem ReplacementSitesFree.joinValue (le : LEnv) (before : LS) (yes : Option BlockId) (yesValue : ValueId)
    (no : Option BlockId) (noValue : ValueId) :
    ReplacementSitesFree (root := root) (targets := targets) le before (Goose.Lower.joinValue yes yesValue no noValue) := by
  refine .of_runs ?_ (types_joinValue yes yesValue no noValue)
    (generatedTargetFrame_joinValue none yes no yesValue noValue)
  unfold Goose.Lower.joinValue
  split
  · exact (emits_setCur _).bind fun _ => .pure _ _
  · exact (emits_valTy _).bind fun _ => (emits_newBlock _).bind fun _ =>
      (emits_patchBrs _ _).bind fun _ => (emits_setCur _).bind fun _ => .pure _ _

theorem ReplacementSitesFree.joinArms (le : LEnv) (before : LS) (yes no : Option BlockId) :
    ReplacementSitesFree (root := root) (targets := targets) le before (Goose.Lower.joinArms yes no) := by
  refine .of_runs ?_ (types_joinArms yes no) (generatedTargetFrame_joinArms none yes no)
  unfold Goose.Lower.joinArms
  split
  · exact emits_setCur _
  · exact (emits_newBlock _).bind fun _ => (emits_patchBrs0 _ _).bind fun _ => emits_setCur _

theorem ReplacementSitesFree.finishFunction (le : LEnv) (before : LS) (impl : Core.Impl) (value : ValueId) :
    ReplacementSitesFree (root := root) (targets := targets) le before (Goose.Lower.finishFunction impl value) := by
  refine .of_interval_runs ?_ ?_ (generatedIntervalFrame_finishFunction none targets impl value)
  · unfold Goose.Lower.finishFunction
    refine (emits_unchanged (read : B LEnv) (by intros; rfl)).bind fun env =>
      (emits_unchanged Goose.Lower.isLive (by intros; rfl)).bind fun live => ?_
    cases live
    · exact .pure _ _
    · simp only [ite_true]
      split
      · exact (emits_newBlock _).bind fun pair => (emitsOnly_emitTerm _ trivial).bind fun _ =>
          (emits_setCur _).bind fun _ => emitsOnly_emitTerm _ trivial
      · exact emitsOnly_emitTerm _ trivial
  · unfold Goose.Lower.finishFunction
    refine TypeRun.bind types_read fun env => TypeRun.bind types_isLive fun live => ?_
    cases live
    · exact .pure _
    · simp only [ite_true]
      split
      · exact (types_newBlock _).bind fun pair => (types_emitTerm _).bind fun _ =>
          (types_setCur _).bind fun _ => types_emitTerm _
      · exact types_emitTerm _

end Goose.Lower.Validation
