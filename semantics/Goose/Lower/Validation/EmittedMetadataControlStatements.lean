import Goose.Lower.Validation.EmittedMetadataControlExpressions
import Goose.Lower.Validation.EmittedMetadataControlHeaders
import Goose.Lower.Validation.SourceStatementTypingTransfers

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem metadata_source_conditional {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (condition : Expr) (yes : Core.Block) (otherwise : Option Core.Block) (origin : OriginId)
    (conditionChild : EmittedMetadataSourceExpression env results condition)
    (yesChild : ∀ env, EmittedMetadataSourceBlock env results yes)
    (otherwiseChild : ∀ body, otherwise = some body → ∀ env, EmittedMetadataSourceBlock env results body) :
    EmittedMetadataSourceStatement env results scope (.ifS condition yes otherwise origin) := by
  intro resultTypes output start finish source loop before result after generated loopBounds loopTypes run checked
  cases otherwise with
  | none =>
    obtain ⟨conditionFinish, yesType, yesFinish, conditionSource, yesSource, otherwiseSource, _⟩ := tyStmt_if_children source
    simp only [lowerStmt] at run
    obtain ⟨value, middle, conditionRun, tailRun⟩ := bind_eq.mp run
    have conditionChecked := conditionChild resultTypes conditionSource before value middle generated trivial trivial conditionRun checked
    have middleGenerated := generated.lowerExpr condition conditionRun
    have middleBounds := loopBounds.mono (advB_lowerExpr condition _ before _ _ conditionRun).ext.1
    have middleTypes := loopTypes.retained (types_lowerExpr condition _ before _ _ conditionRun)
    have conditionTyped := fun active => lowerExpr_generated_typed condition conditionSource conditionRun active generated
    have final := conditionChecked.ifThen middleGenerated middleBounds middleTypes value conditionTyped
      (metadata_source_emptyBlock (yesChild env) resultTypes yesSource loop false)
    simpa only [tailRun] using final
  | some no =>
    obtain ⟨conditionFinish, yesType, yesFinish, conditionSource, yesSource, otherwiseSource, _⟩ := tyStmt_if_children source
    obtain ⟨noType, noSource⟩ := otherwiseSource
    simp only [lowerStmt] at run
    obtain ⟨value, middle, conditionRun, tailRun⟩ := bind_eq.mp run
    have conditionChecked := conditionChild resultTypes conditionSource before value middle generated trivial trivial conditionRun checked
    have middleGenerated := generated.lowerExpr condition conditionRun
    have middleBounds := loopBounds.mono (advB_lowerExpr condition _ before _ _ conditionRun).ext.1
    have middleTypes := loopTypes.retained (types_lowerExpr condition _ before _ _ conditionRun)
    have conditionTyped := fun active => lowerExpr_generated_typed condition conditionSource conditionRun active generated
    have final := conditionChecked.ifArms middleGenerated middleBounds middleTypes value conditionTyped
      (metadata_source_emptyBlock (yesChild env) resultTypes yesSource loop false)
      (metadata_source_emptyBlock (otherwiseChild no rfl env) resultTypes noSource loop false)
    simpa only [tailRun] using final

theorem metadata_source_assert {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (condition : Expr) (origin : OriginId) (child : EmittedMetadataSourceExpression env results condition) :
    EmittedMetadataSourceStatement env results scope (.assertS condition origin) := by
  intro resultTypes output start finish source loop before result after generated loopBounds loopTypes run checked
  have conditionSource := (tyStmt_assert_children source).1
  simp only [lowerStmt] at run
  obtain ⟨value, middle, conditionRun, tailRun⟩ := bind_eq.mp run
  have conditionChecked := child resultTypes conditionSource before value middle generated trivial trivial conditionRun checked
  cases live : middle.cur with
  | none =>
    rw [whenLive_none _ _ _ live] at tailRun
    obtain ⟨_, rfl⟩ := Prod.mk.inj tailRun
    exact conditionChecked
  | some block =>
    rw [whenLive_some _ _ _ live] at tailRun
    have forked := conditionChecked.fork value (fun active => lowerExpr_generated_typed condition conditionSource conditionRun active generated)
    have selected := forked.setCur (some (Goose.Lower.fork value (lowerEnv env.mod env.vars results) middle).1.2)
    have terminated := selected.emitTerm (.abort .assert (some origin)) (fun _ => .abort _ _)
    have final := terminated.setCur (some (Goose.Lower.fork value (lowerEnv env.mod env.vars results) middle).1.1)
    have same := congrArg Prod.snd tailRun
    simp only [bind_run] at same
    rw [← same]
    exact final

theorem metadata_source_while {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (condition : Expr) (body : Core.Block) (origin : OriginId)
    (conditionChild : EmittedMetadataSourceExpression env results condition)
    (bodyChild : ∀ env, EmittedMetadataSourceBlock env results body) :
    EmittedMetadataSourceStatement env results scope (.while condition body origin) := by
  intro resultTypes output start finish source loop before result after generated loopBounds loopTypes run checked
  obtain ⟨conditionFinish, bodyType, conditionSource, bodySource, _⟩ := tyStmt_while_children source
  have lowered := metadata_control_whileHeader checked generated (lowerExpr condition)
    (fun header depth target => lowerBlock (some ⟨depth, target, .jump header⟩) [] false body)
    (fun state checked generated =>
      ⟨conditionChild resultTypes conditionSource state _ _ generated trivial trivial rfl checked,
        generated.lowerExpr condition rfl⟩)
    (fun state value after generated run active => lowerExpr_generated_typed condition conditionSource run active generated)
    (advB_lowerExpr condition)
    (fun header depth target state checked generated headerBound targetBound active => by
      have targets : LoopBuilderTargets (some ⟨depth, target, .jump header⟩) state := ⟨targetBound, headerBound⟩
      have bodyChecked := (metadata_source_emptyBlock (bodyChild {env with loops := env.loops + 1}) resultTypes bodySource
        (some ⟨depth, target, .jump header⟩) false).metadata state _ _ generated targets trivial rfl checked
      exact ⟨bodyChecked, generated.lowerBlock _ [] false body targets rfl⟩)
    (fun header depth target => advB_lowerBlock (some ⟨depth, target, .jump header⟩) [] false body)
    (fun header depth target => types_lowerBlock (some ⟨depth, target, .jump header⟩) [] false body)
  simp only [lowerStmt] at run
  simpa only [run] using lowered.1

end Goose.Lower.Validation
