import Goose.Lower.Validation.EmittedMetadataControlSelected
import Goose.Lower.Validation.ExpressionTypingGenerated

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem EmittedMetadataAction.lowerBlock {le : LEnv} (loop : Option LoopCtx)
    (pre : List (SlotId × ValueId × OriginId)) (want : Bool) (body : Core.Block)
    (checked : EmittedMetadataRun le loop (Goose.Lower.lowerBlock loop pre want body)) :
    EmittedMetadataAction le loop (Goose.Lower.lowerBlock loop pre want body) :=
  ⟨checked, dense_lowerBlock loop pre want body, advB_lowerBlock loop pre want body,
    generatedTargets_lowerBlock loop pre want body, types_lowerBlock loop pre want body⟩

theorem metadata_source_emptyBlock {env : Core.TEnv} {results : List Ty} {body : Core.Block}
    (child : EmittedMetadataSourceBlock env results body) (resultTypes : EmittedMetadataResultTypes env results)
    {sourcePre : List (VarId × Ty)} {type : Ty} {start finish : Nat}
    (source : Core.tyBlock env sourcePre body start = .ok (type, finish))
    (loop : Option LoopCtx) (want : Bool) :
    EmittedMetadataAction (lowerEnv env.mod env.vars results) loop (lowerBlock loop [] want body) := by
  apply EmittedMetadataAction.lowerBlock
  intro before result after generated loopBounds loopTypes run checked
  exact child resultTypes source loop [] want before result after generated loopBounds loopTypes
    (by intro slot value origin member; cases member) run checked

theorem metadata_source_and {env : Core.TEnv} {results : List Ty} (left right : Expr)
    (leftChild : EmittedMetadataSourceExpression env results left)
    (rightChild : EmittedMetadataSourceExpression env results right) :
    EmittedMetadataSourceExpression env results (.and left right) := by
  intro resultTypes type start finish source before result after generated loopBounds loopTypes run checked
  obtain ⟨leftType, leftFinish, leftSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨unit, rightStart, leftBool, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨rightType, rightFinish, rightSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  have bool := (requireBool_ok _ _ _ _).mp leftBool |>.1
  subst leftType
  obtain ⟨value, middle, leftRun, tailRun⟩ := bind_eq.mp run
  have leftChecked := leftChild resultTypes leftSource before value middle generated trivial trivial leftRun checked
  have middleGenerated := generated.lowerExpr left leftRun
  have final := leftChecked.shortCircuit middleGenerated (loop := none) trivial trivial true value
    (fun active => lowerExpr_generated_typed left leftSource leftRun active generated)
    (EmittedMetadataAction.lowerExpr right (rightChild resultTypes rightSource))
  simpa only [tailRun] using final

theorem metadata_source_or {env : Core.TEnv} {results : List Ty} (left right : Expr)
    (leftChild : EmittedMetadataSourceExpression env results left)
    (rightChild : EmittedMetadataSourceExpression env results right) :
    EmittedMetadataSourceExpression env results (.or left right) := by
  intro resultTypes type start finish source before result after generated loopBounds loopTypes run checked
  obtain ⟨leftType, leftFinish, leftSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨unit, rightStart, leftBool, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨rightType, rightFinish, rightSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  have bool := (requireBool_ok _ _ _ _).mp leftBool |>.1
  subst leftType
  obtain ⟨value, middle, leftRun, tailRun⟩ := bind_eq.mp run
  have leftChecked := leftChild resultTypes leftSource before value middle generated trivial trivial leftRun checked
  have middleGenerated := generated.lowerExpr left leftRun
  have final := leftChecked.shortCircuit middleGenerated (loop := none) trivial trivial false value
    (fun active => lowerExpr_generated_typed left leftSource leftRun active generated)
    (EmittedMetadataAction.lowerExpr right (rightChild resultTypes rightSource))
  simpa only [tailRun] using final

theorem metadata_source_ifExpression {env : Core.TEnv} {results : List Ty}
    (condition : Expr) (yes no : Core.Block)
    (conditionChild : EmittedMetadataSourceExpression env results condition)
    (yesChild : ∀ env, EmittedMetadataSourceBlock env results yes)
    (noChild : ∀ env, EmittedMetadataSourceBlock env results no) :
    EmittedMetadataSourceExpression env results (.ifE condition yes no) := by
  intro resultTypes type start finish source before result after generated loopBounds loopTypes run checked
  obtain ⟨conditionType, conditionFinish, conditionSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨unit, yesStart, conditionBool, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨yesType, yesFinish, yesSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨noType, noFinish, noSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  have bool := (requireBool_ok _ _ _ _).mp conditionBool |>.1
  subst conditionType
  obtain ⟨value, middle, conditionRun, tailRun⟩ := bind_eq.mp run
  have conditionChecked := conditionChild resultTypes conditionSource before value middle generated trivial trivial conditionRun checked
  have middleGenerated := generated.lowerExpr condition conditionRun
  have final := conditionChecked.ifValue middleGenerated (loop := none) trivial trivial value
    (fun active => lowerExpr_generated_typed condition conditionSource conditionRun active generated)
    (metadata_source_emptyBlock (yesChild (Core.exprEnv env)) resultTypes yesSource none true)
    (metadata_source_emptyBlock (noChild (Core.exprEnv env)) resultTypes noSource none true)
  simpa only [tailRun] using final

theorem metadata_source_blockExpression {results : List Ty} (body : Core.Block)
    (child : ∀ env, EmittedMetadataSourceBlock env results body) :
    ∀ env, EmittedMetadataSourceExpression env results (.blockE body) := by
  intro env resultTypes type start finish source
  exact (metadata_source_emptyBlock (child (Core.exprEnv env)) resultTypes source none true).metadata

end Goose.Lower.Validation
