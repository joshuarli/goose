import Goose.Lower.Validation.PermissionSourceInductionContracts
import Goose.Lower.Validation.PermissionInstructionControlBranches

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem permission_source_and {env : Core.TEnv} {func : Func} {results : List Ty}
    (left right : Expr) (leftChild : PermissionStorageExprChild env func results left)
    (rightChild : PermissionStorageExprChild env func results right) :
    PermissionStorageExprChild env func results (.and left right) := by
  intro type start finish source before after result generated run
  obtain ⟨leftType, leftFinish, leftSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨checked, rightStart, leftBool, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨rightType, rightFinish, rightSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨value, middle, leftRun, tailRun⟩ := bind_eq.mp run
  have middleGenerated := generated.lowerExpr left leftRun
  have tail := shortCircuit_newPermissionInstructions middleGenerated
    (advB_lowerExpr left _ _ _ _ leftRun).vals (dense_lowerExpr right) (advB_lowerExpr right)
    (fun input value output generated lowered => rightChild rightSource generated lowered) tailRun
  exact (leftChild leftSource generated leftRun).compose_framed tail tailRun
    (dense_shortCircuit true value (dense_lowerExpr right))
    (advB_shortCircuit true value (advB_lowerExpr right))
    (types_shortCircuit true value (types_lowerExpr right))
    (generatedTargetFrame_shortCircuit none true value (generatedTargetFrame_lowerExpr none right)) middleGenerated trivial

theorem permission_source_or {env : Core.TEnv} {func : Func} {results : List Ty}
    (left right : Expr) (leftChild : PermissionStorageExprChild env func results left)
    (rightChild : PermissionStorageExprChild env func results right) :
    PermissionStorageExprChild env func results (.or left right) := by
  intro type start finish source before after result generated run
  obtain ⟨leftType, leftFinish, leftSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨checked, rightStart, leftBool, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨rightType, rightFinish, rightSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨value, middle, leftRun, tailRun⟩ := bind_eq.mp run
  have middleGenerated := generated.lowerExpr left leftRun
  have tail := shortCircuit_newPermissionInstructions middleGenerated
    (advB_lowerExpr left _ _ _ _ leftRun).vals (dense_lowerExpr right) (advB_lowerExpr right)
    (fun input value output generated lowered => rightChild rightSource generated lowered) tailRun
  exact (leftChild leftSource generated leftRun).compose_framed tail tailRun
    (dense_shortCircuit false value (dense_lowerExpr right))
    (advB_shortCircuit false value (advB_lowerExpr right))
    (types_shortCircuit false value (types_lowerExpr right))
    (generatedTargetFrame_shortCircuit none false value (generatedTargetFrame_lowerExpr none right)) middleGenerated trivial

theorem permission_source_ifExpression {env : Core.TEnv} {func : Func} {results : List Ty}
    (condition : Expr) (yes no : Core.Block) (tables : PermissionSourceTables env results func)
    (conditionChild : PermissionStorageExprChild env func results condition)
    (yesChild : ∀ env, PermissionSourceBlock env func results yes)
    (noChild : ∀ env, PermissionSourceBlock env func results no) :
    PermissionStorageExprChild env func results (.ifE condition yes no) := by
  intro type start finish source before after result generated run
  obtain ⟨conditionType, conditionFinish, conditionSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨checked, yesStart, conditionBool, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨yesType, yesFinish, yesSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨noType, noFinish, noSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  apply lowerIf_newPermissionInstructions generated (Nat.le_refl _)
  · intro input output value generated floor lowered
    exact (conditionChild conditionSource generated lowered).weaken floor
  · intro input output value generated floor lowered
    exact yesChild (Core.exprEnv env) (tables.retained rfl rfl) yesSource (loop := none) (pre := []) (want := true) generated trivial floor
      (by intro entry member; cases member) lowered
  · intro input output value generated floor lowered
    exact noChild (Core.exprEnv env) (tables.retained rfl rfl) noSource (loop := none) (pre := []) (want := true) generated trivial floor
      (by intro entry member; cases member) lowered
  · exact run

theorem permission_source_blockExpression {env : Core.TEnv} {func : Func} {results : List Ty}
    (body : Core.Block) (tables : PermissionSourceTables env results func)
    (child : ∀ env, PermissionSourceBlock env func results body) :
    PermissionStorageExprChild env func results (.blockE body) := by
  intro type start finish source before after result generated run
  exact child (Core.exprEnv env) (tables.retained rfl rfl) source (loop := none) (pre := []) (want := true) generated trivial (Nat.le_refl _)
    (by intro entry member; cases member) run

#print axioms permission_source_and
#print axioms permission_source_or
#print axioms permission_source_ifExpression
#print axioms permission_source_blockExpression

end Goose.Lower.Validation
