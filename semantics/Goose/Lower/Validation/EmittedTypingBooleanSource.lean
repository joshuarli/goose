import Goose.Lower.Validation.EmittedTypingSourceActions
import Goose.Lower.Validation.EmittedTypingGeneratedBranches

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem emitted_source_and {env : Core.TEnv} {results : List Ty} (left right : Expr)
    (leftChild : EmittedSourceExpression env results left) (rightChild : EmittedSourceExpression env results right) :
    EmittedSourceExpression env results (.and left right) := by
  intro type start finish source initial before generated builder
  obtain ⟨leftType, leftFinish, leftSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, rightStart, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨rightType, rightFinish, rightSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  let lhs := lowerExpr left (lowerEnv env.mod env.vars results) before
  have leftBuilder := leftChild leftSource generated builder
  have leftGenerated : GeneratedBuilderState lhs.2 := generated.lowerExpr left rfl
  have result := emitted_checked_generated_shortCircuit leftBuilder leftGenerated true lhs.1
    (value_lowerExpr left _ _ _ _ rfl) (lowerExpr right)
    (fun initial before builder generated => ⟨rightChild rightSource generated builder, generated.lowerExpr right rfl⟩)
    (advB_lowerExpr right) (value_lowerExpr right)
  exact result.1

theorem emitted_source_or {env : Core.TEnv} {results : List Ty} (left right : Expr)
    (leftChild : EmittedSourceExpression env results left) (rightChild : EmittedSourceExpression env results right) :
    EmittedSourceExpression env results (.or left right) := by
  intro type start finish source initial before generated builder
  obtain ⟨leftType, leftFinish, leftSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, rightStart, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨rightType, rightFinish, rightSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  let lhs := lowerExpr left (lowerEnv env.mod env.vars results) before
  have leftBuilder := leftChild leftSource generated builder
  have leftGenerated : GeneratedBuilderState lhs.2 := generated.lowerExpr left rfl
  have result := emitted_checked_generated_shortCircuit leftBuilder leftGenerated false lhs.1
    (value_lowerExpr left _ _ _ _ rfl) (lowerExpr right)
    (fun initial before builder generated => ⟨rightChild rightSource generated builder, generated.lowerExpr right rfl⟩)
    (advB_lowerExpr right) (value_lowerExpr right)
  exact result.1

end Goose.Lower.Validation
