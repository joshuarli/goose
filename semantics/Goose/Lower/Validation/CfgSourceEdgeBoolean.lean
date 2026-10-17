import Goose.Lower.Validation.CfgSourceEdgeContracts

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem cfg_source_and {env : Core.TEnv} {results : List Ty} (left right : Expr)
    (leftChild : CfgSourceExpression env results left) (rightChild : CfgSourceExpression env results right) :
    CfgSourceExpression env results (.and left right) := by
  intro output start finish source
  simp only [Core.tyExpr] at source
  obtain ⟨leftTy, leftFinish, leftSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, rightStart, leftBoolean, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨rightTy, rightFinish, rightSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, _, rightBoolean, source⟩ := (st_bind_ok _ _ _ _).mp source
  have leftBool := (requireBool_ok _ _ _ _).mp leftBoolean
  have rightBool := (requireBool_ok _ _ _ _).mp rightBoolean
  rw [leftBool.1] at leftSource
  rw [rightBool.1] at rightSource
  intro before result after run generated loop checked
  obtain ⟨value, middle, leftRun, tail⟩ := bind_eq.mp run
  obtain ⟨middleGenerated, firstExtension, middleChecked⟩ := leftChild leftSource before value middle leftRun generated loop checked
  obtain ⟨afterGenerated, finalExtension, afterChecked⟩ := generated_edge_shortCircuit_at _ none true value
    (rightChild rightSource)
    (fun before result after lowered generated live => lowerExpr_generated_typed right rightSource lowered live generated)
    middle after result tail middleGenerated trivial middleChecked
    (fun live => lowerExpr_generated_typed left leftSource leftRun live generated)
  exact ⟨afterGenerated, firstExtension.trans finalExtension, afterChecked⟩

theorem cfg_source_or {env : Core.TEnv} {results : List Ty} (left right : Expr)
    (leftChild : CfgSourceExpression env results left) (rightChild : CfgSourceExpression env results right) :
    CfgSourceExpression env results (.or left right) := by
  intro output start finish source
  simp only [Core.tyExpr] at source
  obtain ⟨leftTy, leftFinish, leftSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, rightStart, leftBoolean, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨rightTy, rightFinish, rightSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, _, rightBoolean, source⟩ := (st_bind_ok _ _ _ _).mp source
  have leftBool := (requireBool_ok _ _ _ _).mp leftBoolean
  have rightBool := (requireBool_ok _ _ _ _).mp rightBoolean
  rw [leftBool.1] at leftSource
  rw [rightBool.1] at rightSource
  intro before result after run generated loop checked
  obtain ⟨value, middle, leftRun, tail⟩ := bind_eq.mp run
  obtain ⟨middleGenerated, firstExtension, middleChecked⟩ := leftChild leftSource before value middle leftRun generated loop checked
  obtain ⟨afterGenerated, finalExtension, afterChecked⟩ := generated_edge_shortCircuit_at _ none false value
    (rightChild rightSource)
    (fun before result after lowered generated live => lowerExpr_generated_typed right rightSource lowered live generated)
    middle after result tail middleGenerated trivial middleChecked
    (fun live => lowerExpr_generated_typed left leftSource leftRun live generated)
  exact ⟨afterGenerated, firstExtension.trans finalExtension, afterChecked⟩

theorem cfg_source_ifExpression {env : Core.TEnv} {results : List Ty} (condition : Expr) (yes no : Core.Block)
    (conditionChild : CfgSourceExpression env results condition)
    (yesChild : CfgSourceBlock (Core.exprEnv env) results yes)
    (noChild : CfgSourceBlock (Core.exprEnv env) results no) :
    CfgSourceExpression env results (.ifE condition yes no) := by
  intro output start finish source
  simp only [Core.tyExpr] at source
  obtain ⟨conditionTy, conditionFinish, conditionSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, yesStart, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨yesTy, noStart, yesSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨noTy, tailStart, noSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  by_cases same : (yesTy == noTy) = true
  · have typesEqual : yesTy = noTy := eq_of_beq same
    subst noTy
    exact (conditionChild conditionSource).bind fun value => generated_edge_ifE_core _ none value (.data yesTy)
      (yesChild yesSource none [] true) (noChild noSource none [] true)
      (fun before value after run generated live => lowerBlock_generated_typed yes yesSource run live generated)
      (fun before value after run generated live => lowerBlock_generated_typed no noSource run live generated)
  · simp only [same] at source
    obtain ⟨_, _, rejected, _⟩ := (st_bind_ok _ _ _ _).mp source
    exact (rej_ok _ _ _ _).mp rejected |>.elim

theorem cfg_source_blockExpression {env : Core.TEnv} {results : List Ty} (body : Core.Block)
    (child : CfgSourceBlock (Core.exprEnv env) results body) :
    CfgSourceExpression env results (.blockE body) := by
  intro output start finish source
  exact child source none [] true

end Goose.Lower.Validation
