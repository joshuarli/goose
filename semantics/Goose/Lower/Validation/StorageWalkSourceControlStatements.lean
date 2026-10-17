import Goose.Lower.Validation.StorageWalkSourceControlExpressions
import Goose.Lower.Validation.StorageWalkSourceControlLoops

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem storageWalk_source_conditional {env : Core.TEnv} {results : List Ty} {stack : List ScopeId}
    (scope : ScopeId) (condition : Expr) (yes : Core.Block) (otherwise : Option Core.Block) (origin : OriginId)
    (conditionChild : StorageWalkSourceExpression env results stack condition)
    (yesChild : ∀ env, StorageWalkSourceBlock env results stack yes)
    (otherwiseChild : ∀ body, otherwise = some body → ∀ env, StorageWalkSourceBlock env results stack body) :
    StorageWalkSourceStatement env results stack scope (.ifS condition yes otherwise origin) := by
  intro output start finish source visible active loop
  cases otherwise with
  | none =>
    obtain ⟨conditionFinish, yesType, yesFinish, conditionSource, yesSource, otherwiseSource, _⟩ := tyStmt_if_children source
    exact (conditionChild conditionSource visible loop).bind fun value =>
      StorageWalkAction.ifThen value (storageWalk_source_emptyBlock (yesChild env) yesSource visible loop false)
  | some no =>
    obtain ⟨conditionFinish, yesType, yesFinish, conditionSource, yesSource, otherwiseSource, _⟩ := tyStmt_if_children source
    obtain ⟨noType, noSource⟩ := otherwiseSource
    exact (conditionChild conditionSource visible loop).bind fun value =>
      StorageWalkAction.ifArms value
        (storageWalk_source_emptyBlock (yesChild env) yesSource visible loop false)
        (storageWalk_source_emptyBlock (otherwiseChild no rfl env) noSource visible loop false)

#print axioms storageWalk_source_conditional

end Goose.Lower.Validation
