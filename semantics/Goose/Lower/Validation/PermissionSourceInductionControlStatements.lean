import Goose.Lower.Validation.PermissionSourceInductionContracts
import Goose.Lower.Validation.PermissionInstructionControlIfStatements
import Goose.Lower.Validation.SourceStatementTyping

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem permission_source_conditional {env : Core.TEnv} {func : Func} {results : List Ty}
    (scope : ScopeId) (condition : Expr) (yes : Core.Block) (otherwise : Option Core.Block) (origin : OriginId)
    (conditionChild : PermissionStorageExprChild env func results condition)
    (yesChild : ∀ env, PermissionSourceBlock env func results yes)
    (otherwiseChild : ∀ body, otherwise = some body → ∀ env, PermissionSourceBlock env func results body) :
    PermissionSourceStatement env func results scope (.ifS condition yes otherwise origin) := by
  intro tables output start finish source first loop before after result generated frames floor run
  cases otherwise with
  | none =>
    obtain ⟨conditionFinish,yesType,yesFinish,conditionSource,yesSource,otherwiseSource,_⟩ := tyStmt_if_children source
    apply lowerIfNone_newPermissionInstructions generated floor frames
    · intro input output value generated floor lowered
      exact (conditionChild conditionSource generated lowered).weaken floor
    · intro input output value generated floor frames lowered
      exact yesChild env tables yesSource generated frames floor
        (by intro entry member; cases member) lowered
    · exact run
  | some no =>
    obtain ⟨conditionFinish,yesType,yesFinish,conditionSource,yesSource,otherwiseSource,_⟩ := tyStmt_if_children source
    obtain ⟨noType,noSource⟩ := otherwiseSource
    apply lowerIfSome_newPermissionInstructions generated floor frames
    · intro input output value generated floor lowered
      exact (conditionChild conditionSource generated lowered).weaken floor
    · intro input output value generated floor frames lowered
      exact yesChild env tables yesSource generated frames floor
        (by intro entry member; cases member) lowered
    · intro input output value generated floor frames lowered
      exact otherwiseChild no rfl env tables noSource generated frames floor
        (by intro entry member; cases member) lowered
    · exact run

#print axioms permission_source_conditional

end Goose.Lower.Validation
