import Goose.Proofs.OwnershipRuntimeIdentitiesPreservation

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership

open Goose.Construct
open Goose.Core (VarId)

theorem preservesOwnershipRuntimeIdentities_execResultScope (environment : RuntimeActivation)
    (pre : List (VarId × Value)) (channels : List Channel) (block : Block)
    (statementsAction : RuntimeActivation → List Stmt → EvalM Flow)
    (tailAction : RuntimeActivation → Expr → EvalM (List Carrier))
    (statementsPreserved : ∀ runtime statements, PreservesOwnershipRuntimeIdentities (statementsAction runtime statements))
    (tailPreserved : ∀ runtime expression, PreservesOwnershipRuntimeIdentities (tailAction runtime expression)) :
    PreservesOwnershipRuntimeIdentities (execResultScope environment pre channels block statementsAction tailAction) := by
  cases block with
  | mk scope statements value =>
    unfold execResultScope
    apply preservesOwnershipRuntimeIdentities_bind
    · exact preservesOwnershipRuntimeIdentities_freshScope
    · intro scopeInst
      apply preservesOwnershipRuntimeIdentities_get_bind
      intro state valid
      let runtime : RuntimeActivation := {environment with scopes := (scope, scopeInst) :: environment.scopes}
      let mapped : ExecutionState := {state with activations := state.activations.map (fun current : RuntimeActivation =>
        if current.act == environment.act then {current with scopes := runtime.scopes} else current)}
      have mappedValid : OwnershipRuntimeIdentities mapped :=
        ownershipRuntimeIdentities_scopes valid environment runtime.scopes
      change OwnershipRuntimeIdentities (Goose.Proofs.Exit.stepState
        (withScope environment scope scopeInst _ mapped))
      refine preservesOwnershipRuntimeIdentities_withScope environment scope scopeInst _ ?_ mapped mappedValid
      apply preservesOwnershipRuntimeIdentities_bind
      · exact preservesOwnershipRuntimeIdentities_bindAll _ _ _
      · intro _
        apply preservesOwnershipRuntimeIdentities_bind
        · exact statementsPreserved runtime statements
        · intro flow
          cases flow with
          | normal result =>
            cases value with
            | some expression =>
              dsimp only
              apply preservesOwnershipRuntimeIdentities_bind
              · exact tailPreserved runtime expression
              · intro _; exact preservesOwnershipRuntimeIdentities_pure _
            | none =>
              dsimp only
              split
              · exact preservesOwnershipRuntimeIdentities_pure _
              · split
                · exact preservesOwnershipRuntimeIdentities_pure _
                · exact preservesOwnershipRuntimeIdentities_stop (.fault .arity)
          | breaking result | continuing => dsimp only; exact preservesOwnershipRuntimeIdentities_pure _

#print axioms preservesOwnershipRuntimeIdentities_execResultScope

end Goose.Proofs.ConstructionExecutionOwnership
