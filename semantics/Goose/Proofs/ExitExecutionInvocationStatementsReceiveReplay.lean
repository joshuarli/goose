import Goose.Proofs.ExitExecutionInvocationStatementsDefinitions

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

private theorem bind_step (action : EvalM α) (next : α → EvalM β) (state : ExecutionState) :
    (action >>= next) state = match action state with
      | .ok value after => next value after
      | .stop reason after => .stop reason after
      | .escape address carriers after => .escape address carriers after
      | .jump target kind after => .jump target kind after := rfl

theorem statementReceiveProduce_escape (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (localVars : List Goose.Core.VarId) (expression : Expr) (origin : Goose.Core.OriginId)
    (initial prepared : ExecutionState) (channels : List Channel)
    (setup : statementInvocation_statementReceivePrefix fuel config environment localVars expression origin initial = .ok channels prepared)
    (address : ExitAddress) (carriers : List Carrier) (before : ExecutionState)
    (escaped : evalProduce fuel config environment channels expression prepared = .escape address carriers before) :
    execStmt (fuel + 1) config environment (.receive localVars expression origin) initial = .escape address carriers before := by
  rw [execStmt]
  change ((statementInvocation_statementReceivePrefix fuel config environment localVars expression origin >>= _) initial) = _
  rw [bind_step, setup]
  dsimp only []
  rw [bind_step, escaped]

end Goose.Proofs.ExitExecution
