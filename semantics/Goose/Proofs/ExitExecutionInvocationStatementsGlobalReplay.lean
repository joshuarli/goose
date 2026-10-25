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

private theorem bind_assoc (action : EvalM α) (next : α → EvalM β) (last : β → EvalM γ) :
    ((action >>= next) >>= last) = (action >>= fun value => next value >>= last) := by
  funext state
  cases evaluated : action state <;> simp only [bind, evaluated]

private theorem bind_pure (value : α) (next : α → EvalM β) :
    ((pure value : EvalM α) >>= next) = next value := rfl

theorem statementGlobal_next_action (fuel : Nat) (config : EvalConfig) (global : Goose.Core.GlobalId)
    (globals : List Goose.Core.GlobalId) :
    initGlobals fuel config (global :: globals) = ((do
      let value ← statementInvocation_globalValuePrefix fuel config global
      bindRoot (.global global) value
      initGlobals fuel config globals) : EvalM Unit) := by
  rw [initGlobals]
  unfold statementInvocation_globalValuePrefix statementInvocation_globalEnvironmentPrefix
  cases config.module.globals[global]? with
  | none =>
      simp only [fault, EvalM.stop, bind]
      rfl
  | some descriptor =>
      simp only [bind_assoc, bind_pure]
      congr 1
      funext act
      split
      · simp only [bind_assoc]
        congr 1
        funext materialized
        cases materialized <;> simp only [bind_assoc]
      · rfl

theorem statementGlobalNext_escape (fuel : Nat) (config : EvalConfig) (global : Goose.Core.GlobalId)
    (globals : List Goose.Core.GlobalId) (initial prepared : ExecutionState)
    (setup : ((do
      let value ← statementInvocation_globalValuePrefix fuel config global
      bindRoot (.global global) value) : EvalM Unit) initial = .ok () prepared)
    (address : ExitAddress) (carriers : List Carrier) (before : ExecutionState)
    (escaped : initGlobals fuel config globals prepared = .escape address carriers before) :
    initGlobals fuel config (global :: globals) initial = .escape address carriers before := by
  rw [statementGlobal_next_action]
  rw [← bind_assoc]
  rw [bind_step, setup]
  dsimp only []
  exact escaped

end Goose.Proofs.ExitExecution
