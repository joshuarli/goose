import Goose.Proofs.ExitExecutionInvocationStatementsCauses
import Goose.Proofs.ExitExecutionInvocationStatementsNative

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

private theorem breakTarget_escape_inv (act : Goose.Core.ActId) (scope : BreakScope)
    (channels : List Channel) (action : EvalM α) (receive : JumpKind → EvalM α)
    (never : ∀ kind, ProducerNeverEscapes (receive kind))
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : withBreakTarget act scope channels action receive initial = .escape address carriers final) :
    ∃ before, action { initial with nextScope := initial.nextScope + 1, breaks := ⟨initial.nextScope, act, scope, channels⟩ :: initial.breaks } = .escape address carriers before := by
  cases evaluated : action { initial with nextScope := initial.nextScope + 1, breaks := ⟨initial.nextScope, act, scope, channels⟩ :: initial.breaks } with
  | ok value after | stop reason after =>
      simp only [withBreakTarget, evaluated, mapStepState] at escaped
      cases escaped
  | escape target payload after =>
      simp only [withBreakTarget, evaluated, mapStepState, ExecutionStep.escape.injEq] at escaped
      rcases escaped with ⟨rfl, rfl, _⟩
      exact ⟨after, rfl⟩
  | jump target kind after =>
      simp only [withBreakTarget, evaluated, mapStepState] at escaped
      split at escaped
      · exact False.elim (never kind _ address carriers final escaped)
      · cases escaped

private theorem loopReceive_neverEscapes (kind : JumpKind) :
    ProducerNeverEscapes ((do
      match kind with
      | .continueLoop => pure .continuing
      | .breakValue [] => pure (.breaking none)
      | .breakValue carriers => pure (.breaking (some (← carrierValue (← singleCarrier carriers))))) : EvalM Flow) := by
  cases kind with
  | continueLoop => exact producerNeverEscapes_pure _
  | breakValue carriers =>
      cases carriers with
      | nil => exact producerNeverEscapes_pure _
      | cons carrier carriers =>
          apply producerNeverEscapes_bind
          · exact producerNeverEscapes_singleCarrier _
          · intro selected
            apply producerNeverEscapes_bind
            · exact producerNeverEscapes_carrierValue _
            · intro value
              exact producerNeverEscapes_pure _

theorem statementLoopBlock_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (body : Block) (initial final : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier)
    (escaped : loopBody fuel config environment pre body initial = .escape address carriers final) :
    StatementCausalChild config (.loop fuel environment pre body) initial address carriers := by
  cases fuel with
  | zero =>
      simp only [loopBody, timeout, EvalM.stop] at escaped
      cases escaped
  | succ fuel =>
      rw [loopBody] at escaped
      obtain ⟨before, child⟩ := breakTarget_escape_inv environment.act .loop []
        (execBlock fuel config environment pre [] body) _ loopReceive_neverEscapes
        initial final address carriers escaped
      exact ⟨Flow, .block fuel environment pre [] body, _, before,
        .loopBlock fuel environment pre body initial, child⟩

end Goose.Proofs.ExitExecution
