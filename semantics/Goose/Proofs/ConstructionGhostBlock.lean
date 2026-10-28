import Goose.Proofs.ConstructionGhostStatements

namespace Goose.Proofs.ConstructionGhostBlock
open Goose.Construct Goose.Proofs.ConstructionGhostStatements

def blockContinuation (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channels : List Channel) (value : Option Expr) (statements : ExecutionStep Flow) : ExecutionStep Flow :=
  match statements with
  | .ok flow state => (match flow, value with
      | .normal _, some expression => do
          if channels.isEmpty then pure (Flow.normal (← evalValue fuel config environment expression))
          else pure (Flow.normal (← carrierValue (← singleCarrier (← evalProduce fuel config environment channels expression))))
      | flow, _ => pure flow) state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

theorem execBlock_statementReplay (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (channels : List Channel) (scope : Nat)
    (statements : List Stmt) (value : Option Expr) (before ready : ExecutionState)
    (bound : bindAll environment.act before.nextScope pre
      { before with nextScope := before.nextScope + 1 } = .ok () ready) :
    ∃ outcome visits,
      StatementReplay config { environment with scopes := (scope, before.nextScope) :: environment.scopes }
        fuel 0 statements ready outcome visits ∧
      execBlock (fuel + 1) config environment pre channels (.mk scope statements value) before =
        withScope environment scope before.nextScope (fun _ => blockContinuation fuel config
          { environment with scopes := (scope, before.nextScope) :: environment.scopes }
          channels value outcome) { before with nextScope := before.nextScope + 1 } := by
  obtain ⟨visits, replay⟩ := statementReplay_exists fuel config
    { environment with scopes := (scope, before.nextScope) :: environment.scopes } 0 statements ready
  refine ⟨_, visits, replay, ?_⟩
  simp only [execBlock, freshScope, EvalM.get, EvalM.set, bind, pure, withScope, bound, blockContinuation]
  cases result : execStmts fuel config
    { environment with scopes := (scope, before.nextScope) :: environment.scopes } statements ready <;> rfl

private def witnessConfig : EvalConfig := ⟨.release, ⟨#[], #[], #[], #[], #[], 0, #[], #[], #[]⟩⟩
private def witnessEnvironment : RuntimeActivation := ⟨0, 4, #[], [], []⟩
private def witnessBlock : Block := .mk 1
  [.print [.text "before"] 0, .abort "stop" 0, .print [.text "after"] 0] none
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

theorem blockWitness_sideEffect :
    ∃ state, execBlock 20 witnessConfig witnessEnvironment [] [] witnessBlock .initial =
      .stop (.abort .userAbort 0) state ∧
      state.construction.stdout.data.toList = [98, 101, 102, 111, 114, 101, 10] := by
  refine ⟨stepState (execBlock 20 witnessConfig witnessEnvironment [] [] witnessBlock .initial), ?_, ?_⟩ <;>
    unfold witnessConfig witnessEnvironment witnessBlock stepState <;> cbv

#print axioms blockWitness_sideEffect
#print axioms execBlock_statementReplay
end Goose.Proofs.ConstructionGhostBlock
