import Goose.Proofs.ConstructionGhostCallArgumentEvents

namespace Goose.Proofs.ConstructionGhostArgumentHistoryInversion
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual
open Goose.Proofs.ConstructionGhostCallArgumentEvents Goose.Proofs.ConstructionGhostCallArguments
open Goose.Proofs.ConstructionGhostArguments Goose.Proofs.ConstructionExecution

def argumentsSyntax : SourceOperation α → Option (RuntimeActivation × Array LocalVar × List Param × List Arg)
  | .arguments environment vars parameters arguments => some (environment, vars, parameters, arguments)
  | _ => none

theorem byValue_head_history {config : EvalConfig} {α : Type} {fuel : Nat} {path : List Nat}
    {operation : SourceOperation α} {before : ExecutionState} {outcome : ExecutionStep α}
    (history : SourceHistory config fuel path operation before outcome) (sourceFuel : Nat)
    (environment : RuntimeActivation) (vars : Array LocalVar) (parameter : Param) (parameters : List Param)
    (operand : Expr) (arguments : List Arg)
    (fuelEq : fuel = sourceFuel + 1)
    (operationEq : argumentsSyntax operation = some (environment, vars, parameter :: parameters, .byVal operand :: arguments)) :
    SourceHistory config sourceFuel (path ++ [0]) (.value environment operand) before
      (evalValue sourceFuel config environment operand before) := by
  cases history <;> simp_all [argumentsSyntax]
  case argumentValue =>
    rename_i child
    have actual := child.sound
    simp only [execute] at actual
    rw [actual]
    exact child

theorem byValue_head_source (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (path : List Nat) (vars : Array LocalVar) (parameter : Param) (parameters : List Param)
    (operand : Expr) (arguments : List Arg) (before : ExecutionState) (outcome : ExecutionStep (List Value))
    (visits : List ArgumentInvocation) (callResult : ExecutionStep (List Carrier))
    (history : SourceHistory config (fuel + 1) path (.arguments environment vars (parameter :: parameters) (.byVal operand :: arguments)) before outcome)
    (replay : ArgumentReplay config environment vars (fuel + 1) 0 (parameter :: parameters) (.byVal operand :: arguments) before outcome visits)
    (callPrefix : ∀ visit ∈ visits, EventPrefix (Goose.Proofs.Exit.stepState visit.outcome).construction.events
      (Goose.Proofs.Exit.stepState callResult).construction.events) :
    SourceHistory config fuel (path ++ [0]) (.value environment operand) before (evalValue fuel config environment operand before) ∧
    EventPrefix (Goose.Proofs.Exit.stepState (evalValue fuel config environment operand before)).construction.events
      (Goose.Proofs.Exit.stepState callResult).construction.events := by
  refine ⟨byValue_head_history history fuel environment vars parameter parameters operand arguments rfl rfl, ?_⟩
  cases replay with
  | next head tail =>
      have kept := callPrefix _ (List.mem_cons_self)
      simp only [argumentValue] at head
      rw [head]
      exact kept
  | stopped head | escaped head | jumped head =>
      have kept := callPrefix _ (List.mem_singleton_self _)
      simp only [argumentValue] at head
      rw [head]
      exact kept

theorem byValue_head_invokeCall (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (path : List Nat) (context : Goose.Core.ContextId) (parameter : Param) (parameters : List Param)
    (operand : Expr) (arguments : List Arg) (channels : List Channel) (origin : Goose.Core.OriginId)
    (callBefore before : ExecutionState) (id : Goose.Core.ImplId) (implementation : Impl)
    (callableChannels : List Channel) (outcome : ExecutionStep (List Value)) (visits : List ArgumentInvocation)
    (params : implementation.params.toList = parameter :: parameters)
    (history : SourceHistory config (fuel + 1) path (.arguments environment implementation.vars (parameter :: parameters) (.byVal operand :: arguments)) before outcome)
    (replay : ArgumentReplay config environment implementation.vars (fuel + 1) 0 (parameter :: parameters) (.byVal operand :: arguments) before outcome visits)
    (execution : invokeCall (fuel + 2) config environment context (.byVal operand :: arguments) channels origin callBefore =
      callArgumentsContinuation (fuel + 1) config id implementation channels callableChannels origin outcome) :
    SourceHistory config fuel (path ++ [0]) (.value environment operand) before (evalValue fuel config environment operand before) ∧
    EventPrefix (Goose.Proofs.Exit.stepState (evalValue fuel config environment operand before)).construction.events
      (Goose.Proofs.Exit.stepState (invokeCall (fuel + 2) config environment context (.byVal operand :: arguments) channels origin callBefore)).construction.events := by
  apply byValue_head_source fuel config environment path implementation.vars parameter parameters operand arguments before outcome visits _ history replay
  intro visit member
  apply invokeCall_argumentVisitPrefix (fuel + 1) config environment context (.byVal operand :: arguments) channels origin
    callBefore before id implementation callableChannels outcome visits visit
  · simpa [params] using replay
  · exact member
  · exact execution

#print axioms byValue_head_invokeCall
#print axioms byValue_head_source
#print axioms byValue_head_history
end Goose.Proofs.ConstructionGhostArgumentHistoryInversion
