import Goose.Proofs.ConstructionGhostSourceAggregate
import Goose.Proofs.ConstructionExecutionEventPrefix

namespace Goose.Proofs.ConstructionGhostSourceTrace
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual
open Goose.Proofs.ConstructionGhostSourceAggregate Goose.Proofs.ConstructionExecution
open Goose.Proofs.ConstructionInvocationReplay Goose.Proofs.ConstructionGhostInvocation

theorem sourceOperation_keepsEventPrefix (fuel : Nat) (config : EvalConfig)
    (operation : SourceOperation α) : KeepsEventPrefix (execute fuel config operation) := by
  have preserved := evaluation_keepsEventPrefix fuel config
  cases operation <;> simp only [execute] <;>
    first
    | exact preserved.value _ _
    | exact preserved.statement _ _
    | exact preserved.statements _ _
    | exact preserved.block _ _ _ _
    | exact preserved.resultBlock _ _ _
    | exact preserved.resultBlockWith _ _ _ _
    | exact preserved.activationBody _ _ _
    | exact preserved.activation _ _ _ _
    | exact preserved.call _ _ _ _ _
    | exact preserved.build _ _ _
    | exact preserved.bound _ _ _ _
    | exact preserved.place _ _
    | exact preserved.view _ _
    | exact preserved.loop _ _ _
    | exact preserved.whileLoop _ _ _
    | exact preserved.eachLoop _ _ _ _ _ _ _
    | exact preserved.rangeLoop _ _ _ _ _ _
    | exact preserved.printArgument _ _
    | exact preserved.element _ _ _ _
    | exact preserved.arguments _ _ _ _
    | exact preserved.produce _ _ _
    | exact preserved.operands _ _ _

theorem sourceHistory_eventPrefix (history : SourceHistory config fuel path operation before outcome) :
    EventPrefix before.construction.events
      (Goose.Proofs.Exit.stepState outcome).construction.events := by
  have preserved := sourceOperation_keepsEventPrefix fuel config operation before
  rw [history.sound] at preserved
  exact preserved

theorem aggregate_replay_eventPrefixes (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (path : List Nat) (expression : Expr) (operands : List Expr) (before : ExecutionState)
    (shape : ValueAggregate expression operands)
    (supported : ∀ operand ∈ operands, SupportedOperation config (.value environment operand)) :
    ∃ mapped visits,
      OperandReplay (evalValue fuel config environment) 0 operands [] before mapped visits ∧
      (∀ visit ∈ visits, SourceHistory config fuel (path ++ [visit.ordinal])
        (.value environment visit.operand) visit.before visit.outcome ∧
        EventPrefix visit.before.construction.events
          (Goose.Proofs.Exit.stepState visit.outcome).construction.events) ∧
      visits.map Invocation.operand = operands.take visits.length ∧
      (visits.map Invocation.ordinal).Nodup ∧
      evalValue (fuel + 1) config environment expression before = aggregateResult expression mapped := by
  obtain ⟨mapped, visits, replay, children, ordered, once, execution, history⟩ :=
    aggregate_replay fuel config environment path expression operands before shape supported
  refine ⟨mapped, visits, replay, ?_, ordered, once, execution⟩
  intro visit member
  exact ⟨children visit member, sourceHistory_eventPrefix (children visit member)⟩

#print axioms sourceOperation_keepsEventPrefix
#print axioms sourceHistory_eventPrefix
#print axioms aggregate_replay_eventPrefixes

end Goose.Proofs.ConstructionGhostSourceTrace
