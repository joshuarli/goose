import Goose.Proofs.ConstructionAcceptedNestedArgument

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

theorem AcceptedFrame.leaveOrdinaryOperand {config : EvalConfig} {accepted : AcceptedModule config}
    {frame : ConstructionSourceFrame} {before after : ExecutionState} {types : RootTypes}
    (source : AcceptedFrame config accepted frame before types) (fuel : Nat)
    (result : AcceptedFrame config accepted (ordinaryOperandFrame frame fuel) after types) :
    AcceptedFrame config accepted frame after types :=
  ⟨source.compatible, result.frontier, result.scopeFrontier, result.initializingBefore, result.aliases, result.locals,
    result.localTypes, result.uninitializedLocals, result.uninitializedTypes, result.futureGlobals, result.direct, result.contents⟩

theorem FirstArgumentOutcome.leaveOrdinaryOperand {config : EvalConfig} {accepted : AcceptedModule config}
    {frame : ConstructionSourceFrame} {before : ExecutionState} {types : RootTypes} {ambient : OwnershipAmbient}
    {live : Goose.Core.RootInst → Prop} {regions : List ReceivingRegion} {pending : List PendingCarrierFrame}
    (source : AcceptedFrame config accepted frame before types) (fuel : Nat) (ty : Ty) (step : ExecutionStep Value)
    (outcome : FirstArgumentOutcome config accepted (ordinaryOperandFrame frame fuel) ambient types live regions pending ty [] step) :
    FirstArgumentOutcome config accepted frame ambient types live regions pending ty [] step := by
  cases step with
  | escape address carriers after | jump target kind after => simp [FirstArgumentOutcome] at outcome
  | stop reason after =>
    have restored := source.leaveOrdinaryOperand fuel outcome.2.1
    simpa [ordinaryOperandFrame, FirstArgumentOutcome, Goose.Proofs.Exit.stepState] using
      And.intro outcome.1 (And.intro restored True.intro)
  | ok value after =>
    have restored := source.leaveOrdinaryOperand fuel outcome.2.1
    simpa [ordinaryOperandFrame, FirstArgumentOutcome, Goose.Proofs.Exit.stepState] using
      And.intro outcome.1 (And.intro restored outcome.2.2)

#print axioms AcceptedFrame.leaveOrdinaryOperand
#print axioms FirstArgumentOutcome.leaveOrdinaryOperand
end Goose.Proofs.ConstructionAcceptedExecution
