import Goose.Proofs.ConstructionAcceptedUnusedScopeRoots
import Goose.Proofs.ConstructionAcceptedRegisterBreakOutcome

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

theorem withUnusedScope_outcome {α : Type} (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (before state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion)
    (pending : List PendingCarrierFrame) (scope scopeInst fuel : Nat) (action : EvalM α)
    (source : AcceptedFrame config accepted frame before types)
    (absent : ∀ descriptor ∈ frame.interpretation.environment.vars.toList, descriptor.scope ≠ scope)
    (safe : RegisterBreakActionOutcome config accepted (unusedChildScopeFrame frame scope scopeInst fuel)
      ambient types live regions pending (action state)) :
    RegisterBreakActionOutcome config accepted frame ambient types live regions pending
      (withScope frame.interpretation.environment scope scopeInst action state) := by
  cases actual : action state with
  | escape address carriers after | jump target kind after =>
    simp [actual, RegisterBreakActionOutcome] at safe
  | stop reason after =>
    simp only [actual, RegisterBreakActionOutcome, Goose.Proofs.Exit.stepState] at safe
    have afterSource := source.leaveScope_withoutDeclarations scope scopeInst fuel absent safe.2.1
    simpa [withScope, actual, unusedChildScopeFrame, RegisterBreakActionOutcome, Goose.Proofs.Exit.stepState] using
      And.intro safe.1 (And.intro afterSource True.intro)
  | ok value after =>
    simp only [actual, RegisterBreakActionOutcome, Goose.Proofs.Exit.stepState] at safe
    have afterSource := source.leaveScope_withoutDeclarations scope scopeInst fuel absent safe.2.1
    have finalSource := afterSource.releaseScope_withoutDeclarations frame.interpretation.environment scope scopeInst absent
    have finalWorld := safe.1.releaseScope_withoutDeclarations config frame.initialized after ambient types live regions pending
      frame.interpretation.environment scope scopeInst absent
    simpa [withScope, releaseScope, EvalM.get, EvalM.set, bind, pure, actual, RegisterBreakActionOutcome,
      Goose.Proofs.Exit.stepState] using And.intro finalWorld (And.intro finalSource True.intro)

#print axioms withUnusedScope_outcome
end Goose.Proofs.ConstructionAcceptedExecution
