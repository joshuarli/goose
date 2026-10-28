import Goose.Proofs.ConstructionAcceptedRegisterBreak

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

def RegisterBreakActionOutcome (config : EvalConfig) (accepted : AcceptedModule config) (frame : ConstructionSourceFrame)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (step : ExecutionStep α) : Prop :=
  AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState step) ambient types live regions pending ∧
  AcceptedFrame config accepted frame (Goose.Proofs.Exit.stepState step) types ∧
  match step with
  | .ok .. | .stop .. => True
  | _ => False

theorem withRegisterBreak_outcome {α : Type} (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion)
    (pending : List PendingCarrierFrame) (act : Nat) (scope : BreakScope) (ty : Ty)
    (action : EvalM α) (receive : JumpKind → EvalM α)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (safe : let target : BreakTarget := ⟨state.nextScope, act, scope, [.register ty]⟩
      let pushed := { state with nextScope := state.nextScope + 1, breaks := target :: state.breaks }
      RegisterBreakActionOutcome config accepted frame (.breakTarget target [] :: ambient) types live regions pending (action pushed)) :
    RegisterBreakActionOutcome config accepted frame ambient types live regions pending
      (withBreakTarget act scope [.register ty] action receive state) := by
  let target : BreakTarget := ⟨state.nextScope, act, scope, [.register ty]⟩
  let pushed := { state with nextScope := state.nextScope + 1, breaks := target :: state.breaks }
  change RegisterBreakActionOutcome config accepted frame (.breakTarget target [] :: ambient) types live regions pending (action pushed) at safe
  have outer := world.freshBreakOutside config frame.initialized state ambient types live regions pending
  cases actual : action pushed with
  | escape address carriers after | jump id kind after =>
    simp [actual, RegisterBreakActionOutcome, Goose.Proofs.Exit.stepState, pushed, target] at safe
  | ok value after =>
    simp only [actual, RegisterBreakActionOutcome, Goose.Proofs.Exit.stepState] at safe
    have finalWorld := safe.1.finishEmptyBreak config frame.initialized after target ambient types live regions pending (by simpa [target] using outer)
    have finalSource := safe.2.1.withBreaks (after.breaks.filter (fun current => current.id != state.nextScope))
    simpa [RegisterBreakActionOutcome, withBreakTarget, target, pushed, actual, mapStepState, Goose.Proofs.Exit.stepState] using And.intro finalWorld (And.intro finalSource True.intro)
  | stop reason after =>
    simp only [actual, RegisterBreakActionOutcome, Goose.Proofs.Exit.stepState] at safe
    have finalWorld := safe.1.finishEmptyBreak config frame.initialized after target ambient types live regions pending (by simpa [target] using outer)
    have finalSource := safe.2.1.withBreaks (after.breaks.filter (fun current => current.id != state.nextScope))
    simpa [RegisterBreakActionOutcome, withBreakTarget, target, pushed, actual, mapStepState, Goose.Proofs.Exit.stepState] using And.intro finalWorld (And.intro finalSource True.intro)

#print axioms withRegisterBreak_outcome
end Goose.Proofs.ConstructionAcceptedExecution
