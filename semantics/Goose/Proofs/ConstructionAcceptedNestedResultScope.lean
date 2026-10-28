import Goose.Proofs.ConstructionAcceptedUnusedScopeOutcome

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence

theorem execResultBlock_emptyTail_world (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (scope sourceFuel : Nat) (expression : Expr) (intTy : Goose.Core.IntTy) (literal : Int)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types)
    (fresh : ∀ entry ∈ frame.interpretation.environment.scopes, entry.1 ≠ scope)
    (absent : ∀ descriptor ∈ frame.interpretation.environment.vars.toList, descriptor.scope ≠ scope)
    (tailSafe : let scopeState := ownershipResultScopeState frame.interpretation.environment scope state
      let child := unusedChildScopeFrame frame scope state.nextScope sourceFuel
      let step := evalProduce fuel config child.interpretation.environment [.register (.int intTy)] expression scopeState
      RegisterBreakActionOutcome config accepted child ambient types live regions pending step ∧
        match step with | .ok carriers _ => carriers = [.register (.int intTy literal)] | _ => True) :
    let step := execResultBlock (fuel + 2) config frame.interpretation.environment [.register (.int intTy)]
      ⟨scope, [], some expression⟩ state
    RegisterBreakActionOutcome config accepted frame ambient types live regions pending step ∧
      match step with | .ok result _ => result = (.normal .unit, [.register (.int intTy literal)]) | _ => True := by
  let environment := frame.interpretation.environment
  let scopeState := ownershipResultScopeState environment scope state
  let child := unusedChildScopeFrame frame scope state.nextScope sourceFuel
  change RegisterBreakActionOutcome config accepted child ambient types live regions pending
    (evalProduce fuel config child.interpretation.environment [.register (.int intTy)] expression scopeState) ∧
    (match evalProduce fuel config child.interpretation.environment [.register (.int intTy)] expression scopeState with
      | .ok carriers _ => carriers = [.register (.int intTy literal)] | _ => True) at tailSafe
  have childWorld : AcceptedWorld config child.initialized scopeState ambient types live regions pending :=
    acceptedWorld_resultScope config frame.initialized state ambient types live regions pending environment scope world
  have childSource : AcceptedFrame config accepted child scopeState types := by
    have entered := source.enterScope_withoutDeclarations scope sourceFuel fresh absent
    have actual := entered.withActivations (({ state with nextScope := state.nextScope + 1 }).activations.map fun (current : RuntimeActivation) =>
      if current.act == frame.interpretation.environment.act then
        { current with scopes := (scope, state.nextScope) :: frame.interpretation.environment.scopes } else current)
    simpa [scopeState, ownershipResultScopeState, child] using actual
  let action : EvalM (Flow × List Carrier) := do
    bindAll environment.act state.nextScope []
    let flow ← execStmts fuel config child.interpretation.environment []
    match flow, some expression with
    | .normal _, some value => pure (.normal .unit, ← evalProduce fuel config child.interpretation.environment [.register (.int intTy)] value)
    | .normal _, none => fault .arity
    | flow, _ => pure (flow, [])
  have safeAction : RegisterBreakActionOutcome config accepted child ambient types live regions pending (action scopeState) := by
    cases fuel with
    | zero => simpa [action, bindAll, bind, pure, execStmts, timeout, EvalM.stop, RegisterBreakActionOutcome, Goose.Proofs.Exit.stepState] using And.intro childWorld (And.intro childSource True.intro)
    | succ fuel =>
      cases produced : evalProduce (fuel + 1) config child.interpretation.environment [.register (.int intTy)] expression scopeState with
      | escape address carriers after | jump target kind after => simp [produced, RegisterBreakActionOutcome] at tailSafe
      | stop reason after => simpa [action, bindAll, bind, pure, execStmts, produced, RegisterBreakActionOutcome, Goose.Proofs.Exit.stepState] using tailSafe.1
      | ok carriers after => simpa [action, bindAll, bind, pure, execStmts, produced, RegisterBreakActionOutcome, Goose.Proofs.Exit.stepState] using tailSafe.1
  have scopeSafe := withUnusedScope_outcome config accepted frame state scopeState ambient types live regions pending
    scope state.nextScope sourceFuel action source absent safeAction
  have sameStep : execResultBlock (fuel + 2) config environment [.register (.int intTy)] ⟨scope, [], some expression⟩ state =
      withScope environment scope state.nextScope action scopeState := by
    simp only [execResultBlock, execResultBlockWith, execResultScope, freshScope, EvalM.get, EvalM.set, bind, pure,
      scopeState, ownershipResultScopeState, environment, child, unusedChildScopeFrame, RootInterpretation.enterScope]
    unfold withScope
    simp only [action, bindAll, List.forIn_nil, bind, pure, environment, child, unusedChildScopeFrame, RootInterpretation.enterScope]
    cases step : execStmts fuel config
      { frame.interpretation.environment with scopes := (scope, state.nextScope) :: frame.interpretation.environment.scopes }
      [] (ownershipResultScopeState frame.interpretation.environment scope state) <;>
      simp only [ownershipResultScopeState, beq_iff_eq] at step <;> simp [step, bind, pure]
    case ok flow after => cases flow <;> simp [bind, pure]
  have shape : ∀ result after, withScope environment scope state.nextScope action scopeState = .ok result after →
      result = (.normal .unit, [.register (.int intTy literal)]) := by
    intro result after executed
    cases fuel with
    | zero => simp [withScope, action, bindAll, bind, pure, execStmts, timeout, EvalM.stop] at executed
    | succ fuel =>
      cases produced : evalProduce (fuel + 1) config child.interpretation.environment [.register (.int intTy)] expression scopeState with
      | stop reason middle =>
        simp [withScope, action, bindAll, bind, pure, execStmts, produced] at executed
      | escape address carriers middle | jump target kind middle =>
        simp [produced, RegisterBreakActionOutcome] at tailSafe
      | ok carriers middle =>
        have carriersEq : carriers = [.register (.int intTy literal)] := by simpa [produced] using tailSafe.2
        subst carriers
        simp [withScope, action, bindAll, bind, pure, execStmts, produced] at executed
        cases released : releaseScope environment scope state.nextScope middle <;> simp [released] at executed
        case ok unit final => cases unit; exact executed.1.symm

  rw [sameStep]
  have safe : RegisterBreakActionOutcome config accepted frame ambient types live regions pending
      (withScope environment scope state.nextScope action scopeState) := by simpa [environment] using scopeSafe
  cases executed : withScope environment scope state.nextScope action scopeState with
  | stop reason after => simpa [executed] using And.intro safe True.intro
  | escape address carriers after | jump target kind after => simp [executed, RegisterBreakActionOutcome] at safe
  | ok result after => exact ⟨by simpa [executed] using safe, shape result after executed⟩

#print axioms execResultBlock_emptyTail_world
end Goose.Proofs.ConstructionAcceptedExecution
