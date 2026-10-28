import Goose.Proofs.ConstructionAcceptedUnusedScopeOutcome

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence

theorem execResultBlock_integerTail_world (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion)
    (pending : List PendingCarrierFrame) (scope sourceFuel : Nat) (statements : List Stmt)
    (intTy : Goose.Core.IntTy) (literal : Int)
    (source : AcceptedFrame config accepted frame state types)
    (absent : ∀ descriptor ∈ frame.interpretation.environment.vars.toList, descriptor.scope ≠ scope)
    (statementsSafe :
      let scopeState := ownershipResultScopeState frame.interpretation.environment scope state
      let child := unusedChildScopeFrame frame scope state.nextScope sourceFuel
      let step := execStmts fuel config child.interpretation.environment statements scopeState
      RegisterBreakActionOutcome config accepted child ambient types live regions pending step ∧
        match step with | .ok flow _ => flow = .normal .unit | _ => True) :
    RegisterBreakActionOutcome config accepted frame ambient types live regions pending
      (execResultBlock (fuel + 2) config frame.interpretation.environment [.register (.int intTy)]
        ⟨scope, statements, some (.lit intTy literal)⟩ state) := by
  let environment := frame.interpretation.environment
  let scopeState := ownershipResultScopeState environment scope state
  let child := unusedChildScopeFrame frame scope state.nextScope sourceFuel
  let action : EvalM (Flow × List Carrier) := do
    bindAll environment.act state.nextScope []
    let flow ← execStmts fuel config child.interpretation.environment statements
    match flow, some (.lit intTy literal) with
    | .normal _, some expression => pure (.normal .unit, ← evalProduce fuel config child.interpretation.environment [.register (.int intTy)] expression)
    | .normal _, none => fault .arity
    | flow, _ => pure (flow, [])
  have safeAction : RegisterBreakActionOutcome config accepted child ambient types live regions pending (action scopeState) := by
    change RegisterBreakActionOutcome config accepted child ambient types live regions pending
      (execStmts fuel config child.interpretation.environment statements scopeState) ∧
      (match execStmts fuel config child.interpretation.environment statements scopeState with
       | .ok flow _ => flow = .normal .unit | _ => True) at statementsSafe
    cases statement : execStmts fuel config child.interpretation.environment statements scopeState with
    | stop reason after =>
      simpa [action, bindAll, bind, pure, statement, RegisterBreakActionOutcome, Goose.Proofs.Exit.stepState] using statementsSafe.1
    | escape address carriers after | jump target kind after =>
      simp [statement, RegisterBreakActionOutcome] at statementsSafe
    | ok flow after =>
      simp only [statement] at statementsSafe
      have same := statementsSafe.2
      subst flow
      cases fuel with
      | zero =>
        simpa [action, bindAll, bind, pure, evalProduce, timeout, EvalM.stop, statement,
          RegisterBreakActionOutcome, Goose.Proofs.Exit.stepState] using statementsSafe.1
      | succ fuel =>
        cases fuel <;> simpa [action, bindAll, bind, pure, evalProduce, evalValue, selectCompletionChannel, timeout, EvalM.stop, statement,
          RegisterBreakActionOutcome, Goose.Proofs.Exit.stepState] using statementsSafe.1
  have scopeSafe := withUnusedScope_outcome config accepted frame state scopeState ambient types live regions pending
    scope state.nextScope sourceFuel action source absent safeAction
  have sameStep : execResultBlock (fuel + 2) config frame.interpretation.environment [.register (.int intTy)]
      ⟨scope, statements, some (.lit intTy literal)⟩ state =
      withScope frame.interpretation.environment scope state.nextScope action scopeState := by
    simp only [execResultBlock, execResultBlockWith, execResultScope, freshScope, EvalM.get, EvalM.set, bind, pure,
      scopeState, ownershipResultScopeState, environment, child, unusedChildScopeFrame, RootInterpretation.enterScope]
    unfold withScope
    simp only [action, bindAll, List.forIn_nil, bind, pure, environment, child, unusedChildScopeFrame,
      RootInterpretation.enterScope]
    cases step : execStmts fuel config
      { frame.interpretation.environment with scopes := (scope, state.nextScope) :: frame.interpretation.environment.scopes }
      statements (ownershipResultScopeState frame.interpretation.environment scope state) <;>
      simp only [ownershipResultScopeState, beq_iff_eq] at step <;> simp [step, bind, pure]
    case ok flow after => cases flow <;> simp [bind, pure]
  rw [sameStep]
  exact scopeSafe

#print axioms execResultBlock_integerTail_world
end Goose.Proofs.ConstructionAcceptedExecution
