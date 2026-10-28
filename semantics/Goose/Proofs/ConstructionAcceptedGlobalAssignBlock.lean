import Goose.Proofs.ConstructionAcceptedGlobalAssignSequence
import Goose.Proofs.ConstructionAcceptedGlobalBranchSequence

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst)
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem execBlock_checked_globalAssignments (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (id act scope : Nat) (names : Array (List RootRef)) (cursor : RState) (statements : List Stmt) (tail : Expr)
    (form : GlobalScalarStatements statements) (tailForm : AcceptedBinaryExpression tail)
    (next : TypingEnv) (typingMiddle typingAfter : Nat) (rootsMiddle rootsAfter : RState) (roots : List RootRef) (ty : Ty)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (world : AcceptedWorld config id before ambient types live [] []) (clear : FutureGlobalsClear config id before)
    (source : AcceptedFrame config accepted (scalarGlobalBranchFrame config id act names scope before.nextScope cursor)
      { before with nextScope := before.nextScope + 1 } types)
    (bounded : GlobalEffectTargetsBounded cursor.eff id)
    (statementsTyped : typeStatements 4094 (scalarGlobalBranchFrame config id act names scope before.nextScope cursor).typing
      statements 0 = .ok (next, typingMiddle))
    (tailTyped : typeExpr 4094 next tail typingMiddle = .ok ([ty], typingAfter))
    (statementsRooted : rpStmts (scalarGlobalBranchFrame config id act names scope before.nextScope cursor).source
      statements cursor = .ok ((), rootsMiddle))
    (tailRooted : rpExpr (scalarGlobalBranchFrame config id act names scope before.nextScope cursor).source tail rootsMiddle = .ok (roots, rootsAfter))
    (scalar : ∀ global expression origin, .assign (.global global) expression origin ∈ statements →
      ∀ descriptor, config.module.globals[global]? = some descriptor → (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool) :
    ∃ nextLive,
      let outcome := execBlock fuel config ⟨0, act, #[], [], []⟩ [] [] ⟨scope, statements, some tail⟩ before
      let after := Goose.Proofs.Exit.stepState outcome
      AcceptedWorld config id after ambient types nextLive [] [] ∧ FutureGlobalsClear config id after ∧
      (match outcome with | .ok (.normal value) _ => ValueRepresentation ty value ∧ PointerTypedValue types ty value | .stop .. => True | _ => False) := by
  let environment : RuntimeActivation := ⟨0, act, #[], [], []⟩
  let entered := { before with nextScope := before.nextScope + 1 }
  let frame := scalarGlobalBranchFrame config id act names scope before.nextScope cursor
  have enteredWorld := (freshScope_acceptedWorld config id before ambient types live world).2
  have enteredClear : FutureGlobalsClear config id entered := clear
  have limit : frame.typing.globalLimit ≤ frame.initialized := by simp [frame, scalarGlobalBranchFrame, scalarGlobalInitializerFrame]
  have noParameters : ∀ parameter global, ¬ frame.interpretation.parameters parameter (.global global) := by
    simp [frame, scalarGlobalBranchFrame, scalarGlobalInitializerFrame, EntryInterpretation, RootInterpretation.enterScope]
  have ⟨sameNext, sameCounter, sameCursor, middleBound⟩ := globalScalarStatements_checker_advance form config accepted frame entered types
    next typingMiddle rootsMiddle source limit noParameters bounded statementsTyped statementsRooted
  have tailBound := recursiveScalar_effects_bounded tailForm 4094 next frame.source id typingMiddle typingAfter rootsMiddle rootsAfter
    [ty] roots (by simp [sameNext, frame, scalarGlobalBranchFrame, scalarGlobalInitializerFrame]) middleBound tailTyped tailRooted
  change ∃ nextLive, let outcome := execBlock fuel config environment [] [] ⟨scope, statements, some tail⟩ before
    let after := Goose.Proofs.Exit.stepState outcome
    AcceptedWorld config id after ambient types nextLive [] [] ∧ FutureGlobalsClear config id after ∧
      (match outcome with | .ok (.normal value) _ => ValueRepresentation ty value ∧ PointerTypedValue types ty value | .stop .. => True | _ => False)
  cases fuel with
  | zero =>
    simp only [execBlock, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
    exact ⟨live, world, clear, trivial⟩
  | succ fuel =>
    let branchEnv := frame.interpretation.environment
    obtain ⟨finalFrame, initEq, interpretationEq, sourceEq, statementsWorld, statementsSource, statementsFlow⟩ :=
      execStmts_globalScalar_prefix form fuel config accepted frame entered ambient types live [] [] next typingMiddle rootsMiddle
        enteredWorld source limit noParameters bounded statementsTyped statementsRooted scalar
    change AcceptedWorld config id (Goose.Proofs.Exit.stepState (execStmts fuel config branchEnv statements entered))
      ambient types live [] [] at statementsWorld
    change AcceptedFrame config accepted finalFrame (Goose.Proofs.Exit.stepState (execStmts fuel config branchEnv statements entered)) types at statementsSource
    change (match execStmts fuel config branchEnv statements entered with
      | .ok flow _ => flow = .normal .unit ∧ finalFrame.typing = next ∧ finalFrame.typingCounter = typingMiddle ∧ finalFrame.rootCursor = rootsMiddle
      | .stop .. => True | _ => False) at statementsFlow
    cases statementsExecution : execStmts fuel config branchEnv statements entered with
    | escape address carriers after | jump target kind after => simp only [statementsExecution] at statementsFlow
    | stop reason after =>
      simp only [statementsExecution, Goose.Proofs.Exit.stepState] at statementsWorld statementsSource
      have afterClear : FutureGlobalsClear config id after := by
        intro global future inside
        exact statementsSource.futureGlobals global (by simpa [initEq, frame, scalarGlobalBranchFrame, scalarGlobalInitializerFrame] using future) inside
      change execStmts fuel config ⟨0, act, #[], [(scope, before.nextScope)], []⟩ statements entered = .stop reason after at statementsExecution
      have stopped : execBlock (fuel + 1) config environment [] [] ⟨scope, statements, some tail⟩ before = .stop reason after := by
        simp [execBlock, freshScope, EvalM.get, EvalM.set, bind, pure, withScope, bindAll, statementsExecution, environment, entered]
      simp only [stopped, Goose.Proofs.Exit.stepState]
      exact ⟨live, statementsWorld, afterClear, trivial⟩
    | ok flow middle =>
      simp only [statementsExecution, Goose.Proofs.Exit.stepState] at statementsWorld statementsSource statementsFlow
      obtain ⟨flowEq, typingEq, counterEq, cursorEq⟩ := statementsFlow
      subst flow
      let tailFrame := { finalFrame with typingFuel := 4094 }
      have tailSource : AcceptedFrame config accepted tailFrame middle types := statementsSource.withTypingFuel 4094
      have tailAvailable : GlobalEffectsAvailable tailFrame.interpretation tailFrame.initialized rootsAfter.eff := by
        intro target member global instantiates
        cases target with
        | global other =>
          change global = other at instantiates
          subst global
          simpa [tailFrame, initEq, frame, scalarGlobalBranchFrame, scalarGlobalInitializerFrame] using tailBound other member
        | param parameter =>
          have impossible := noParameters parameter global
          exact (impossible (by simpa [tailFrame, interpretationEq] using instantiates.1)).elim
      have tailChecked : CheckedValue tailFrame tail ty roots typingAfter rootsAfter := by
        refine ⟨?_, ?_, tailAvailable⟩
        · simpa [tailFrame, typingEq, counterEq] using tailTyped
        · simpa [tailFrame, sourceEq, cursorEq, StateT.run] using tailRooted
      have tailRun := evalValue_checked_binary_recursive tailForm fuel config accepted tailFrame middle ambient types live [] []
        (by simpa [tailFrame, initEq, frame, scalarGlobalBranchFrame, scalarGlobalInitializerFrame] using statementsWorld) tailSource ty roots typingAfter rootsAfter tailChecked
      have middleClear : FutureGlobalsClear config id middle := by
        intro global future inside
        exact statementsSource.futureGlobals global (by simpa [initEq, frame, scalarGlobalBranchFrame, scalarGlobalInitializerFrame] using future) inside
      simp only [tailFrame, interpretationEq] at tailRun
      change Goose.Proofs.Exit.stepState (evalValue fuel config branchEnv tail middle) = middle ∧ _ at tailRun
      cases tailExecution : evalValue fuel config branchEnv tail middle with
      | escape address carriers after =>
        exact ((evalValue_scalar_controlFree tailForm fuel config branchEnv).1 middle address carriers after tailExecution).elim
      | jump target kind after =>
        exact ((evalValue_scalar_controlFree tailForm fuel config branchEnv).2 middle target kind after tailExecution).elim
      | stop reason after =>
        have same : after = middle := by simpa [tailExecution, Goose.Proofs.Exit.stepState] using tailRun.1
        subst after
        change execStmts fuel config ⟨0, act, #[], [(scope, before.nextScope)], []⟩ statements entered = .ok (.normal .unit) middle at statementsExecution
        change evalValue fuel config ⟨0, act, #[], [(scope, before.nextScope)], []⟩ tail middle = .stop reason middle at tailExecution
        have stopped : execBlock (fuel + 1) config environment [] [] ⟨scope, statements, some tail⟩ before = .stop reason middle := by
          simp [execBlock, freshScope, EvalM.get, EvalM.set, bind, pure, withScope, bindAll, statementsExecution, tailExecution, environment, entered]
        simp only [stopped, Goose.Proofs.Exit.stepState]
        exact ⟨live, statementsWorld, middleClear, trivial⟩
      | ok value after =>
        have same : after = middle := by simpa [tailExecution, Goose.Proofs.Exit.stepState] using tailRun.1
        subst after
        have valid := tailRun.2.1 value middle (by simpa [tailFrame, interpretationEq] using tailExecution)
        let released := releaseScopeState environment scope before.nextScope middle
        have releasedWorld := statementsWorld.releaseScope config id middle ambient types live [] [] environment scope before.nextScope
        have releasedClear : FutureGlobalsClear config id released := by
          intro global future inside
          simpa [released, releaseScopeState, environment] using middleClear global future inside
        change execStmts fuel config ⟨0, act, #[], [(scope, before.nextScope)], []⟩ statements entered = .ok (.normal .unit) middle at statementsExecution
        change evalValue fuel config ⟨0, act, #[], [(scope, before.nextScope)], []⟩ tail middle = .ok value middle at tailExecution
        have done : execBlock (fuel + 1) config environment [] [] ⟨scope, statements, some tail⟩ before = .ok (.normal value) released := by
          simp [execBlock, freshScope, EvalM.get, EvalM.set, bind, pure, withScope, bindAll, statementsExecution, tailExecution,
            releaseScope, released, environment, entered]
        simp only [done, Goose.Proofs.Exit.stepState]
        exact ⟨_, releasedWorld, releasedClear, valid.represented, valid.pointers⟩

#print axioms execBlock_checked_globalAssignments
end Goose.Proofs.ConstructionAcceptedExecution
