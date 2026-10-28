import Goose.Proofs.ConstructionAcceptedGlobalExpressionSequence
import Goose.Proofs.ConstructionAcceptedConditionalAlignment

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation

theorem globalBranch_blockChecks (fuel : Nat) (environment : TypingEnv) (source : PEnv) (scope : Nat)
    (statements : List Stmt) (tail : Expr) (typingBefore typingAfter : Nat) (types : List Ty)
    (rootBefore rootAfter : RState) (result : List RootRef × (Nat × Nat))
    (typed : typeBlock (fuel + 1) environment ⟨scope, statements, some tail⟩ typingBefore = .ok (types, typingAfter))
    (rooted : rpBlockValue source [] ⟨scope, statements, some tail⟩ rootBefore = .ok (result, rootAfter)) :
    ∃ next typingMiddle rootsMiddle roots,
      typeStatements fuel { environment with scope := scope } statements typingBefore = .ok (next, typingMiddle) ∧
      typeExpr fuel next tail typingMiddle = .ok (types, typingAfter) ∧
      rpStmts { source with scopes := scope :: source.scopes } statements rootBefore = .ok ((), rootsMiddle) ∧
      rpExpr { source with scopes := scope :: source.scopes } tail rootsMiddle = .ok (roots, rootAfter) := by
  simp only [typeBlock, bind, StateT.bind] at typed
  obtain ⟨_, rootsMiddle, roots, statementsRooted, tailRooted, _⟩ := rpBlockValue_body rooted
  simp only [List.length_nil, Nat.add_zero] at statementsRooted
  cases statementsTyped : typeStatements fuel { environment with scope := scope } statements typingBefore with
  | error failure => rw [statementsTyped] at typed; cases typed
  | ok result =>
    obtain ⟨next, typingMiddle⟩ := result
    rw [statementsTyped] at typed
    change typeExpr fuel next tail typingMiddle = .ok (types, typingAfter) at typed
    exact ⟨next, typingMiddle, rootsMiddle, roots, rfl, typed, statementsRooted, tailRooted⟩

#print axioms globalBranch_blockChecks

theorem accepted_globalBranch_statements_tail (config : EvalConfig) (accepted : AcceptedModule config)
    (id act scope scopeInst : Nat) (names : Array (List RootRef)) (cursor : RState)
    (statements : List Stmt) (tail : Expr) (form : ScalarExpressionStatements statements) (tailForm : AcceptedBinaryExpression tail)
    (state : ExecutionState) (types : RootTypes)
    (next : TypingEnv) (typingMiddle typingAfter : Nat) (rootsMiddle rootsAfter : RState) (roots : List RootRef)
    (source : AcceptedFrame config accepted (scalarGlobalBranchFrame config id act names scope scopeInst cursor) state types)
    (bounded : GlobalEffectTargetsBounded cursor.eff id)
    (statementsTyped : typeStatements 4094 (scalarGlobalBranchFrame config id act names scope scopeInst cursor).typing
      statements 0 = .ok (next, typingMiddle))
    (tailTyped : typeExpr 4094 next tail typingMiddle = .ok ([typesTy], typingAfter))
    (statementsRooted : rpStmts (scalarGlobalBranchFrame config id act names scope scopeInst cursor).source
      statements cursor = .ok ((), rootsMiddle))
    (tailRooted : rpExpr (scalarGlobalBranchFrame config id act names scope scopeInst cursor).source tail rootsMiddle = .ok (roots, rootsAfter)) :
    let frame := scalarGlobalBranchFrame config id act names scope scopeInst cursor
    let tailFrame := { frame with
    typing := next
    typingCounter := typingMiddle
    rootCursor := rootsMiddle }
    CheckedScalarStatements frame statements ∧ AcceptedFrame config accepted tailFrame state types ∧
      CheckedValue tailFrame tail typesTy roots typingAfter rootsAfter := by
  let frame := scalarGlobalBranchFrame config id act names scope scopeInst cursor
  have limit : frame.typing.globalLimit ≤ id := by simp [frame, scalarGlobalBranchFrame, scalarGlobalInitializerFrame]
  have ⟨same, middleBound⟩ := scalarExpressionStatements_effects_bounded form 4094 frame.typing next frame.source id
    0 typingMiddle cursor rootsMiddle limit bounded statementsTyped statementsRooted
  have tailBound := recursiveScalar_effects_bounded tailForm 4094 next frame.source id typingMiddle typingAfter rootsMiddle
    rootsAfter [typesTy] roots (by simpa [same] using limit) middleBound tailTyped tailRooted
  have middleAvailable : GlobalEffectsAvailable frame.interpretation id rootsMiddle.eff := by
    intro target member global instantiates
    cases target with
    | global other =>
      change global = other at instantiates
      subst global
      exact middleBound other member
    | param parameter => exact instantiates.1.elim
  have statementsChecked := scalarExpressionStatements_checked form frame next typingMiddle rootsMiddle statementsTyped statementsRooted middleAvailable
  have finalFrame := checkedScalarStatements_finalFrame statementsChecked config accepted state types next typingMiddle rootsMiddle
    source statementsTyped statementsRooted
  let tailFrame := { frame with
    typing := next
    typingCounter := typingMiddle
    rootCursor := rootsMiddle }
  have tailSource : AcceptedFrame config accepted tailFrame state types := finalFrame.withTypingFuel 4094
  have tailAvailable : GlobalEffectsAvailable tailFrame.interpretation id rootsAfter.eff := by
    intro target member global instantiates
    cases target with
    | global other =>
      change global = other at instantiates
      subst global
      exact tailBound other member
    | param parameter => exact instantiates.1.elim
  exact ⟨statementsChecked, tailSource, ⟨tailTyped, tailRooted, tailAvailable⟩⟩

theorem execBlock_checked_globalStatements (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (id act scope : Nat) (names : Array (List RootRef)) (cursor : RState) (statements : List Stmt) (tail : Expr)
    (form : ScalarExpressionStatements statements) (tailForm : AcceptedBinaryExpression tail)
    (next : TypingEnv) (typingMiddle typingAfter : Nat) (rootsMiddle rootsAfter : RState) (roots : List RootRef) (ty : Ty)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (world : AcceptedWorld config id before ambient types live [] []) (clear : FutureGlobalsClear config id before)
    (source : AcceptedFrame config accepted (scalarGlobalBranchFrame config id act names scope before.nextScope cursor)
      { before with nextScope := before.nextScope + 1 } types)
    (bounded : GlobalEffectTargetsBounded cursor.eff id)
    (statementsTyped : typeStatements 4094 (scalarGlobalBranchFrame config id act names scope before.nextScope cursor).typing
      statements 0 = .ok (next, typingMiddle))
    (tailTyped : typeExpr 4094 next tail typingMiddle = .ok ([ty], typingAfter))
    (statementsRooted : rpStmts (scalarGlobalBranchFrame config id act names scope before.nextScope cursor).source
      statements cursor = .ok ((), rootsMiddle))
    (tailRooted : rpExpr (scalarGlobalBranchFrame config id act names scope before.nextScope cursor).source tail rootsMiddle = .ok (roots, rootsAfter)) :
    ∃ nextLive,
      let outcome := execBlock fuel config ⟨0, act, #[], [], []⟩ [] [] ⟨scope, statements, some tail⟩ before
      let after := Goose.Proofs.Exit.stepState outcome
      AcceptedWorld config id after ambient types nextLive [] [] ∧ FutureGlobalsClear config id after ∧
      (match outcome with | .ok (.normal value) _ => ValueRepresentation ty value ∧ PointerTypedValue types ty value | .stop .. => True | _ => False) := by
  let environment : RuntimeActivation := ⟨0, act, #[], [], []⟩
  let entered := { before with nextScope := before.nextScope + 1 }
  let frame := scalarGlobalBranchFrame config id act names scope before.nextScope cursor
  let tailFrame := { frame with
    typing := next
    typingCounter := typingMiddle
    rootCursor := rootsMiddle }
  have enteredWorld := (freshScope_acceptedWorld config id before ambient types live world).2
  have enteredClear : FutureGlobalsClear config id entered := clear
  obtain ⟨statementsChecked, tailSource, tailChecked⟩ := accepted_globalBranch_statements_tail config accepted
    id act scope before.nextScope names cursor statements tail form tailForm entered types next typingMiddle typingAfter
    rootsMiddle rootsAfter roots source bounded statementsTyped tailTyped statementsRooted tailRooted
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
    have statementsRun := execStmts_checkedScalar_initializer statementsChecked fuel config accepted entered ambient types live [] [] enteredWorld source
    change Goose.Proofs.Exit.stepState (execStmts fuel config branchEnv statements entered) = entered ∧ _ at statementsRun
    cases statementsExecution : execStmts fuel config branchEnv statements entered with
    | escape address carriers after =>
      exact ((execStmts_scalar_controlFree form fuel config branchEnv).1 entered address carriers after statementsExecution).elim
    | jump target kind after =>
      exact ((execStmts_scalar_controlFree form fuel config branchEnv).2 entered target kind after statementsExecution).elim
    | stop reason after =>
      have same : after = entered := by simpa [statementsExecution, Goose.Proofs.Exit.stepState] using statementsRun.1
      subst after
      change execStmts fuel config ⟨0, act, #[], [(scope, before.nextScope)], []⟩ statements entered = .stop reason entered at statementsExecution
      have stopped : execBlock (fuel + 1) config environment [] [] ⟨scope, statements, some tail⟩ before = .stop reason entered := by
        simp [execBlock, freshScope, EvalM.get, EvalM.set, bind, pure, withScope, bindAll, statementsExecution, environment, entered]
      simp only [stopped, Goose.Proofs.Exit.stepState]
      exact ⟨live, enteredWorld, enteredClear, trivial⟩
    | ok flow after =>
      obtain ⟨sameFlow, sameState⟩ := statementsRun.2.1 flow after statementsExecution
      subst flow after
      have tailRun := evalValue_checked_binary_recursive tailForm fuel config accepted tailFrame entered ambient types live [] []
        enteredWorld tailSource ty roots typingAfter rootsAfter tailChecked
      change Goose.Proofs.Exit.stepState (evalValue fuel config branchEnv tail entered) = entered ∧ _ at tailRun
      cases tailExecution : evalValue fuel config branchEnv tail entered with
      | escape address carriers after =>
        exact ((evalValue_scalar_controlFree tailForm fuel config branchEnv).1 entered address carriers after tailExecution).elim
      | jump target kind after =>
        exact ((evalValue_scalar_controlFree tailForm fuel config branchEnv).2 entered target kind after tailExecution).elim
      | stop reason after =>
        have same : after = entered := by simpa [tailExecution, Goose.Proofs.Exit.stepState] using tailRun.1
        subst after
        change execStmts fuel config ⟨0, act, #[], [(scope, before.nextScope)], []⟩ statements entered = .ok (.normal .unit) entered at statementsExecution
        change evalValue fuel config ⟨0, act, #[], [(scope, before.nextScope)], []⟩ tail entered = .stop reason entered at tailExecution
        have stopped : execBlock (fuel + 1) config environment [] [] ⟨scope, statements, some tail⟩ before = .stop reason entered := by
          simp [execBlock, freshScope, EvalM.get, EvalM.set, bind, pure, withScope, bindAll, statementsExecution, tailExecution, environment, entered]
        simp only [stopped, Goose.Proofs.Exit.stepState]
        exact ⟨live, enteredWorld, enteredClear, trivial⟩
      | ok value after =>
        have same : after = entered := by simpa [tailExecution, Goose.Proofs.Exit.stepState] using tailRun.1
        subst after
        have valid := tailRun.2.1 value entered tailExecution
        let released := releaseScopeState environment scope before.nextScope entered
        have releasedWorld := enteredWorld.releaseScope config id entered ambient types live [] [] environment scope before.nextScope
        have releasedClear : FutureGlobalsClear config id released := by
          intro global future within
          simpa [released, releaseScopeState, environment] using clear global future within
        change execStmts fuel config ⟨0, act, #[], [(scope, before.nextScope)], []⟩ statements entered = .ok (.normal .unit) entered at statementsExecution
        change evalValue fuel config ⟨0, act, #[], [(scope, before.nextScope)], []⟩ tail entered = .ok value entered at tailExecution
        have done : execBlock (fuel + 1) config environment [] [] ⟨scope, statements, some tail⟩ before = .ok (.normal value) released := by
          simp [execBlock, freshScope, EvalM.get, EvalM.set, bind, pure, withScope, bindAll, statementsExecution, tailExecution,
            releaseScope, released, environment, entered]
        simp only [done, Goose.Proofs.Exit.stepState]
        exact ⟨_, releasedWorld, releasedClear, valid.represented, valid.pointers⟩

#print axioms execBlock_checked_globalStatements
#print axioms accepted_globalBranch_statements_tail
end Goose.Proofs.ConstructionAcceptedExecution
