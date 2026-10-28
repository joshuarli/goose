import Goose.Proofs.ConstructionAcceptedConditionalScope
import Lean.Elab.Tactic

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

private def flowName (name : String) : Lean.Name :=
  Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Goose") "Construct") "Declarations") 0) "Goose") "Construct") name

macro "expressionFlowPrivate" : term => pure (Lean.mkIdent (flowName "expressionFlow"))
macro "nextFlowPrivate" : term => pure (Lean.mkIdent (Lean.Name.str (flowName "StatementFlow") "next"))

macro "continueFlowPrivate" : term => pure (Lean.mkIdent (flowName "continueFlow"))
macro "placeFlowPrivate" : term => pure (Lean.mkIdent (flowName "placeFlow"))
macro "blockFlowPrivate" : term => pure (Lean.mkIdent (flowName "blockFlow"))
macro "statementsFlowPrivate" : term => pure (Lean.mkIdent (flowName "statementsFlow"))

elab "unfold_typing_require" : tactic => do
  let name := Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Goose") "Construct") "Typing") 0) "Goose") "Construct") "require"
  let requireName := Lean.mkIdent name
  let checked := Lean.mkIdent `checked
  Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $requireName:ident at $checked:ident))

macro "flow_simp" : tactic => do
  let expression := Lean.mkIdent (flowName "expressionFlow")
  let place := Lean.mkIdent (flowName "placeFlow")
  let block := Lean.mkIdent (flowName "blockFlow")
  let statements := Lean.mkIdent (flowName "statementsFlow")
  let cont := Lean.mkIdent (flowName "continueFlow")
  `(tactic| simp [$expression:ident, $place:ident, $block:ident, $statements:ident, $cont:ident])

macro "flow_simp_all" : tactic => do
  let expression := Lean.mkIdent (flowName "expressionFlow")
  let place := Lean.mkIdent (flowName "placeFlow")
  let block := Lean.mkIdent (flowName "blockFlow")
  let statements := Lean.mkIdent (flowName "statementsFlow")
  let cont := Lean.mkIdent (flowName "continueFlow")
  `(tactic| simp_all [$expression:ident, $place:ident, $block:ident, $statements:ident, $cont:ident])

macro "flow_simpa" " using " t:term : tactic => do
  let expression := Lean.mkIdent (flowName "expressionFlow")
  let place := Lean.mkIdent (flowName "placeFlow")
  let block := Lean.mkIdent (flowName "blockFlow")
  let statements := Lean.mkIdent (flowName "statementsFlow")
  let cont := Lean.mkIdent (flowName "continueFlow")
  `(tactic| simpa [$expression:ident, $place:ident, $block:ident, $statements:ident, $cont:ident] using $t)

theorem scalarExpressionFlow_next {expression : Expr} (form : AcceptedScalarExpression expression) :
    ∀ fuel, nextFlowPrivate ∈ expressionFlowPrivate fuel expression := by
  cases form <;> intro fuel <;> cases fuel <;> flow_simp <;> (rename_i fuel; cases fuel <;> flow_simp)

theorem notExpressionFlow_next {expression : Expr} (form : AcceptedNotExpression expression) :
    ∀ fuel, nextFlowPrivate ∈ expressionFlowPrivate fuel expression := by
  induction form with
  | scalar form => exact scalarExpressionFlow_next form
  | not form ih =>
    intro fuel
    cases fuel with
    | zero => flow_simp
    | succ fuel => flow_simpa using ih fuel

theorem numericExpressionFlow_next {expression : Expr} (form : AcceptedNumericExpression expression) :
    ∀ fuel, nextFlowPrivate ∈ expressionFlowPrivate fuel expression := by
  induction form with
  | scalar form => exact notExpressionFlow_next form
  | unary operation origin form ih | conversion kind target origin form ih =>
    intro fuel
    cases fuel with
    | zero => flow_simp
    | succ fuel => flow_simpa using ih fuel

theorem recursiveScalarFlow_next {expression : Expr} (form : AcceptedBinaryExpression expression) :
    ∀ fuel, nextFlowPrivate ∈ expressionFlowPrivate fuel expression := by
  induction form with
  | numeric form => exact numericExpressionFlow_next form
  | binary operation origin left right leftIH rightIH | comparison operation left right leftIH rightIH =>
    intro fuel
    cases fuel with
    | zero => flow_simp
    | succ fuel =>
      flow_simp
      exact ⟨nextFlowPrivate, leftIH fuel, rightIH fuel⟩
  | @conjunction lhs rhs left right leftIH rightIH | @disjunction lhs rhs left right leftIH rightIH =>
    intro fuel
    cases fuel with
    | zero => flow_simp
    | succ fuel =>
      flow_simp
      refine ⟨nextFlowPrivate, leftIH fuel, ?_⟩
      cases lhs <;> flow_simp_all <;> (rename_i b; cases b <;> flow_simp_all)
  | not expression ih | unary operation origin expression ih | conversion kind target origin expression ih =>
    intro fuel
    cases fuel with
    | zero => flow_simp
    | succ fuel => flow_simpa using ih fuel

theorem recursiveScalarBlock_notEscapes {expression : Expr} (form : AcceptedBinaryExpression expression)
    (scope fuel : Nat) : blockEscapes fuel ⟨scope, [], some expression⟩ = false := by
  cases fuel with
  | zero => simp only [blockEscapes]; flow_simp
  | succ fuel =>
    simp only [blockEscapes]; flow_simp
    cases fuel with
    | zero => flow_simp
    | succ fuel =>
      flow_simp
      simpa using recursiveScalarFlow_next form (fuel + 1)

theorem typeExpr_if_scalar_branches (fuel : Nat) (environment : TypingEnv) (condition yes no : Expr)
    (yesScope noScope origin before after conditionAfter yesAfter noAfter : Nat) (ty yesTy noTy : Ty)
    (checked : typeExpr (fuel + 1) environment (.ifE condition ⟨yesScope, [], some yes⟩ ⟨noScope, [], some no⟩ origin) before = .ok ([ty], after))
    (conditionTyped : typeExpr fuel { environment with use := .ordinary, request := .value, resultRequests := [] }
      condition before = .ok ([.bool], conditionAfter))
    (yesTyped : typeBlock fuel environment ⟨yesScope, [], some yes⟩ conditionAfter = .ok ([yesTy], yesAfter))
    (noTyped : typeBlock fuel environment ⟨noScope, [], some no⟩ yesAfter = .ok ([noTy], noAfter))
    (yesForm : AcceptedBinaryExpression yes) (noForm : AcceptedBinaryExpression no) :
    yesTy = ty ∧ noTy = ty := by
  have yesNoEscape := recursiveScalarBlock_notEscapes yesForm yesScope fuel
  have noNoEscape := recursiveScalarBlock_notEscapes noForm noScope fuel
  simp only [typeExpr, bind, StateT.bind] at checked
  change (Except.bind (typeExpr fuel
    { environment with use := .ordinary, request := .value, resultRequests := [] } condition before) _) = _ at checked
  simp only [conditionTyped, Except.bind] at checked
  change (Except.bind (typeBlock fuel environment ⟨yesScope, [], some yes⟩ conditionAfter) _) = _ at checked
  simp only [yesTyped, Except.bind] at checked
  change (Except.bind (typeBlock fuel environment ⟨noScope, [], some no⟩ yesAfter) _) = _ at checked
  simp only [noTyped, Except.bind, yesNoEscape, noNoEscape, Bool.false_and] at checked
  unfold_typing_require
  by_cases same : yesTy = noTy
  · subst noTy
    simp [bind, StateT.bind, pure, StateT.pure, Except.pure, Except.bind] at checked
    exact ⟨checked.1, checked.1⟩
  · simp [same, bind, StateT.bind, pure, StateT.pure, Except.pure, Except.bind] at checked
    change Except.error _ = Except.ok _ at checked
    cases checked

theorem validated_globalConditional_branch_types (config : EvalConfig) (accepted : AcceptedModule config)
    (id : Nat) (descriptor : Global) (present : config.module.globals[id]? = some descriptor)
    (condition yes no : Expr) (yesScope noScope origin : Nat)
    (shape : descriptor.init = .ifE condition ⟨yesScope, [], some yes⟩ ⟨noScope, [], some no⟩ origin)
    (yesForm : AcceptedBinaryExpression yes) (noForm : AcceptedBinaryExpression no)
    (scalar : (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool) :
    ∃ conditionAfter yesAfter noAfter,
      let environment := (scalarGlobalInitializerFrame config id 0 #[]).typing
      typeExpr 4095 { environment with use := .ordinary, request := .value, resultRequests := [] }
        condition 0 = .ok ([.bool], conditionAfter) ∧
      typeExpr 4094 { environment with scope := yesScope } yes conditionAfter = .ok ([descriptor.ty], yesAfter) ∧
      typeExpr 4094 { environment with scope := noScope } no yesAfter = .ok ([descriptor.ty], noAfter) := by
  obtain ⟨ty, typingAfter, typed, adapts⟩ := validated_global_initializer_typing config.module id descriptor accepted.accepted present
  rw [shape] at typed
  let environment := (scalarGlobalInitializerFrame config id 0 #[]).typing
  obtain ⟨conditionAfter, yesTypes, yesAfter, noTypes, noAfter, conditionTyped, yesTyped, noTyped⟩ :=
    typeExpr_if_branches 4095 environment condition _ _ origin 0 typingAfter [ty] typed
  have yesTail := typeBlock_empty_tail 4093 environment yesScope yes conditionAfter yesAfter yesTypes yesTyped
  have noTail := typeBlock_empty_tail 4093 environment noScope no yesAfter noAfter noTypes noTyped
  obtain ⟨yesTy, yesEq⟩ := typeExpr_scalar_singleton yesForm 4094 _ conditionAfter yesAfter yesTypes yesTail
  obtain ⟨noTy, noEq⟩ := typeExpr_scalar_singleton noForm 4094 _ yesAfter noAfter noTypes noTail
  subst yesTypes noTypes
  obtain ⟨yesAligned, noAligned⟩ := typeExpr_if_scalar_branches 4095 environment condition yes no yesScope noScope origin
    0 typingAfter conditionAfter yesAfter noAfter ty yesTy noTy typed conditionTyped yesTyped noTyped yesForm noForm
  have descriptorAligned : ty = descriptor.ty := by
    rcases scalar with ⟨intTy, same⟩ | same <;> rw [same] at adapts ⊢ <;>
      cases ty <;> simp_all [Ty.adaptsTo, Ty.element?]
  subst ty yesTy noTy
  exact ⟨conditionAfter, yesAfter, noAfter, conditionTyped, yesTail, noTail⟩

theorem accepted_globalConditional_aligned_tails (config : EvalConfig) (accepted : AcceptedModule config)
    (id : Nat) (descriptor : Global) (before : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (world : AcceptedWorld config id before ambient types live [] []) (clear : FutureGlobalsClear config id before)
    (present : config.module.globals[id]? = some descriptor) (condition yes no : Expr) (yesScope noScope origin : Nat)
    (shape : descriptor.init = .ifE condition ⟨yesScope, [], some yes⟩ ⟨noScope, [], some no⟩ origin)
    (conditionForm : AcceptedBinaryExpression condition) (yesForm : AcceptedBinaryExpression yes) (noForm : AcceptedBinaryExpression no)
    (scalar : (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool) :
    ∃ names yesRoots noRoots yesAfter noAfter conditionCursor yesCursor,
      let activated := { before with nextAct := before.nextAct + 1 }
      let scopeState := { activated with nextScope := activated.nextScope + 1 }
      let yesFrame := scalarGlobalBranchFrame config id before.nextAct names yesScope activated.nextScope conditionCursor
      let noFrame := scalarGlobalBranchFrame config id before.nextAct names noScope activated.nextScope yesCursor
      AcceptedWorld config id scopeState ambient types live [] [] ∧
      AcceptedFrame config accepted yesFrame scopeState types ∧ AcceptedFrame config accepted noFrame scopeState types ∧
      CheckedValue yesFrame yes descriptor.ty yesRoots 0 yesAfter ∧ CheckedValue noFrame no descriptor.ty noRoots 0 noAfter := by
  obtain ⟨names, yesTy, noTy, yesRoots, noRoots, yesAfter, noAfter, conditionCursor, yesCursor,
    scopeWorld, yesSource, noSource, yesChecked, noChecked⟩ :=
    accepted_globalConditional_scoped_tails config accepted id descriptor before ambient types live world clear present
      condition yes no yesScope noScope origin shape conditionForm yesForm noForm
  obtain ⟨conditionAfter, yesTypingAfter, noTypingAfter, conditionTyped, yesTyped, noTyped⟩ :=
    validated_globalConditional_branch_types config accepted id descriptor present condition yes no yesScope noScope origin
      shape yesForm noForm scalar
  obtain ⟨conditionNames, conditionRoots, checkedAfter, rootsAfter, activeWorld, conditionSource, conditionChecked⟩ :=
    accepted_globalConditional_condition config accepted id descriptor before ambient types live world clear present
      condition _ _ origin shape conditionForm
  let conditionFrame := ordinaryOperandFrame (scalarGlobalInitializerFrame config id before.nextAct conditionNames) 4095
  have conditionFacts := checked_binary_recursive_cursor conditionForm conditionFrame .bool conditionRoots checkedAfter rootsAfter conditionChecked
  have checkedZero : checkedAfter = 0 := by
    simpa [conditionFrame, ordinaryOperandFrame, scalarGlobalInitializerFrame] using conditionFacts.1
  have sameCondition : conditionAfter = 0 := by
    have checkedCondition := conditionChecked.typing
    rw [checkedZero] at checkedCondition
    have same : (Except.ok ([Ty.bool], conditionAfter) : Except Goose.Core.Rejection (List Ty × Nat)) = Except.ok ([Ty.bool], 0) := by
      calc
        _ = typeExpr 4095 { (scalarGlobalInitializerFrame config id 0 #[]).typing with
          use := .ordinary, request := .value, resultRequests := [] } condition 0 := conditionTyped.symm
        _ = _ := by simpa [conditionFrame, ordinaryOperandFrame, scalarGlobalInitializerFrame] using checkedCondition
    cases same
    rfl
  rw [sameCondition] at yesTyped
  have yesSame : yesTy = descriptor.ty ∧ yesTypingAfter = 0 := by
    have actual := yesChecked.typing
    have same : (Except.ok ([yesTy], 0) : Except Goose.Core.Rejection (List Ty × Nat)) = Except.ok ([descriptor.ty], yesTypingAfter) := by
      calc
        _ = typeExpr 4094 { (scalarGlobalInitializerFrame config id 0 #[]).typing with scope := yesScope } yes 0 := by
          simpa [scalarGlobalBranchFrame, scalarGlobalInitializerFrame] using actual.symm
        _ = _ := yesTyped
    cases same
    exact ⟨rfl, rfl⟩
  rw [yesSame.2] at noTyped
  have noSame : noTy = descriptor.ty := by
    have actual := noChecked.typing
    have same : (Except.ok ([noTy], 0) : Except Goose.Core.Rejection (List Ty × Nat)) = Except.ok ([descriptor.ty], noTypingAfter) := by
      calc
        _ = typeExpr 4094 { (scalarGlobalInitializerFrame config id 0 #[]).typing with scope := noScope } no 0 := by
          simpa [scalarGlobalBranchFrame, scalarGlobalInitializerFrame] using actual.symm
        _ = _ := noTyped
    cases same
    rfl
  rw [yesSame.1] at yesChecked
  rw [noSame] at noChecked
  exact ⟨names, yesRoots, noRoots, yesAfter, noAfter, conditionCursor, yesCursor,
    scopeWorld, yesSource, noSource, yesChecked, noChecked⟩

theorem execBlock_checked_globalScalar (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (id act scope : Nat) (names : Array (List RootRef)) (cursor : RState) (expression : Expr)
    (form : AcceptedBinaryExpression expression) (ty : Ty) (roots : List RootRef) (rootAfter : RState)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (world : AcceptedWorld config id before ambient types live [] []) (clear : FutureGlobalsClear config id before)
    (source : AcceptedFrame config accepted (scalarGlobalBranchFrame config id act names scope before.nextScope cursor)
      { before with nextScope := before.nextScope + 1 } types)
    (checked : CheckedValue (scalarGlobalBranchFrame config id act names scope before.nextScope cursor)
      expression ty roots 0 rootAfter) :
    ∃ nextLive,
      let outcome := execBlock fuel config ⟨0, act, #[], [], []⟩ [] [] ⟨scope, [], some expression⟩ before
      let after := Goose.Proofs.Exit.stepState outcome
      AcceptedWorld config id after ambient types nextLive [] [] ∧ FutureGlobalsClear config id after ∧
      (match outcome with
       | .ok (.normal value) _ => ValueRepresentation ty value ∧ PointerTypedValue types ty value
       | .stop .. => True | _ => False) := by
  let environment : RuntimeActivation := ⟨0, act, #[], [], []⟩
  let entered := { before with nextScope := before.nextScope + 1 }
  let frame := scalarGlobalBranchFrame config id act names scope before.nextScope cursor
  have scopeWorld := (freshScope_acceptedWorld config id before ambient types live world).2
  have scopeClear : FutureGlobalsClear config id entered := clear
  change ∃ nextLive, let outcome := execBlock fuel config environment [] [] ⟨scope, [], some expression⟩ before
    let after := Goose.Proofs.Exit.stepState outcome
    AcceptedWorld config id after ambient types nextLive [] [] ∧ FutureGlobalsClear config id after ∧
      (match outcome with
       | .ok (.normal value) _ => ValueRepresentation ty value ∧ PointerTypedValue types ty value
       | .stop .. => True | _ => False)
  cases fuel with
  | zero =>
    simp only [execBlock, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
    exact ⟨live, world, clear, trivial⟩
  | succ fuel =>
    cases fuel with
    | zero =>
      have stopped : execBlock 1 config environment [] [] ⟨scope, [], some expression⟩ before = .stop .timeout entered := by
        simp [execBlock, freshScope, EvalM.get, EvalM.set, bind, pure, withScope, bindAll, execStmts, timeout, EvalM.stop, entered]
      simp only [stopped, Goose.Proofs.Exit.stepState]
      exact ⟨live, scopeWorld, scopeClear, trivial⟩
    | succ fuel =>
      have evaluated := evalValue_checked_binary_recursive form (fuel + 1) config accepted frame entered ambient types live [] []
        scopeWorld source ty roots 0 rootAfter checked
      let branchEnv := frame.interpretation.environment
      change Goose.Proofs.Exit.stepState (evalValue (fuel + 1) config branchEnv expression entered) = entered ∧ _ at evaluated
      cases execution : evalValue (fuel + 1) config branchEnv expression entered with
      | escape address carriers after =>
        exact ((evalValue_scalar_controlFree form (fuel + 1) config branchEnv).1 entered address carriers after execution).elim
      | jump target kind after =>
        exact ((evalValue_scalar_controlFree form (fuel + 1) config branchEnv).2 entered target kind after execution).elim
      | stop reason after =>
        have same : after = entered := by simpa [execution, Goose.Proofs.Exit.stepState] using evaluated.1
        subst after
        change evalValue (fuel + 1) config ⟨0, act, #[], [(scope, before.nextScope)], []⟩ expression entered = .stop reason entered at execution
        have stopped : execBlock (fuel + 2) config environment [] [] ⟨scope, [], some expression⟩ before = .stop reason entered := by
          simp [execBlock, freshScope, EvalM.get, EvalM.set, bind, pure, withScope, bindAll, execStmts,
            execution, environment, entered]
        simp only [stopped, Goose.Proofs.Exit.stepState]
        exact ⟨live, scopeWorld, scopeClear, trivial⟩
      | ok value after =>
        have same : after = entered := by simpa [execution, Goose.Proofs.Exit.stepState] using evaluated.1
        subst after
        have valid := evaluated.2.1 value entered execution
        let released := releaseScopeState environment scope before.nextScope entered
        have releasedWorld := scopeWorld.releaseScope config id entered ambient types live [] [] environment scope before.nextScope
        have releasedClear : FutureGlobalsClear config id released := by
          intro global future within
          simpa [released, releaseScopeState, environment] using clear global future within
        change evalValue (fuel + 1) config ⟨0, act, #[], [(scope, before.nextScope)], []⟩ expression entered = .ok value entered at execution
        have done : execBlock (fuel + 2) config environment [] [] ⟨scope, [], some expression⟩ before = .ok (.normal value) released := by
          simp [execBlock, freshScope, EvalM.get, EvalM.set, bind, pure, withScope, bindAll, execStmts,
            releaseScope, released, execution, environment, entered]
        simp only [done, Goose.Proofs.Exit.stepState]
        exact ⟨_, releasedWorld, releasedClear, valid.represented, valid.pointers⟩

#print axioms execBlock_checked_globalScalar
#print axioms accepted_globalConditional_aligned_tails
#print axioms validated_globalConditional_branch_types
#print axioms typeExpr_if_scalar_branches
#print axioms recursiveScalarBlock_notEscapes
end Goose.Proofs.ConstructionAcceptedExecution
