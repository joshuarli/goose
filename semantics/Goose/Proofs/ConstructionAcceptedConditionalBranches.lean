import Goose.Proofs.ConstructionAcceptedConditionalTyping
import Goose.Proofs.ConstructionAcceptedBlockTailChecks

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionExecutionOwnership

theorem typeExpr_if_branches (fuel : Nat) (environment : TypingEnv) (condition : Expr)
    (yes no : Block) (origin : Nat) (before after : Nat) (types : List Ty)
    (checked : typeExpr (fuel + 1) environment (.ifE condition yes no origin) before = .ok (types, after)) :
    ∃ conditionAfter yesTypes yesAfter noTypes noAfter,
      typeExpr fuel { environment with use := .ordinary, request := .value, resultRequests := [] }
        condition before = .ok ([.bool], conditionAfter) ∧
      typeBlock fuel environment yes conditionAfter = .ok (yesTypes, yesAfter) ∧
      typeBlock fuel environment no yesAfter = .ok (noTypes, noAfter) := by
  simp only [typeExpr, bind, StateT.bind] at checked
  change (Except.bind (typeExpr fuel
    { environment with use := .ordinary, request := .value, resultRequests := [] } condition before) _) = _ at checked
  cases first : typeExpr fuel
      { environment with use := .ordinary, request := .value, resultRequests := [] } condition before with
  | error failure => simp only [first, Except.bind] at checked; cases checked
  | ok result =>
    obtain ⟨conditionTypes, middle⟩ := result
    simp only [first, Except.bind] at checked
    cases conditionTypes with
    | nil => change Except.error _ = Except.ok _ at checked; cases checked
    | cons conditionType tail =>
      cases tail with
      | cons other rest => change Except.error _ = Except.ok _ at checked; cases checked
      | nil =>
        cases conditionType <;> try (change Except.error _ = Except.ok _ at checked; cases checked)
        case bool =>
          change (Except.bind (typeBlock fuel environment yes middle) _) = _ at checked
          cases second : typeBlock fuel environment yes middle with
          | error failure => simp only [second, Except.bind] at checked; cases checked
          | ok yesResult =>
            obtain ⟨yesTypes, yesAfter⟩ := yesResult
            simp only [second, Except.bind] at checked
            change (Except.bind (typeBlock fuel environment no yesAfter) _) = _ at checked
            cases third : typeBlock fuel environment no yesAfter with
            | error failure => simp only [third, Except.bind] at checked; cases checked
            | ok noResult =>
              obtain ⟨noTypes, noAfter⟩ := noResult
              exact ⟨middle, yesTypes, yesAfter, noTypes, noAfter, rfl, second, third⟩

theorem rpExpr_if_branches (environment : PEnv) (condition : Expr) (yes no : Block) (origin : Nat)
    (before after : RState) (roots : List RootRef)
    (checked : rpExpr environment (.ifE condition yes no origin) before = .ok (roots, after)) :
    ∃ conditionRoots conditionAfter yesResult yesAfter noResult,
      rpExpr environment condition before = .ok (conditionRoots, conditionAfter) ∧
      rpBlockValue environment [] yes conditionAfter = .ok (yesResult, yesAfter) ∧
      rpBlockValue environment [] no yesAfter = .ok (noResult, after) := by
  change (Except.bind (rpExpr environment condition before) _) = .ok (roots, after) at checked
  cases first : rpExpr environment condition before with
  | error failure => simp only [first, Except.bind] at checked; cases checked
  | ok result =>
    obtain ⟨conditionRoots, conditionAfter⟩ := result
    simp only [first, Except.bind] at checked
    change (Except.bind (rpBlockValue environment [] yes conditionAfter) _) = _ at checked
    cases second : rpBlockValue environment [] yes conditionAfter with
    | error failure => simp only [second, Except.bind] at checked; cases checked
    | ok result =>
      obtain ⟨yesResult, yesAfter⟩ := result
      simp only [second, Except.bind] at checked
      change (Except.bind (rpBlockValue environment [] no yesAfter) _) = _ at checked
      cases third : rpBlockValue environment [] no yesAfter with
      | error failure => simp only [third, Except.bind] at checked; cases checked
      | ok result =>
        obtain ⟨noResult, noAfter⟩ := result
        simp only [third, Except.bind] at checked
        change Except.ok (_, noAfter) = Except.ok (roots, after) at checked
        cases checked
        exact ⟨conditionRoots, conditionAfter, yesResult, yesAfter, noResult, rfl, second, third⟩

theorem typeBlock_empty_tail (fuel : Nat) (environment : TypingEnv) (scope : Nat) (expression : Expr)
    (before after : Nat) (types : List Ty)
    (checked : typeBlock (fuel + 2) environment ⟨scope, [], some expression⟩ before = .ok (types, after)) :
    typeExpr (fuel + 1) { environment with scope := scope } expression before = .ok (types, after) := by
  simpa [typeBlock, typeStatements, bind, StateT.bind, pure, StateT.pure, Except.pure, Except.bind] using checked

theorem rpBlockValue_empty_tail (environment : PEnv) (scope : Nat) (expression : Expr)
    (before after : RState) (result : List RootRef × (Nat × Nat))
    (checked : rpBlockValue environment [] ⟨scope, [], some expression⟩ before = .ok (result, after)) :
    ∃ roots, rpExpr { environment with scopes := scope :: environment.scopes } expression before = .ok (roots, after) := by
  obtain ⟨_, middle, roots, statements, tail, _⟩ := rpBlockValue_body checked
  simp [rpStmts, pure, StateT.pure, Except.pure] at statements
  subst middle
  exact ⟨roots, tail⟩

theorem accepted_globalConditional_tail_checks (config : EvalConfig) (accepted : AcceptedModule config)
    (id : Nat) (descriptor : Global) (before : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (world : AcceptedWorld config id before ambient types live [] []) (clear : FutureGlobalsClear config id before)
    (present : config.module.globals[id]? = some descriptor) (condition yes no : Expr) (yesScope noScope origin : Nat)
    (shape : descriptor.init = .ifE condition ⟨yesScope, [], some yes⟩ ⟨noScope, [], some no⟩ origin)
    (conditionForm : AcceptedBinaryExpression condition) (yesForm : AcceptedBinaryExpression yes) (noForm : AcceptedBinaryExpression no) :
    ∃ names conditionTyping yesTyping noTyping yesTy noTy conditionRoots conditionCursor yesRoots yesCursor noRoots noCursor,
      let frame := scalarGlobalInitializerFrame config id before.nextAct names
      typeExpr 4094 { frame.typing with scope := yesScope } yes conditionTyping = .ok ([yesTy], yesTyping) ∧
      typeExpr 4094 { frame.typing with scope := noScope } no yesTyping = .ok ([noTy], noTyping) ∧
      rpExpr frame.source condition frame.rootCursor = .ok (conditionRoots, conditionCursor) ∧
      rpExpr { frame.source with scopes := yesScope :: frame.source.scopes } yes conditionCursor = .ok (yesRoots, yesCursor) ∧
      rpExpr { frame.source with scopes := noScope :: frame.source.scopes } no yesCursor = .ok (noRoots, noCursor) ∧
      GlobalEffectTargetsBounded conditionCursor.eff id ∧ GlobalEffectTargetsBounded yesCursor.eff id ∧
      GlobalEffectTargetsBounded noCursor.eff id := by
  obtain ⟨names, activeWorld, frameSource, roots, rootsAfter, rooted⟩ :=
    accepted_scalarGlobalInitializer_frame config accepted id descriptor before ambient types live world clear present
  obtain ⟨ty, typingAfter, typed, adapts⟩ := validated_global_initializer_typing config.module id descriptor accepted.accepted present
  rw [shape] at typed rooted
  let frame := scalarGlobalInitializerFrame config id before.nextAct names
  obtain ⟨conditionTyping, yesTypes, yesTyping, noTypes, noTyping, conditionTyped, yesTyped, noTyped⟩ :=
    typeExpr_if_branches 4095 frame.typing condition _ _ origin 0 typingAfter [ty] typed
  have yesTail := typeBlock_empty_tail 4093 frame.typing yesScope yes conditionTyping yesTyping yesTypes yesTyped
  have noTail := typeBlock_empty_tail 4093 frame.typing noScope no yesTyping noTyping noTypes noTyped
  obtain ⟨yesTy, yesSingle⟩ := typeExpr_scalar_singleton yesForm 4094 _ conditionTyping yesTyping yesTypes yesTail
  obtain ⟨noTy, noSingle⟩ := typeExpr_scalar_singleton noForm 4094 _ yesTyping noTyping noTypes noTail
  subst yesTypes noTypes
  obtain ⟨conditionRoots, conditionCursor, yesResult, yesCursor, noResult, conditionRooted, yesRooted, noRooted⟩ :=
    rpExpr_if_branches frame.source condition _ _ origin frame.rootCursor rootsAfter roots rooted
  obtain ⟨yesRoots, yesTailRooted⟩ := rpBlockValue_empty_tail frame.source yesScope yes conditionCursor yesCursor yesResult yesRooted
  obtain ⟨noRoots, noTailRooted⟩ := rpBlockValue_empty_tail frame.source noScope no yesCursor rootsAfter noResult noRooted
  have initial : GlobalEffectTargetsBounded frame.rootCursor.eff id := by
    simp [frame, scalarGlobalInitializerFrame, GlobalEffectTargetsBounded, Eff.accessTargets]
  have conditionBound := recursiveScalar_effects_bounded conditionForm 4095
    { frame.typing with use := .ordinary, request := .value, resultRequests := [] } frame.source id 0 conditionTyping
    frame.rootCursor conditionCursor [.bool] conditionRoots (by simp [frame, scalarGlobalInitializerFrame]) initial conditionTyped conditionRooted
  have yesBound := recursiveScalar_effects_bounded yesForm 4094
    { frame.typing with scope := yesScope } { frame.source with scopes := yesScope :: frame.source.scopes } id
    conditionTyping yesTyping conditionCursor yesCursor [yesTy] yesRoots (by simp [frame, scalarGlobalInitializerFrame])
    conditionBound yesTail yesTailRooted
  have noBound := recursiveScalar_effects_bounded noForm 4094
    { frame.typing with scope := noScope } { frame.source with scopes := noScope :: frame.source.scopes } id
    yesTyping noTyping yesCursor rootsAfter [noTy] noRoots (by simp [frame, scalarGlobalInitializerFrame])
    yesBound noTail noTailRooted
  exact ⟨names, conditionTyping, yesTyping, noTyping, yesTy, noTy, conditionRoots, conditionCursor,
    yesRoots, yesCursor, noRoots, rootsAfter, yesTail, noTail, conditionRooted, yesTailRooted, noTailRooted,
    conditionBound, yesBound, noBound⟩

#print axioms accepted_globalConditional_tail_checks
#print axioms rpBlockValue_empty_tail
#print axioms typeBlock_empty_tail
#print axioms rpExpr_if_branches
#print axioms typeExpr_if_branches
end Goose.Proofs.ConstructionAcceptedExecution
