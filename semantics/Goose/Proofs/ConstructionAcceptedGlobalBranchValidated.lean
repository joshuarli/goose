import Goose.Proofs.ConstructionAcceptedGlobalBranchFlow

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation

theorem accepted_globalConditional_yesBlock (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (id : Nat) (descriptor : Global) (before : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (world : AcceptedWorld config id before ambient types live [] []) (clear : FutureGlobalsClear config id before)
    (present : config.module.globals[id]? = some descriptor) (condition yes no : Expr)
    (yesStatements noStatements : List Stmt) (yesScope noScope origin : Nat)
    (shape : descriptor.init = .ifE condition ⟨yesScope, yesStatements, some yes⟩ ⟨noScope, noStatements, some no⟩ origin)
    (conditionForm : AcceptedBinaryExpression condition) (yesForm : AcceptedBinaryExpression yes) (noForm : AcceptedBinaryExpression no)
    (yesStatementsForm : ScalarExpressionStatements yesStatements) (noStatementsForm : ScalarExpressionStatements noStatements)
    (scalar : (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool) :
    ∃ nextLive,
      let activated := { before with nextAct := before.nextAct + 1 }
      let outcome := execBlock fuel config ⟨0, before.nextAct, #[], [], []⟩ [] [] ⟨yesScope, yesStatements, some yes⟩ activated
      let after := Goose.Proofs.Exit.stepState outcome
      AcceptedWorld config id after ambient types nextLive [] [] ∧ FutureGlobalsClear config id after ∧
      (match outcome with | .ok (.normal value) _ => ValueRepresentation descriptor.ty value ∧ PointerTypedValue types descriptor.ty value | .stop .. => True | _ => False) := by
  obtain ⟨names, activeWorld, source, roots, rootsAfter, rooted⟩ :=
    accepted_scalarGlobalInitializer_frame config accepted id descriptor before ambient types live world clear present
  obtain ⟨ty, typingAfter, typed, adapts⟩ := validated_global_initializer_typing config.module id descriptor accepted.accepted present
  rw [shape] at typed rooted
  let base := scalarGlobalInitializerFrame config id before.nextAct names
  obtain ⟨conditionTyping, yesTypes, yesTyping, noTypes, noTyping, conditionTyped, yesTyped, noTyped⟩ :=
    typeExpr_if_branches 4095 base.typing condition _ _ origin 0 typingAfter [ty] typed
  obtain ⟨conditionRoots, conditionCursor, yesResult, yesCursor, noResult, conditionRooted, yesRooted, noRooted⟩ :=
    rpExpr_if_branches base.source condition _ _ origin base.rootCursor rootsAfter roots rooted
  obtain ⟨yesNext, yesMiddle, yesRootsMiddle, yesRoots, yesStatementsTyped, yesTailTyped, yesStatementsRooted, yesTailRooted⟩ :=
    globalBranch_blockChecks 4094 base.typing base.source yesScope yesStatements yes conditionTyping yesTyping yesTypes
      conditionCursor yesCursor yesResult yesTyped yesRooted
  obtain ⟨noNext, noMiddle, noRootsMiddle, noRoots, noStatementsTyped, noTailTyped, noStatementsRooted, noTailRooted⟩ :=
    globalBranch_blockChecks 4094 base.typing base.source noScope noStatements no yesTyping noTyping noTypes
      yesCursor rootsAfter noResult noTyped noRooted
  obtain ⟨yesTy, yesSingle⟩ := typeExpr_scalar_singleton yesForm 4094 yesNext yesMiddle yesTyping yesTypes yesTailTyped
  obtain ⟨noTy, noSingle⟩ := typeExpr_scalar_singleton noForm 4094 noNext noMiddle noTyping noTypes noTailTyped
  subst yesTypes noTypes
  obtain ⟨yesType, noType⟩ := typeExpr_if_statementBranches 4095 base.typing condition yes no yesStatements noStatements
    yesScope noScope origin 0 typingAfter conditionTyping yesTyping noTyping ty yesTy noTy typed conditionTyped yesTyped noTyped
    yesForm noForm yesStatementsForm noStatementsForm
  have descriptorType : ty = descriptor.ty := by
    rcases scalar with ⟨intTy, same⟩ | same <;> rw [same] at adapts ⊢ <;>
      cases ty <;> simp_all [Ty.adaptsTo, Ty.element?]
  have yesDescriptor : yesTy = descriptor.ty := yesType.trans descriptorType
  have initialBound : GlobalEffectTargetsBounded base.rootCursor.eff id := by
    simp [base, scalarGlobalInitializerFrame, GlobalEffectTargetsBounded, Eff.accessTargets]
  have conditionBound := recursiveScalar_effects_bounded conditionForm 4095
    { base.typing with use := .ordinary, request := .value, resultRequests := [] } base.source id 0 conditionTyping
    base.rootCursor conditionCursor [.bool] conditionRoots (by simp [base, scalarGlobalInitializerFrame]) initialBound conditionTyped conditionRooted
  have conditionAvailable : GlobalEffectsAvailable base.interpretation id conditionCursor.eff := by
    intro target member global instantiates
    cases target with
    | global other =>
      change global = other at instantiates
      subst global
      exact conditionBound other member
    | param parameter => exact instantiates.1.elim
  let conditionFrame := ordinaryOperandFrame base 4095
  have conditionChecked : CheckedValue conditionFrame condition .bool conditionRoots conditionTyping conditionCursor :=
    ⟨conditionTyped, conditionRooted, conditionAvailable⟩
  have conditionFacts := checked_binary_recursive_cursor conditionForm conditionFrame .bool conditionRoots conditionTyping conditionCursor conditionChecked
  have typingZero : conditionTyping = 0 := by simpa [conditionFrame, ordinaryOperandFrame, base, scalarGlobalInitializerFrame] using conditionFacts.1
  have cursorZero : conditionCursor.nextVar = 0 := by simpa [conditionFrame, ordinaryOperandFrame, base, scalarGlobalInitializerFrame] using conditionFacts.2
  let activated := { before with nextAct := before.nextAct + 1 }
  obtain ⟨_, branchSource⟩ := accepted_scalarGlobalBranch_frame_from config accepted id before ambient types live names clear
    yesScope conditionCursor cursorZero activeWorld source
  rw [typingZero] at yesStatementsTyped
  rw [yesDescriptor] at yesTailTyped
  have result := execBlock_checked_globalStatements fuel config accepted id before.nextAct yesScope names conditionCursor yesStatements yes
    yesStatementsForm yesForm yesNext yesMiddle yesTyping yesRootsMiddle yesCursor yesRoots descriptor.ty activated ambient types live
    activeWorld clear.freshAct branchSource conditionBound
    (by simpa [base, scalarGlobalBranchFrame, scalarGlobalInitializerFrame] using yesStatementsTyped)
    yesTailTyped
    (by simpa [base, scalarGlobalBranchFrame, scalarGlobalInitializerFrame, initializerSource] using yesStatementsRooted)
    (by simpa [base, scalarGlobalBranchFrame, scalarGlobalInitializerFrame, initializerSource] using yesTailRooted)
  exact result

theorem accepted_globalConditional_noBlock (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (id : Nat) (descriptor : Global) (before : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (world : AcceptedWorld config id before ambient types live [] []) (clear : FutureGlobalsClear config id before)
    (present : config.module.globals[id]? = some descriptor) (condition yes no : Expr)
    (yesStatements noStatements : List Stmt) (yesScope noScope origin : Nat)
    (shape : descriptor.init = .ifE condition ⟨yesScope, yesStatements, some yes⟩ ⟨noScope, noStatements, some no⟩ origin)
    (conditionForm : AcceptedBinaryExpression condition) (yesForm : AcceptedBinaryExpression yes) (noForm : AcceptedBinaryExpression no)
    (yesStatementsForm : ScalarExpressionStatements yesStatements) (noStatementsForm : ScalarExpressionStatements noStatements)
    (scalar : (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool) :
    ∃ nextLive,
      let activated := { before with nextAct := before.nextAct + 1 }
      let outcome := execBlock fuel config ⟨0, before.nextAct, #[], [], []⟩ [] [] ⟨noScope, noStatements, some no⟩ activated
      let after := Goose.Proofs.Exit.stepState outcome
      AcceptedWorld config id after ambient types nextLive [] [] ∧ FutureGlobalsClear config id after ∧
      (match outcome with | .ok (.normal value) _ => ValueRepresentation descriptor.ty value ∧ PointerTypedValue types descriptor.ty value | .stop .. => True | _ => False) := by
  obtain ⟨names, activeWorld, source, roots, rootsAfter, rooted⟩ :=
    accepted_scalarGlobalInitializer_frame config accepted id descriptor before ambient types live world clear present
  obtain ⟨ty, typingAfter, typed, adapts⟩ := validated_global_initializer_typing config.module id descriptor accepted.accepted present
  rw [shape] at typed rooted
  let base := scalarGlobalInitializerFrame config id before.nextAct names
  obtain ⟨conditionTyping, yesTypes, yesTyping, noTypes, noTyping, conditionTyped, yesTyped, noTyped⟩ :=
    typeExpr_if_branches 4095 base.typing condition _ _ origin 0 typingAfter [ty] typed
  obtain ⟨conditionRoots, conditionCursor, yesResult, yesCursor, noResult, conditionRooted, yesRooted, noRooted⟩ :=
    rpExpr_if_branches base.source condition _ _ origin base.rootCursor rootsAfter roots rooted
  obtain ⟨yesNext, yesMiddle, yesRootsMiddle, yesRoots, yesStatementsTyped, yesTailTyped, yesStatementsRooted, yesTailRooted⟩ :=
    globalBranch_blockChecks 4094 base.typing base.source yesScope yesStatements yes conditionTyping yesTyping yesTypes
      conditionCursor yesCursor yesResult yesTyped yesRooted
  obtain ⟨noNext, noMiddle, noRootsMiddle, noRoots, noStatementsTyped, noTailTyped, noStatementsRooted, noTailRooted⟩ :=
    globalBranch_blockChecks 4094 base.typing base.source noScope noStatements no yesTyping noTyping noTypes
      yesCursor rootsAfter noResult noTyped noRooted
  obtain ⟨yesTy, yesSingle⟩ := typeExpr_scalar_singleton yesForm 4094 yesNext yesMiddle yesTyping yesTypes yesTailTyped
  obtain ⟨noTy, noSingle⟩ := typeExpr_scalar_singleton noForm 4094 noNext noMiddle noTyping noTypes noTailTyped
  subst yesTypes noTypes
  obtain ⟨yesType, noType⟩ := typeExpr_if_statementBranches 4095 base.typing condition yes no yesStatements noStatements
    yesScope noScope origin 0 typingAfter conditionTyping yesTyping noTyping ty yesTy noTy typed conditionTyped yesTyped noTyped
    yesForm noForm yesStatementsForm noStatementsForm
  have descriptorType : ty = descriptor.ty := by
    rcases scalar with ⟨intTy, same⟩ | same <;> rw [same] at adapts ⊢ <;>
      cases ty <;> simp_all [Ty.adaptsTo, Ty.element?]
  have yesDescriptor : yesTy = descriptor.ty := yesType.trans descriptorType
  have initialBound : GlobalEffectTargetsBounded base.rootCursor.eff id := by
    simp [base, scalarGlobalInitializerFrame, GlobalEffectTargetsBounded, Eff.accessTargets]
  have conditionBound := recursiveScalar_effects_bounded conditionForm 4095
    { base.typing with use := .ordinary, request := .value, resultRequests := [] } base.source id 0 conditionTyping
    base.rootCursor conditionCursor [.bool] conditionRoots (by simp [base, scalarGlobalInitializerFrame]) initialBound conditionTyped conditionRooted
  have conditionAvailable : GlobalEffectsAvailable base.interpretation id conditionCursor.eff := by
    intro target member global instantiates
    cases target with
    | global other =>
      change global = other at instantiates
      subst global
      exact conditionBound other member
    | param parameter => exact instantiates.1.elim
  let conditionFrame := ordinaryOperandFrame base 4095
  have conditionChecked : CheckedValue conditionFrame condition .bool conditionRoots conditionTyping conditionCursor :=
    ⟨conditionTyped, conditionRooted, conditionAvailable⟩
  have conditionFacts := checked_binary_recursive_cursor conditionForm conditionFrame .bool conditionRoots conditionTyping conditionCursor conditionChecked
  have typingZero : conditionTyping = 0 := by simpa [conditionFrame, ordinaryOperandFrame, base, scalarGlobalInitializerFrame] using conditionFacts.1
  have cursorZero : conditionCursor.nextVar = 0 := by simpa [conditionFrame, ordinaryOperandFrame, base, scalarGlobalInitializerFrame] using conditionFacts.2
  let activated := { before with nextAct := before.nextAct + 1 }
  obtain ⟨_, branchSource⟩ := accepted_scalarGlobalBranch_frame_from config accepted id before ambient types live names clear
    yesScope conditionCursor cursorZero activeWorld source
  rw [typingZero] at yesStatementsTyped
  rw [yesDescriptor] at yesTailTyped
  let yesFrame := scalarGlobalBranchFrame config id before.nextAct names yesScope activated.nextScope conditionCursor
  have yesStatementsTyped' : typeStatements 4094 yesFrame.typing yesStatements 0 = .ok (yesNext, yesMiddle) := by
    simpa [yesFrame, base, scalarGlobalBranchFrame, scalarGlobalInitializerFrame] using yesStatementsTyped
  have yesStatementsRooted' : rpStmts yesFrame.source yesStatements conditionCursor = .ok ((), yesRootsMiddle) := by
    simpa [yesFrame, base, scalarGlobalBranchFrame, scalarGlobalInitializerFrame, initializerSource] using yesStatementsRooted
  have yesTailRooted' : rpExpr yesFrame.source yes yesRootsMiddle = .ok (yesRoots, yesCursor) := by
    simpa [yesFrame, base, scalarGlobalBranchFrame, scalarGlobalInitializerFrame, initializerSource] using yesTailRooted
  obtain ⟨yesStatementsChecked, yesTailSource, yesTailChecked⟩ := accepted_globalBranch_statements_tail config accepted id before.nextAct
    yesScope activated.nextScope names conditionCursor yesStatements yes yesStatementsForm yesForm _ types yesNext yesMiddle yesTyping
    yesRootsMiddle yesCursor yesRoots branchSource conditionBound yesStatementsTyped' yesTailTyped yesStatementsRooted' yesTailRooted'
  have limit : base.typing.globalLimit ≤ id := by simp [base, scalarGlobalInitializerFrame]
  have ⟨yesNextSame, yesMiddleBound⟩ := scalarExpressionStatements_effects_bounded yesStatementsForm 4094
    { base.typing with scope := yesScope } yesNext { base.source with scopes := yesScope :: base.source.scopes } id
    0 yesMiddle conditionCursor yesRootsMiddle limit conditionBound yesStatementsTyped yesStatementsRooted
  have yesMiddleZero : yesMiddle = 0 := by
    have bound := yesTailSource.compatible.typingBound
    simpa [yesFrame, base, yesNextSame, scalarGlobalBranchFrame, scalarGlobalInitializerFrame] using bound
  have yesRootsMiddleZero : yesRootsMiddle.nextVar = 0 := by
    have bound := yesTailSource.compatible.declarations
    simpa [yesFrame, scalarGlobalBranchFrame, scalarGlobalInitializerFrame, yesMiddleZero] using bound
  let yesTailFrame := { yesFrame with
    typing := yesNext
    typingCounter := yesMiddle
    rootCursor := yesRootsMiddle }
  have yesFacts := checked_binary_recursive_cursor yesForm yesTailFrame descriptor.ty yesRoots yesTyping yesCursor yesTailChecked
  have yesTypingZero : yesTyping = 0 := by simpa [yesTailFrame, yesMiddleZero] using yesFacts.1
  have yesCursorZero : yesCursor.nextVar = 0 := by simpa [yesTailFrame, yesRootsMiddleZero] using yesFacts.2
  have yesBound := recursiveScalar_effects_bounded yesForm 4094 yesNext
    { base.source with scopes := yesScope :: base.source.scopes } id yesMiddle yesTyping yesRootsMiddle yesCursor
    [descriptor.ty] yesRoots (by simpa [yesNextSame] using limit) yesMiddleBound yesTailTyped yesTailRooted
  obtain ⟨_, noSource⟩ := accepted_scalarGlobalBranch_frame_from config accepted id before ambient types live names clear
    noScope yesCursor yesCursorZero activeWorld source
  have noDescriptor : noTy = descriptor.ty := noType.trans descriptorType
  rw [yesTypingZero] at noStatementsTyped
  rw [noDescriptor] at noTailTyped
  have result := execBlock_checked_globalStatements fuel config accepted id before.nextAct noScope names yesCursor noStatements no
    noStatementsForm noForm noNext noMiddle noTyping noRootsMiddle rootsAfter noRoots descriptor.ty activated ambient types live
    activeWorld clear.freshAct noSource yesBound
    (by simpa [base, scalarGlobalBranchFrame, scalarGlobalInitializerFrame] using noStatementsTyped)
    noTailTyped
    (by simpa [base, scalarGlobalBranchFrame, scalarGlobalInitializerFrame, initializerSource] using noStatementsRooted)
    (by simpa [base, scalarGlobalBranchFrame, scalarGlobalInitializerFrame, initializerSource] using noTailRooted)
  exact result

#print axioms accepted_globalConditional_noBlock
#print axioms accepted_globalConditional_yesBlock
end Goose.Proofs.ConstructionAcceptedExecution
