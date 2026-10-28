import Goose.Proofs.ConstructionAcceptedNestedTransitions
import Goose.Proofs.ConstructionAcceptedGlobalBranchSequence

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

structure CheckedConditionalBlock (frame : ConstructionSourceFrame) (block : Block)
    (types : List Ty) (typingAfter : Nat) (result : List RootRef × (Nat × Nat)) (rootsAfter : RState) : Prop where
  typing : typeBlock frame.typingFuel frame.typing block frame.typingCounter = .ok (types, typingAfter)
  provenance : rpBlockValue frame.source [] block frame.rootCursor = .ok (result, rootsAfter)
  available : GlobalEffectsAvailable frame.interpretation frame.initialized rootsAfter.eff

theorem checkedValue_conditional_children (frame : ConstructionSourceFrame) (fuel : Nat)
    (condition : Expr) (yes no : Block) (origin : Nat) (ty : Ty) (roots : List RootRef)
    (typingAfter : Nat) (rootsAfter : RState) (fuelAt : frame.typingFuel = fuel + 1)
    (checked : CheckedValue frame (.ifE condition yes no origin) ty roots typingAfter rootsAfter) :
    ∃ conditionTyping conditionRoots conditionCursor yesTypes yesTyping yesResult yesCursor noTypes noTyping noResult,
      CheckedValue (ordinaryOperandFrame frame fuel) condition .bool conditionRoots conditionTyping conditionCursor ∧
      CheckedConditionalBlock { frame with typingFuel := fuel, typingCounter := conditionTyping, rootCursor := conditionCursor }
        yes yesTypes yesTyping yesResult yesCursor ∧
      CheckedConditionalBlock { frame with typingFuel := fuel, typingCounter := yesTyping, rootCursor := yesCursor }
        no noTypes noTyping noResult rootsAfter := by
  have typed := checked.typing
  rw [fuelAt] at typed
  obtain ⟨conditionTyping, yesTypes, yesTyping, noTypes, noTyping, conditionTyped, yesTyped, noTyped⟩ :=
    typeExpr_if_branches fuel frame.typing condition yes no origin frame.typingCounter typingAfter [ty] typed
  obtain ⟨conditionRoots, conditionCursor, yesResult, yesCursor, noResult, conditionRooted, yesRooted, noRooted⟩ :=
    rpExpr_if_branches frame.source condition yes no origin frame.rootCursor rootsAfter roots checked.provenance
  have yesIncluded := rpBlockValue_effectTargetsIncluded noRooted
  have conditionIncluded := EffectTargetsIncluded.trans (rpBlockValue_effectTargetsIncluded yesRooted) yesIncluded
  have conditionAvailable : GlobalEffectsAvailable frame.interpretation frame.initialized conditionCursor.eff := by
    intro target member global instantiates
    exact checked.available target (conditionIncluded member) global instantiates
  have yesAvailable : GlobalEffectsAvailable frame.interpretation frame.initialized yesCursor.eff := by
    intro target member global instantiates
    exact checked.available target (yesIncluded member) global instantiates
  exact ⟨conditionTyping, conditionRoots, conditionCursor, yesTypes, yesTyping, yesResult, yesCursor, noTypes, noTyping, noResult,
    ⟨conditionTyped, conditionRooted, conditionAvailable⟩,
    ⟨yesTyped, yesRooted, yesAvailable⟩, ⟨noTyped, noRooted, checked.available⟩⟩

theorem checkedConditionalBlock_tail (frame : ConstructionSourceFrame) (fuel scope scopeInst : Nat)
    (statements : List Stmt) (tail : Expr) (ty : Ty) (typingAfter : Nat)
    (result : List RootRef × (Nat × Nat)) (rootsAfter : RState)
    (fuelAt : frame.typingFuel = fuel + 1)
    (checked : CheckedConditionalBlock frame ⟨scope, statements, some tail⟩ [ty] typingAfter result rootsAfter) :
    ∃ next typingMiddle rootsMiddle roots,
      let bodyFrame := emptyChildScopeFrame frame scope scopeInst fuel
      let tailFrame := { bodyFrame with
        typing := next
        typingCounter := typingMiddle
        rootCursor := rootsMiddle }
      typeStatements fuel bodyFrame.typing statements bodyFrame.typingCounter = .ok (next, typingMiddle) ∧
      rpStmts bodyFrame.source statements bodyFrame.rootCursor = .ok ((), rootsMiddle) ∧
      GlobalEffectsAvailable bodyFrame.interpretation bodyFrame.initialized rootsMiddle.eff ∧
      CheckedValue tailFrame tail ty roots typingAfter rootsAfter := by
  have typed := checked.typing
  rw [fuelAt] at typed
  obtain ⟨next, typingMiddle, rootsMiddle, roots, statementsTyped, tailTyped, statementsRooted, tailRooted⟩ :=
    globalBranch_blockChecks fuel frame.typing frame.source scope statements tail frame.typingCounter typingAfter [ty]
      frame.rootCursor rootsAfter result typed checked.provenance
  let bodyFrame := emptyChildScopeFrame frame scope scopeInst fuel
  let tailFrame := { bodyFrame with
    typing := next
    typingCounter := typingMiddle
    rootCursor := rootsMiddle }
  have bodyAvailable : GlobalEffectsAvailable bodyFrame.interpretation bodyFrame.initialized rootsMiddle.eff := by
    have included := rpExpr_effectTargetsIncluded tailRooted
    intro target member global instantiates
    apply checked.available target (included member) global
    simpa [bodyFrame, emptyChildScopeFrame, RootInterpretation.enterScope] using instantiates
  have tailAvailable : GlobalEffectsAvailable tailFrame.interpretation tailFrame.initialized rootsAfter.eff := by
    intro target member global instantiates
    apply checked.available target member global
    simpa [tailFrame, bodyFrame, emptyChildScopeFrame, RootInterpretation.enterScope] using instantiates
  exact ⟨next, typingMiddle, rootsMiddle, roots, statementsTyped, statementsRooted, bodyAvailable,
    ⟨tailTyped, tailRooted, tailAvailable⟩⟩

theorem typeExpr_if_nonEscapingBranches (fuel : Nat) (environment : TypingEnv) (condition yes no : Expr) (yesStatements noStatements : List Stmt)
    (yesScope noScope origin before after conditionAfter yesAfter noAfter : Nat) (ty yesTy noTy : Ty)
    (checked : typeExpr (fuel + 1) environment (.ifE condition ⟨yesScope, yesStatements, some yes⟩ ⟨noScope, noStatements, some no⟩ origin) before = .ok ([ty], after))
    (conditionTyped : typeExpr fuel { environment with use := .ordinary, request := .value, resultRequests := [] }
      condition before = .ok ([.bool], conditionAfter))
    (yesTyped : typeBlock fuel environment ⟨yesScope, yesStatements, some yes⟩ conditionAfter = .ok ([yesTy], yesAfter))
    (noTyped : typeBlock fuel environment ⟨noScope, noStatements, some no⟩ yesAfter = .ok ([noTy], noAfter))
    (yesNoEscape : blockEscapes fuel ⟨yesScope, yesStatements, some yes⟩ = false)
    (noNoEscape : blockEscapes fuel ⟨noScope, noStatements, some no⟩ = false) :
    yesTy = ty ∧ noTy = ty := by
  simp only [typeExpr, bind, StateT.bind] at checked
  change (Except.bind (typeExpr fuel
    { environment with use := .ordinary, request := .value, resultRequests := [] } condition before) _) = _ at checked
  simp only [conditionTyped, Except.bind] at checked
  change (Except.bind (typeBlock fuel environment ⟨yesScope, yesStatements, some yes⟩ conditionAfter) _) = _ at checked
  simp only [yesTyped, Except.bind] at checked
  change (Except.bind (typeBlock fuel environment ⟨noScope, noStatements, some no⟩ yesAfter) _) = _ at checked
  simp only [noTyped, Except.bind, yesNoEscape, noNoEscape, Bool.false_and] at checked
  unfold_typing_require
  by_cases same : yesTy = noTy
  · subst noTy
    simp [bind, StateT.bind, pure, StateT.pure, Except.pure, Except.bind] at checked
    exact ⟨checked.1, checked.1⟩
  · simp [same, bind, StateT.bind, pure, StateT.pure, Except.pure, Except.bind] at checked
    change Except.error _ = Except.ok _ at checked
    cases checked

theorem typeExpr_if_nonEscaping_result (fuel : Nat) (environment : TypingEnv) (condition : Expr) (yes no : Block)
    (origin before after conditionAfter yesAfter noAfter : Nat) (types yesTypes noTypes : List Ty)
    (checked : typeExpr (fuel + 1) environment (.ifE condition yes no origin) before = .ok (types, after))
    (conditionTyped : typeExpr fuel { environment with use := .ordinary, request := .value, resultRequests := [] }
      condition before = .ok ([.bool], conditionAfter))
    (yesTyped : typeBlock fuel environment yes conditionAfter = .ok (yesTypes, yesAfter))
    (noTyped : typeBlock fuel environment no yesAfter = .ok (noTypes, noAfter))
    (yesNoEscape : blockEscapes fuel yes = false) (noNoEscape : blockEscapes fuel no = false) :
    types = yesTypes := by
  simp only [typeExpr, bind, StateT.bind] at checked
  change (Except.bind (typeExpr fuel
    { environment with use := .ordinary, request := .value, resultRequests := [] } condition before) _) = _ at checked
  simp only [conditionTyped, Except.bind] at checked
  change (Except.bind (typeBlock fuel environment yes conditionAfter) _) = _ at checked
  simp only [yesTyped, Except.bind] at checked
  change (Except.bind (typeBlock fuel environment no yesAfter) _) = _ at checked
  simp only [noTyped, Except.bind, yesNoEscape, noNoEscape, Bool.false_and] at checked
  unfold_typing_require
  by_cases same : yesTypes = noTypes
  · subst noTypes
    simp [bind, StateT.bind, pure, StateT.pure, Except.pure, Except.bind] at checked
    exact checked.1.symm
  · simp [same, bind, StateT.bind, pure, StateT.pure, Except.pure, Except.bind] at checked
    change Except.error _ = Except.ok _ at checked
    cases checked

theorem typeExpr_if_nonEscaping_cursor (fuel : Nat) (environment : TypingEnv) (condition : Expr) (yes no : Block)
    (origin before after conditionAfter yesAfter noAfter : Nat) (types yesTypes noTypes : List Ty)
    (checked : typeExpr (fuel + 1) environment (.ifE condition yes no origin) before = .ok (types, after))
    (conditionTyped : typeExpr fuel { environment with use := .ordinary, request := .value, resultRequests := [] }
      condition before = .ok ([.bool], conditionAfter))
    (yesTyped : typeBlock fuel environment yes conditionAfter = .ok (yesTypes, yesAfter))
    (noTyped : typeBlock fuel environment no yesAfter = .ok (noTypes, noAfter))
    (yesNoEscape : blockEscapes fuel yes = false) (noNoEscape : blockEscapes fuel no = false) :
    types = yesTypes ∧ after = noAfter := by
  simp only [typeExpr, bind, StateT.bind] at checked
  change (Except.bind (typeExpr fuel
    { environment with use := .ordinary, request := .value, resultRequests := [] } condition before) _) = _ at checked
  simp only [conditionTyped, Except.bind] at checked
  change (Except.bind (typeBlock fuel environment yes conditionAfter) _) = _ at checked
  simp only [yesTyped, Except.bind] at checked
  change (Except.bind (typeBlock fuel environment no yesAfter) _) = _ at checked
  simp only [noTyped, Except.bind, yesNoEscape, noNoEscape, Bool.false_and] at checked
  unfold_typing_require
  by_cases same : yesTypes = noTypes
  · subst noTypes
    simp [bind, StateT.bind, pure, StateT.pure, Except.pure, Except.bind] at checked
    exact ⟨checked.1.symm, checked.2.symm⟩
  · simp [same, bind, StateT.bind, pure, StateT.pure, Except.pure, Except.bind] at checked
    change Except.error _ = Except.ok _ at checked
    cases checked

#print axioms typeExpr_if_nonEscaping_cursor
#print axioms typeExpr_if_nonEscaping_result
#print axioms typeExpr_if_nonEscapingBranches
#print axioms checkedConditionalBlock_tail
#print axioms checkedValue_conditional_children
end Goose.Proofs.ConstructionAcceptedExecution
