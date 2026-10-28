import Goose.Proofs.ConstructionAcceptedConditionalBranches
import Goose.Proofs.ConstructionAcceptedEntryScope

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation

def scalarGlobalBranchFrame (config : EvalConfig) (id act : Nat) (names : Array (List RootRef))
    (scope scopeInst : Nat) (cursor : RState) : ConstructionSourceFrame :=
  let frame := scalarGlobalInitializerFrame config id act names
  { frame with
    typing := { frame.typing with scope := scope }
    source := { frame.source with scopes := [scope] }
    interpretation := frame.interpretation.enterScope scope scopeInst
    typingFuel := 4094
    rootCursor := cursor }

theorem accepted_scalarGlobalBranch_frame_from (config : EvalConfig) (accepted : AcceptedModule config)
    (id : Nat) (before : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (names : Array (List RootRef)) (clear : FutureGlobalsClear config id before)
    (scope : Nat) (cursor : RState) (cursorVars : cursor.nextVar = 0)
    (activeWorld : AcceptedWorld config id { before with nextAct := before.nextAct + 1 } ambient types live [] [])
    (source : AcceptedFrame config accepted (scalarGlobalInitializerFrame config id before.nextAct names)
      { before with nextAct := before.nextAct + 1 } types) :
    let activated := { before with nextAct := before.nextAct + 1 }
    let after := { activated with nextScope := activated.nextScope + 1 }
    let frame := scalarGlobalBranchFrame config id before.nextAct names scope activated.nextScope cursor
    AcceptedWorld config id after ambient types live [] [] ∧ AcceptedFrame config accepted frame after types := by
  let base := scalarGlobalInitializerFrame config id before.nextAct names
  let activated := { before with nextAct := before.nextAct + 1 }
  let after := { activated with nextScope := activated.nextScope + 1 }
  let frame := scalarGlobalBranchFrame config id before.nextAct names scope activated.nextScope cursor
  have scopeWorld := (freshScope_acceptedWorld config id activated ambient types live activeWorld).2
  have compatible : SourceFrameCompatible accepted frame := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact source.compatible.globals
    · exact source.compatible.initialized
    · simp [frame, scalarGlobalBranchFrame, scalarGlobalInitializerFrame, cursorVars]
    · simp [frame, scalarGlobalBranchFrame, scalarGlobalInitializerFrame]
    · simp [frame, scalarGlobalBranchFrame, scalarGlobalInitializerFrame]
    · simp [frame, scalarGlobalBranchFrame, scalarGlobalInitializerFrame, initializerSource]
    · simp [frame, scalarGlobalBranchFrame, scalarGlobalInitializerFrame, initializerSource]
    · exact source.compatible.origin
  have frontier : RootFrontier frame.interpretation after.nextAct := by
    exact rootFrontier_enterScope base.interpretation scope activated.nextScope activated.nextAct source.frontier
  have aliases : AliasComplete frame.interpretation frame.source.aliases := by
    exact aliasComplete_enterScope base.interpretation base.source.aliases scope activated.nextScope activated.nextAct source.frontier source.aliases
  have frameOk : AcceptedFrame config accepted frame after types := by
    refine ⟨compatible, frontier, ?_, ?_, aliases, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [frame, scalarGlobalBranchFrame, scalarGlobalInitializerFrame, RootInterpretation.enterScope, EntryInterpretation, after]
    · simp [frame, scalarGlobalBranchFrame, scalarGlobalInitializerFrame, initializerSource]
    · simp [frame, scalarGlobalBranchFrame, scalarGlobalInitializerFrame, LocalRepresentations]
    · simp [frame, scalarGlobalBranchFrame, scalarGlobalInitializerFrame]
    · intro other condition root resolved
      simp [frame, scalarGlobalBranchFrame, scalarGlobalInitializerFrame, RootInterpretation.enterScope, EntryInterpretation, rootOf, fault, EvalM.stop] at resolved
    · intro other condition root resolved
      simp [frame, scalarGlobalBranchFrame, scalarGlobalInitializerFrame, RootInterpretation.enterScope, EntryInterpretation, rootOf, fault, EvalM.stop] at resolved
    · intro global future within
      exact clear global future within
    · simp [frame, scalarGlobalBranchFrame, scalarGlobalInitializerFrame, LocalRootCorrespondence]
    · simp [frame, scalarGlobalBranchFrame, scalarGlobalInitializerFrame, ContentRootCorrespondence]
  exact ⟨scopeWorld, frameOk⟩

theorem accepted_globalConditional_scoped_tails (config : EvalConfig) (accepted : AcceptedModule config)
    (id : Nat) (descriptor : Global) (before : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (world : AcceptedWorld config id before ambient types live [] []) (clear : FutureGlobalsClear config id before)
    (present : config.module.globals[id]? = some descriptor) (condition yes no : Expr) (yesScope noScope origin : Nat)
    (shape : descriptor.init = .ifE condition ⟨yesScope, [], some yes⟩ ⟨noScope, [], some no⟩ origin)
    (conditionForm : AcceptedBinaryExpression condition) (yesForm : AcceptedBinaryExpression yes) (noForm : AcceptedBinaryExpression no) :
    ∃ names yesTy noTy yesRoots noRoots yesAfter noAfter conditionCursor yesCursor,
      let activated := { before with nextAct := before.nextAct + 1 }
      let scopeState := { activated with nextScope := activated.nextScope + 1 }
      let yesFrame := scalarGlobalBranchFrame config id before.nextAct names yesScope activated.nextScope conditionCursor
      let noFrame := scalarGlobalBranchFrame config id before.nextAct names noScope activated.nextScope yesCursor
      AcceptedWorld config id scopeState ambient types live [] [] ∧
      AcceptedFrame config accepted yesFrame scopeState types ∧ AcceptedFrame config accepted noFrame scopeState types ∧
      CheckedValue yesFrame yes yesTy yesRoots 0 yesAfter ∧ CheckedValue noFrame no noTy noRoots 0 noAfter := by
  obtain ⟨names, conditionTyping, yesTyping, noTyping, yesTy, noTy, conditionRoots, conditionCursor,
    yesRoots, yesCursor, noRoots, noCursor, activeWorld, source, yesTyped, noTyped, conditionRooted, yesRooted, noRooted,
    conditionBound, yesBound, noBound, conditionTypingZero, yesTypingZero, conditionCursorZero, yesCursorZero⟩ :=
    accepted_globalConditional_tail_checks config accepted id descriptor before ambient types live world clear present
      condition yes no yesScope noScope origin shape conditionForm yesForm noForm
  let activated := { before with nextAct := before.nextAct + 1 }
  let scopeState := { activated with nextScope := activated.nextScope + 1 }
  let yesFrame := scalarGlobalBranchFrame config id before.nextAct names yesScope activated.nextScope conditionCursor
  let noFrame := scalarGlobalBranchFrame config id before.nextAct names noScope activated.nextScope yesCursor
  obtain ⟨scopeWorld, yesSource⟩ := accepted_scalarGlobalBranch_frame_from config accepted id before ambient types live
    names clear yesScope conditionCursor conditionCursorZero activeWorld source
  obtain ⟨_, noSource⟩ := accepted_scalarGlobalBranch_frame_from config accepted id before ambient types live
    names clear noScope yesCursor yesCursorZero activeWorld source
  have yesAvailable : GlobalEffectsAvailable yesFrame.interpretation id yesCursor.eff := by
    intro target member global instantiated
    cases target with
    | global other =>
      change global = other at instantiated
      subst global
      exact yesBound other member
    | param parameter => exact instantiated.1.elim
  have noAvailable : GlobalEffectsAvailable noFrame.interpretation id noCursor.eff := by
    intro target member global instantiated
    cases target with
    | global other =>
      change global = other at instantiated
      subst global
      exact noBound other member
    | param parameter => exact instantiated.1.elim
  have yesChecked : CheckedValue yesFrame yes yesTy yesRoots 0 yesCursor := by
    refine ⟨?_, ?_, yesAvailable⟩
    · simpa [yesFrame, scalarGlobalBranchFrame, scalarGlobalInitializerFrame, conditionTypingZero, yesTypingZero] using yesTyped
    · simpa [yesFrame, scalarGlobalBranchFrame, scalarGlobalInitializerFrame, initializerSource, StateT.run] using yesRooted
  have noTypingZero : noTyping = 0 := by
    let noCheckedFrame := { noFrame with typingCounter := yesTyping }
    have noChecked : CheckedValue noCheckedFrame no noTy noRoots noTyping noCursor := by
      refine ⟨?_, ?_, noAvailable⟩
      · simpa [noCheckedFrame, noFrame, scalarGlobalBranchFrame, scalarGlobalInitializerFrame] using noTyped
      · simpa [noCheckedFrame, noFrame, scalarGlobalBranchFrame, scalarGlobalInitializerFrame, initializerSource, StateT.run] using noRooted
    have cursorFacts := checked_binary_recursive_cursor noForm noCheckedFrame noTy noRoots noTyping noCursor noChecked
    simpa [noCheckedFrame, yesTypingZero] using cursorFacts.1
  have noChecked : CheckedValue noFrame no noTy noRoots 0 noCursor := by
    refine ⟨?_, ?_, noAvailable⟩
    · simpa [noFrame, scalarGlobalBranchFrame, scalarGlobalInitializerFrame, yesTypingZero, noTypingZero] using noTyped
    · simpa [noFrame, scalarGlobalBranchFrame, scalarGlobalInitializerFrame, initializerSource, StateT.run] using noRooted
  exact ⟨names, yesTy, noTy, yesRoots, noRoots, yesCursor, noCursor, conditionCursor, yesCursor,
    scopeWorld, yesSource, noSource, yesChecked, noChecked⟩

theorem accepted_globalConditional_tails_evaluate (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (id : Nat) (descriptor : Global) (before : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (world : AcceptedWorld config id before ambient types live [] []) (clear : FutureGlobalsClear config id before)
    (present : config.module.globals[id]? = some descriptor) (condition yes no : Expr) (yesScope noScope origin : Nat)
    (shape : descriptor.init = .ifE condition ⟨yesScope, [], some yes⟩ ⟨noScope, [], some no⟩ origin)
    (conditionForm : AcceptedBinaryExpression condition) (yesForm : AcceptedBinaryExpression yes) (noForm : AcceptedBinaryExpression no) :
    ∃ names yesTy noTy yesRoots noRoots conditionCursor yesCursor,
      let activated := { before with nextAct := before.nextAct + 1 }
      let scopeState := { activated with nextScope := activated.nextScope + 1 }
      let yesFrame := scalarGlobalBranchFrame config id before.nextAct names yesScope activated.nextScope conditionCursor
      let noFrame := scalarGlobalBranchFrame config id before.nextAct names noScope activated.nextScope yesCursor
      let yesRun := evalValue fuel config yesFrame.interpretation.environment yes scopeState
      let noRun := evalValue fuel config noFrame.interpretation.environment no scopeState
      Goose.Proofs.Exit.stepState yesRun = scopeState ∧ Goose.Proofs.Exit.stepState noRun = scopeState ∧
      (∀ value after, yesRun = .ok value after → AcceptedValue config.layout types yesFrame.interpretation after yesTy yesRoots value) ∧
      (∀ value after, noRun = .ok value after → AcceptedValue config.layout types noFrame.interpretation after noTy noRoots value) ∧
      AcceptedWorld config id scopeState ambient types live [] [] := by
  obtain ⟨names, yesTy, noTy, yesRoots, noRoots, yesAfter, noAfter, conditionCursor, yesCursor,
    scopeWorld, yesSource, noSource, yesChecked, noChecked⟩ :=
    accepted_globalConditional_scoped_tails config accepted id descriptor before ambient types live world clear present
      condition yes no yesScope noScope origin shape conditionForm yesForm noForm
  let activated := { before with nextAct := before.nextAct + 1 }
  let scopeState := { activated with nextScope := activated.nextScope + 1 }
  let yesFrame := scalarGlobalBranchFrame config id before.nextAct names yesScope activated.nextScope conditionCursor
  let noFrame := scalarGlobalBranchFrame config id before.nextAct names noScope activated.nextScope yesCursor
  have yesRun := evalValue_checked_binary_recursive yesForm fuel config accepted yesFrame scopeState ambient types live [] []
    scopeWorld yesSource yesTy yesRoots 0 yesAfter yesChecked
  have noRun := evalValue_checked_binary_recursive noForm fuel config accepted noFrame scopeState ambient types live [] []
    scopeWorld noSource noTy noRoots 0 noAfter noChecked
  exact ⟨names, yesTy, noTy, yesRoots, noRoots, conditionCursor, yesCursor,
    yesRun.1, noRun.1, yesRun.2.1, noRun.2.1, scopeWorld⟩

#print axioms accepted_globalConditional_tails_evaluate
#print axioms accepted_globalConditional_scoped_tails
#print axioms accepted_scalarGlobalBranch_frame_from
end Goose.Proofs.ConstructionAcceptedExecution
