import Goose.Proofs.ConstructionAcceptedScalarAssignCursors
import Goose.Proofs.ConstructionByteReplay

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

theorem SourcePosition.singleScalarGlobal_replay {config : EvalConfig} (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (before : ExecutionState) (types : RootTypes)
    (id : Nat) (expression : Expr) (origin : Goose.Core.OriginId) (checkFuel : Nat)
    (form : AcceptedBinaryExpression expression) (source : AcceptedFrame config accepted frame before types)
    (initialized : frame.initialized = config.module.globals.size)
    (bounded : GlobalEffectTargetsBounded frame.rootCursor.eff config.module.globals.size)
    (position : SourcePosition accepted frame (.statements [.assign (.global id) expression origin]))
    (nesting : frame.typingFuel = checkFuel + 2) :
    ∃ rootsAfter : RState,
      rootsAfter.nextVar = frame.rootCursor.nextVar ∧ GlobalEffectTargetsBounded rootsAfter.eff config.module.globals.size ∧
      typeStatements frame.typingFuel frame.typing [.assign (.global id) expression origin] frame.typingCounter = .ok (frame.typing, frame.typingCounter) ∧
      rpStmts frame.source [.assign (.global id) expression origin] frame.rootCursor = .ok ((), rootsAfter) := by
  have headPosition := position.statements_head accepted frame (.assign (.global id) expression origin) [] (checkFuel + 1) nesting
  obtain ⟨headTyping, headCounter, headRoots, headTyped, headRooted⟩ := headPosition.checked accepted _ _
  have cursors := scalarAssign_statement_cursors checkFuel config accepted { frame with typingFuel := checkFuel + 1 } before types
    (.global id) expression origin form headTyping headCounter headRoots (source.withTypingFuel (checkFuel + 1)) initialized
    (Or.inr ⟨id, rfl⟩) headTyped headRooted
  have sameRoot : headRoots.nextVar = frame.rootCursor.nextVar := cursors.2.2
  obtain ⟨ty, operandRoots, operandTypingAfter, operandRootsAfter, checked, operandSource, sameNext, sameAfter,
      writable, binding, placeTyped, mutable⟩ := checkedValue_scalarAssign_operand checkFuel config accepted frame before types
        (.global id) expression origin form headTyping headCounter headRoots source initialized (Or.inr ⟨id, rfl⟩) headTyped headRooted
  have operandBounded : GlobalEffectTargetsBounded operandRootsAfter.eff config.module.globals.size := by
    exact (globalEffectsAvailable_iff_bounded frame.interpretation operandRootsAfter.eff).1
      (by simpa [scalarAssignmentOperandFrame, ordinaryOperandFrame, initialized, source.compatible.globalCount] using checked.available)
      |> fun h => by simpa [source.compatible.globalCount] using h
  have targetBounded : ∀ targetId, .global targetId ∈ rootsTargets (scalarAssignmentRoots (.global id)) → targetId < config.module.globals.size := by
    intro targetId member
    have equal : targetId = id := by simpa [scalarAssignmentRoots, rootsTargets, rootTarget] using member
    subst targetId
    obtain ⟨descriptor, inside, declared, sameTy, sameMutable, sameCounter⟩ :=
      typePlace_global_scalarFacts checkFuel frame.typing id frame.typingCounter frame.typingCounter ty writable binding placeTyped
    exact Nat.lt_of_lt_of_le inside source.compatible.globals
  have finalBounded := rpStmt_directAssign_effects_bounded frame.source (.global id) expression origin frame.rootCursor headRoots
    operandRootsAfter operandRoots config.module.globals.size (Or.inr ⟨id, rfl⟩) checked.provenance headRooted bounded operandBounded targetBounded
  let next := { frame with typingFuel := checkFuel + 1, rootCursor := headRoots }
  have headTyped' : typeStatement (checkFuel + 1) frame.typing (.assign (.global id) expression origin) frame.typingCounter =
      .ok (next.typing, next.typingCounter) := by simpa [next, cursors.1, cursors.2.1] using headTyped
  have replay := statementReplay_cons (checkFuel + 1) frame next next (.assign (.global id) expression origin) []
    headTyped' headRooted rfl (by simp [next, typeStatements, pure, StateT.pure, Except.pure])
    (by simp [next, rpStmts, pure, StateT.pure, Except.pure])
  refine ⟨headRoots, sameRoot, finalBounded, ?_, ?_⟩
  · simpa [next, nesting, Nat.add_assoc] using replay.1
  · simpa [next] using replay.2

#print axioms SourcePosition.singleScalarGlobal_replay
end Goose.Proofs.ConstructionAcceptedExecution
