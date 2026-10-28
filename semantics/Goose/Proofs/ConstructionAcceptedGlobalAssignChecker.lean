import Goose.Proofs.ConstructionAcceptedGlobalAssignRuntime
import Goose.Proofs.ConstructionAcceptedScalarAssignCursor

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst)
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem checkedValue_scalarAssign_prefix_operand (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (state : ExecutionState) (types : RootTypes) (place : Place)
    (expression : Expr) (origin : Goose.Core.OriginId) (form : AcceptedBinaryExpression expression)
    (next : TypingEnv) (typingAfter : Nat) (rootsAfter : RState)
    (source : AcceptedFrame config accepted frame state types)
    (globalLimit : frame.typing.globalLimit ≤ frame.initialized)
    (noParameters : ∀ parameter global, ¬ frame.interpretation.parameters parameter (.global global))
    (direct : (∃ id, place = .var id) ∨ ∃ id, place = .global id)
    (typed : typeStatement (fuel + 1) frame.typing (.assign place expression origin) frame.typingCounter = .ok (next, typingAfter))
    (rooted : rpStmt frame.source (.assign place expression origin) frame.rootCursor = .ok ((), rootsAfter)) :
    ∃ ty roots expressionTypingAfter expressionRootsAfter,
      CheckedValue (scalarAssignmentOperandFrame frame fuel) expression ty roots expressionTypingAfter expressionRootsAfter ∧
      AcceptedFrame config accepted (scalarAssignmentOperandFrame frame fuel) state types ∧
      next = frame.typing ∧ typingAfter = expressionTypingAfter ∧
      ∃ writable binding, typePlace fuel frame.typing place frame.typingCounter =
        .ok ((ty, writable, binding), frame.typingCounter) ∧ writable = true := by
  obtain ⟨ty, writable, binding, middle, expressionAfter, placeTyped, expressionTyped, flat, mutable, sameNext, sameAfter⟩ :=
    typeStatement_scalarAssign fuel frame.typing next place expression origin frame.typingCounter typingAfter form typed
  have sameMiddle : middle = frame.typingCounter := by
    rcases direct with ⟨id, same⟩ | ⟨id, same⟩
    · subst place
      obtain ⟨descriptor, visible, declared, sameTy, sameMutable, sameMiddle⟩ :=
        typePlace_local_scalarFacts fuel frame.typing id frame.typingCounter middle ty writable binding placeTyped
      exact sameMiddle
    · subst place
      obtain ⟨descriptor, inside, declared, sameTy, sameMutable, sameMiddle⟩ :=
        typePlace_global_scalarFacts fuel frame.typing id frame.typingCounter middle ty writable binding placeTyped
      exact sameMiddle
  subst middle
  obtain ⟨roots, expressionRootsAfter, expressionRooted⟩ := rpStmt_directAssign_operand frame.source place expression origin
    frame.rootCursor rootsAfter direct rooted
  have initial := (ordinaryOperandFrame_accepted accepted frame fuel state types source).withRootCursor
    { frame.rootCursor with eff := {} } rfl
  have bound : GlobalEffectTargetsBounded (scalarAssignmentOperandFrame frame fuel).rootCursor.eff frame.initialized := by
    simp [scalarAssignmentOperandFrame, GlobalEffectTargetsBounded, Eff.accessTargets]
  have effects : GlobalEffectTargetsBounded expressionRootsAfter.eff frame.initialized := by
    exact recursiveScalar_effects_bounded form fuel (scalarAssignmentOperandFrame frame fuel).typing
      (scalarAssignmentOperandFrame frame fuel).source frame.initialized frame.typingCounter expressionAfter
      (scalarAssignmentOperandFrame frame fuel).rootCursor expressionRootsAfter [ty] roots globalLimit
      bound expressionTyped expressionRooted
  have available : GlobalEffectsAvailable frame.interpretation frame.initialized expressionRootsAfter.eff := by
    intro target member global instantiated
    cases target with
    | global other =>
      change global = other at instantiated
      subst global
      exact effects other member
    | param parameter => exact (noParameters parameter global instantiated.1).elim
  exact ⟨ty, roots, expressionAfter, expressionRootsAfter, ⟨expressionTyped, expressionRooted, available⟩,
    initial, sameNext, sameAfter, writable, binding, placeTyped, mutable⟩

theorem execStmt_checkedGlobalAssign_prefix (fuel checkFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (id : Nat) (expression : Expr) (origin : Goose.Core.OriginId) (form : AcceptedBinaryExpression expression)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types)
    (globalLimit : frame.typing.globalLimit ≤ frame.initialized)
    (noParameters : ∀ parameter global, ¬ frame.interpretation.parameters parameter (.global global))
    (next : TypingEnv) (typingAfter : Nat) (rootsAfter : RState)
    (typed : typeStatement (checkFuel + 1) frame.typing (.assign (.global id) expression origin) frame.typingCounter = .ok (next, typingAfter))
    (rooted : rpStmt frame.source (.assign (.global id) expression origin) frame.rootCursor = .ok ((), rootsAfter))
    (scalar : ∀ descriptor, config.module.globals[id]? = some descriptor →
      (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool) :
    let outcome := execStmt fuel config frame.interpretation.environment (.assign (.global id) expression origin) before
    AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) ambient types live regions pending ∧
      AcceptedFrame config accepted frame (Goose.Proofs.Exit.stepState outcome) types ∧
      (match outcome with | .ok flow _ => flow = .normal .unit | .stop .. => True | .escape .. | .jump .. => False) := by
  obtain ⟨ty, roots, operandTypingAfter, operandRootsAfter, checked, operandSource, sameNext, sameAfter,
      writable, binding, placeTyped, mutable⟩ :=
    checkedValue_scalarAssign_prefix_operand checkFuel config accepted frame before types (.global id) expression origin form
      next typingAfter rootsAfter source globalLimit noParameters (Or.inr ⟨id, rfl⟩) typed rooted
  obtain ⟨descriptor, inside, declared, sameTy, sameMutable, sameCounter⟩ :=
    typePlace_global_scalarFacts checkFuel frame.typing id frame.typingCounter frame.typingCounter ty writable binding placeTyped
  subst ty
  have moduleDeclared : config.module.globals[id]? = some descriptor := by
    rw [← source.compatible.module]; exact declared
  have available : id < frame.initialized := by omega
  let cleared := { frame with rootCursor := { frame.rootCursor with eff := {} } }
  have clearedSource : AcceptedFrame config accepted cleared before types := source.withRootCursor _ rfl
  have checked' : CheckedValue (ordinaryOperandFrame cleared checkFuel) expression descriptor.ty roots operandTypingAfter operandRootsAfter := checked
  have result := execStmt_checkedScalarAssignGlobal_prefix_complete fuel checkFuel config accepted cleared before ambient types live regions pending
    id expression origin descriptor form world clearedSource available moduleDeclared (scalar descriptor moduleDeclared)
    roots operandTypingAfter operandRootsAfter checked'
  obtain ⟨nextWorld, nextSource, flow⟩ := result
  have originalSource : AcceptedFrame config accepted frame
      (Goose.Proofs.Exit.stepState (execStmt fuel config frame.interpretation.environment (.assign (.global id) expression origin) before)) types := by
    simpa only [cleared] using nextSource.withRootCursor frame.rootCursor rfl
  exact ⟨nextWorld, originalSource, flow⟩

theorem checkedGlobalAssign_prefix_advance (checkFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (before : ExecutionState) (types : RootTypes)
    (id : Nat) (expression : Expr) (origin : Goose.Core.OriginId) (form : AcceptedBinaryExpression expression)
    (source : AcceptedFrame config accepted frame before types)
    (globalLimit : frame.typing.globalLimit ≤ frame.initialized)
    (noParameters : ∀ parameter global, ¬ frame.interpretation.parameters parameter (.global global))
    (bounded : GlobalEffectTargetsBounded frame.rootCursor.eff frame.initialized)
    (next : TypingEnv) (typingAfter : Nat) (rootsAfter : RState)
    (typed : typeStatement (checkFuel + 1) frame.typing (.assign (.global id) expression origin) frame.typingCounter = .ok (next, typingAfter))
    (rooted : rpStmt frame.source (.assign (.global id) expression origin) frame.rootCursor = .ok ((), rootsAfter)) :
    next = frame.typing ∧ typingAfter = frame.typingCounter ∧ rootsAfter.nextVar = frame.rootCursor.nextVar ∧
      GlobalEffectTargetsBounded rootsAfter.eff frame.initialized := by
  obtain ⟨ty, roots, operandTypingAfter, operandRootsAfter, checked, operandSource, sameNext, sameAfter,
      writable, binding, placeTyped, mutable⟩ :=
    checkedValue_scalarAssign_prefix_operand checkFuel config accepted frame before types (.global id) expression origin form
      next typingAfter rootsAfter source globalLimit noParameters (Or.inr ⟨id, rfl⟩) typed rooted
  have cursor := checked_binary_recursive_cursor form (scalarAssignmentOperandFrame frame checkFuel) ty roots
    operandTypingAfter operandRootsAfter checked
  have nextVar := rpStmt_directAssign_cursor frame.source (.global id) expression origin frame.rootCursor rootsAfter operandRootsAfter
    roots (Or.inr ⟨id, rfl⟩) checked.provenance rooted
  have sameRoot : rootsAfter.nextVar = frame.rootCursor.nextVar := by
    rw [nextVar]
    simpa [scalarAssignmentOperandFrame, ordinaryOperandFrame] using cursor.2
  have operandBound : GlobalEffectTargetsBounded operandRootsAfter.eff frame.initialized := by
    apply recursiveScalar_effects_bounded form checkFuel (scalarAssignmentOperandFrame frame checkFuel).typing
      (scalarAssignmentOperandFrame frame checkFuel).source frame.initialized frame.typingCounter operandTypingAfter
      (scalarAssignmentOperandFrame frame checkFuel).rootCursor operandRootsAfter [ty] roots globalLimit
    · simp [scalarAssignmentOperandFrame, GlobalEffectTargetsBounded, Eff.accessTargets]
    · exact checked.typing
    · exact checked.provenance
  have targetBound : ∀ target, .global target ∈ rootsTargets (scalarAssignmentRoots (.global id)) → target < frame.initialized := by
    intro target member
    have equal : target = id := by simpa [scalarAssignmentRoots, rootsTargets, rootTarget] using member
    subst target
    obtain ⟨descriptor, inside, declared, sameTy, sameMutable, sameCounter⟩ :=
      typePlace_global_scalarFacts checkFuel frame.typing id frame.typingCounter frame.typingCounter ty writable binding placeTyped
    omega
  have finalBound := rpStmt_directAssign_effects_bounded frame.source (.global id) expression origin frame.rootCursor rootsAfter
    operandRootsAfter roots frame.initialized (Or.inr ⟨id, rfl⟩) checked.provenance rooted bounded operandBound targetBound
  have sameCounter : typingAfter = frame.typingCounter := by
    rw [sameAfter]
    simpa [scalarAssignmentOperandFrame, ordinaryOperandFrame] using cursor.1
  exact ⟨sameNext, sameCounter, sameRoot, finalBound⟩

#print axioms checkedGlobalAssign_prefix_advance
#print axioms execStmt_checkedGlobalAssign_prefix
#print axioms checkedValue_scalarAssign_prefix_operand
end Goose.Proofs.ConstructionAcceptedExecution
