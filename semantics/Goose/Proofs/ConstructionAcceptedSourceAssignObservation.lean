import Goose.Proofs.ConstructionAcceptedScalarAssignObservation
import Goose.Proofs.ConstructionAcceptedScalarAssignSource

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence

def ScalarAssignmentObservation (before : ExecutionState) (root : Goose.Core.RootInst) (step : ExecutionStep Flow) : Prop :=
  let after := Goose.Proofs.Exit.stepState step
  after.nextAct = before.nextAct ∧ after.nextScope = before.nextScope ∧
    (∀ other, other ≠ root → after.objects.lookup other = before.objects.lookup other ∧
      after.objectOrdinals.lookup other = before.objectOrdinals.lookup other) ∧
    match step with
    | .ok _ _ => ∃ value, after.objects.lookup root = some value ∧
        ((∃ intTy number, value = .int intTy number) ∨ ∃ boolean, value = .bool boolean)
    | .stop .. => True
    | _ => False

theorem execStmt_sourceScalarAssignGlobal_observation (fuel checkFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (id : Nat) (expression : Expr) (origin : Goose.Core.OriginId) (form : AcceptedBinaryExpression expression)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types) (initialized : frame.initialized = config.module.globals.size)
    (position : SourcePosition accepted frame (.statement (.assign (.global id) expression origin)))
    (nesting : frame.typingFuel = checkFuel + 1)
    (scalar : ∀ descriptor, config.module.globals[id]? = some descriptor →
      (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool) :
    ScalarAssignmentObservation before (.global id)
      (execStmt fuel config frame.interpretation.environment (.assign (.global id) expression origin) before) := by
  obtain ⟨next, typingAfter, rootsAfter, typed, rooted⟩ := position.checked accepted frame _
  rw [nesting] at typed
  obtain ⟨ty, roots, operandTypingAfter, operandRootsAfter, checked, operandSource, sameNext, sameAfter,
      writable, binding, placeTyped, mutable⟩ := checkedValue_scalarAssign_operand checkFuel config accepted frame before types (.global id) expression origin form
        next typingAfter rootsAfter source initialized (Or.inr ⟨id, rfl⟩) typed rooted
  obtain ⟨descriptor, inside, declared, sameTy, sameMutable, sameCounter⟩ :=
    typePlace_global_scalarFacts checkFuel frame.typing id frame.typingCounter frame.typingCounter ty writable binding placeTyped
  subst ty
  have moduleDeclared : config.module.globals[id]? = some descriptor := by rw [← source.compatible.module]; exact declared
  have available : id < frame.initialized := by rw [initialized]; exact (Array.getElem?_eq_some_iff.mp moduleDeclared).1
  obtain ⟨other, old, otherDeclared, found, represented⟩ := world.globals.2 id available
  let cleared := { frame with rootCursor := { frame.rootCursor with eff := {} } }
  have clearedSource : AcceptedFrame config accepted cleared before types := source.withRootCursor _ rfl
  have checked' : CheckedValue (ordinaryOperandFrame cleared checkFuel) expression descriptor.ty roots operandTypingAfter operandRootsAfter := checked
  have resolved : ∀ runtimeFuel, evalPlace (runtimeFuel + 1) config cleared.interpretation.environment (.global id) before = .ok ⟨.global id, []⟩ before := by
    intro runtimeFuel; simp [evalPlace, pure]
  have result := execStmt_checkedScalarAssign_observation fuel checkFuel config accepted cleared before ambient types live regions pending
    (.global id) expression origin (.global id) descriptor.ty old form world clearedSource resolved found (scalar descriptor moduleDeclared)
    roots operandTypingAfter operandRootsAfter checked'
  cases step : execStmt fuel config frame.interpretation.environment (.assign (.global id) expression origin) before <;>
    simpa only [cleared, ScalarAssignmentObservation, step] using result

theorem execStmt_sourceScalarAssignLocal_observation (fuel checkFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (id : Nat) (expression : Expr) (origin : Goose.Core.OriginId) (form : AcceptedBinaryExpression expression)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types) (initialized : frame.initialized = config.module.globals.size)
    (position : SourcePosition accepted frame (.statement (.assign (.var id) expression origin)))
    (nesting : frame.typingFuel = checkFuel + 1)
    (scalar : ∀ descriptor, frame.typing.variables[id]? = some descriptor →
      (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool) :
    ∃ scope, ScalarAssignmentObservation before (.local frame.interpretation.environment.act scope id)
      (execStmt fuel config frame.interpretation.environment (.assign (.var id) expression origin) before) := by
  obtain ⟨next, typingAfter, rootsAfter, typed, rooted⟩ := position.checked accepted frame _
  rw [nesting] at typed
  obtain ⟨ty, roots, operandTypingAfter, operandRootsAfter, checked, operandSource, sameNext, sameAfter,
      writable, binding, placeTyped, mutable⟩ := checkedValue_scalarAssign_operand checkFuel config accepted frame before types (.var id) expression origin form
        next typingAfter rootsAfter source initialized (Or.inl ⟨id, rfl⟩) typed rooted
  obtain ⟨descriptor, visible, declared, sameTy, sameMutable, sameCounter⟩ :=
    typePlace_local_scalarFacts checkFuel frame.typing id frame.typingCounter frame.typingCounter ty writable binding placeTyped
  subst ty
  obtain ⟨other, root, old, runtimeDeclared, rootResolved, found, represented⟩ := source.locals id visible
  obtain ⟨scope, rootEq⟩ := rootOf_variable frame.interpretation id before root rootResolved
  subst root
  let cleared := { frame with rootCursor := { frame.rootCursor with eff := {} } }
  have clearedSource : AcceptedFrame config accepted cleared before types := source.withRootCursor _ rfl
  have checked' : CheckedValue (ordinaryOperandFrame cleared checkFuel) expression descriptor.ty roots operandTypingAfter operandRootsAfter := checked
  have resolved : ∀ runtimeFuel, evalPlace (runtimeFuel + 1) config cleared.interpretation.environment (.var id) before =
      .ok ⟨.local frame.interpretation.environment.act scope id, []⟩ before := by
    intro runtimeFuel; simp [cleared, evalPlace, rootResolved, bind, pure]
  have result := execStmt_checkedScalarAssign_observation fuel checkFuel config accepted cleared before ambient types live regions pending
    (.var id) expression origin (.local frame.interpretation.environment.act scope id) descriptor.ty old form world clearedSource
    resolved found (scalar descriptor declared) roots operandTypingAfter operandRootsAfter checked'
  refine ⟨scope, ?_⟩
  cases step : execStmt fuel config frame.interpretation.environment (.assign (.var id) expression origin) before <;>
    simpa only [cleared, ScalarAssignmentObservation, step] using result

#print axioms execStmt_sourceScalarAssignGlobal_observation
#print axioms execStmt_sourceScalarAssignLocal_observation
end Goose.Proofs.ConstructionAcceptedExecution
