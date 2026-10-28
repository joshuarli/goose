import Goose.Proofs.ConstructionAcceptedScalarAssignRoots

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst)
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem execStmt_sourceScalarAssignLocal (fuel checkFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (id : Nat) (expression : Expr) (origin : Goose.Core.OriginId) (form : AcceptedBinaryExpression expression)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types)
    (initialized : frame.initialized = config.module.globals.size)
    (position : SourcePosition accepted frame (.statement (.assign (.var id) expression origin)))
    (nesting : frame.typingFuel = checkFuel + 1)
    (scalar : ∀ descriptor, frame.typing.variables[id]? = some descriptor →
      (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool) :
    let outcome := execStmt fuel config frame.interpretation.environment (.assign (.var id) expression origin) before
    ∃ nextLive, AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) ambient types nextLive regions pending ∧
      AcceptedFrame config accepted frame (Goose.Proofs.Exit.stepState outcome) types ∧
      (match outcome with | .ok flow _ => flow = .normal .unit | .stop .. => True | .escape .. | .jump .. => False) := by
  obtain ⟨next, typingAfter, rootsAfter, typed, rooted⟩ := position.checked accepted frame _
  rw [nesting] at typed
  obtain ⟨ty, roots, operandTypingAfter, operandRootsAfter, checked, operandSource, sameNext, sameAfter,
      writable, binding, placeTyped, mutable⟩ :=
    checkedValue_scalarAssign_operand checkFuel config accepted frame before types (.var id) expression origin form
      next typingAfter rootsAfter source initialized (Or.inl ⟨id, rfl⟩) typed rooted
  obtain ⟨descriptor, visible, declared, sameTy, sameMutable, sameCounter⟩ :=
    typePlace_local_scalarFacts checkFuel frame.typing id frame.typingCounter frame.typingCounter ty writable binding placeTyped
  subst ty
  let cleared := { frame with rootCursor := { frame.rootCursor with eff := {} } }
  have clearedSource : AcceptedFrame config accepted cleared before types := source.withRootCursor _ rfl
  have checked' : CheckedValue (ordinaryOperandFrame cleared checkFuel) expression descriptor.ty roots operandTypingAfter operandRootsAfter := checked
  have result := execStmt_checkedScalarAssignLocal_registered fuel checkFuel config accepted cleared before ambient types live regions pending
    id expression origin descriptor form world clearedSource initialized visible declared (scalar descriptor declared)
    roots operandTypingAfter operandRootsAfter checked'
  obtain ⟨nextLive, nextWorld, nextSource, flow⟩ := result
  have originalSource : AcceptedFrame config accepted frame
      (Goose.Proofs.Exit.stepState (execStmt fuel config frame.interpretation.environment (.assign (.var id) expression origin) before)) types := by
    simpa only [cleared] using nextSource.withRootCursor frame.rootCursor rfl
  exact ⟨nextLive, nextWorld, originalSource, flow⟩

theorem execStmt_sourceScalarAssignGlobal (fuel checkFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (id : Nat) (expression : Expr) (origin : Goose.Core.OriginId) (form : AcceptedBinaryExpression expression)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types)
    (initialized : frame.initialized = config.module.globals.size)
    (position : SourcePosition accepted frame (.statement (.assign (.global id) expression origin)))
    (nesting : frame.typingFuel = checkFuel + 1)
    (scalar : ∀ descriptor, config.module.globals[id]? = some descriptor →
      (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool) :
    let outcome := execStmt fuel config frame.interpretation.environment (.assign (.global id) expression origin) before
    AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) ambient types live regions pending ∧
      AcceptedFrame config accepted frame (Goose.Proofs.Exit.stepState outcome) types ∧
      (match outcome with | .ok flow _ => flow = .normal .unit | .stop .. => True | .escape .. | .jump .. => False) := by
  obtain ⟨next, typingAfter, rootsAfter, typed, rooted⟩ := position.checked accepted frame _
  rw [nesting] at typed
  obtain ⟨ty, roots, operandTypingAfter, operandRootsAfter, checked, operandSource, sameNext, sameAfter,
      writable, binding, placeTyped, mutable⟩ :=
    checkedValue_scalarAssign_operand checkFuel config accepted frame before types (.global id) expression origin form
      next typingAfter rootsAfter source initialized (Or.inr ⟨id, rfl⟩) typed rooted
  obtain ⟨descriptor, inside, declared, sameTy, sameMutable, sameCounter⟩ :=
    typePlace_global_scalarFacts checkFuel frame.typing id frame.typingCounter frame.typingCounter ty writable binding placeTyped
  subst ty
  have moduleDeclared : config.module.globals[id]? = some descriptor := by
    rw [← source.compatible.module]; exact declared
  let cleared := { frame with rootCursor := { frame.rootCursor with eff := {} } }
  have clearedSource : AcceptedFrame config accepted cleared before types := source.withRootCursor _ rfl
  have checked' : CheckedValue (ordinaryOperandFrame cleared checkFuel) expression descriptor.ty roots operandTypingAfter operandRootsAfter := checked
  have result := execStmt_checkedScalarAssignGlobal_complete fuel checkFuel config accepted cleared before ambient types live regions pending
    id expression origin descriptor form world clearedSource initialized moduleDeclared (scalar descriptor moduleDeclared)
    roots operandTypingAfter operandRootsAfter checked'
  obtain ⟨nextWorld, nextSource, flow⟩ := result
  have originalSource : AcceptedFrame config accepted frame
      (Goose.Proofs.Exit.stepState (execStmt fuel config frame.interpretation.environment (.assign (.global id) expression origin) before)) types := by
    simpa only [cleared] using nextSource.withRootCursor frame.rootCursor rfl
  exact ⟨nextWorld, originalSource, flow⟩

#print axioms execStmt_sourceScalarAssignLocal
#print axioms execStmt_sourceScalarAssignGlobal
end Goose.Proofs.ConstructionAcceptedExecution
