import Goose.Proofs.ConstructionAcceptedGlobalAssignFrame
import Goose.Proofs.ConstructionAcceptedScalarWriteRuntime

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst)
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem writeLoc_scalar_prefix_complete (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (root : RootInst) (ty : Ty) (old value : Value)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types)
    (rootSafe : ∀ id, frame.initialized ≤ id → id < config.module.globals.size → root ≠ .global id)
    (rootType : types root = some ty) (retained : live root) (found : before.objects.lookup root = some old)
    (scalar : (∃ intTy number, value = .int intTy number) ∨ ∃ boolean, value = .bool boolean)
    (represented : ValueRepresentation ty value) (pointers : PointerTypedValue types ty value) :
    let outcome := writeLoc fuel config.layout ⟨root, []⟩ value before
    AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) ambient types live regions pending ∧
      AcceptedFrame config accepted frame (Goose.Proofs.Exit.stepState outcome) types ∧
      (match outcome with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  cases fuel with
  | zero =>
    simp [writeLoc, EvalM.get, found, bind, writeValuePath, timeout, EvalM.stop, Goose.Proofs.Exit.stepState, world, source]
  | succ fuel =>
    obtain ⟨after, bound, afterWorld⟩ := bindRoot_scalar_update_world config frame.initialized before ambient types live root ty value
      regions pending world scalar rootType retained represented pointers
    have afterSource := source.bindScalar_update_preservingFuture root ty value rootSafe rootType represented scalar bound
    simp [writeLoc, EvalM.get, found, bind, writeValuePath, pure, bound, Goose.Proofs.Exit.stepState, afterWorld, afterSource]

theorem execStmt_checkedScalarAssignGlobal_prefix_positive (fuel checkFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (id : Nat) (expression : Expr) (origin : Goose.Core.OriginId) (ty : Ty) (old : Value)
    (form : AcceptedBinaryExpression expression)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types)
    (available : id < frame.initialized)
    (rootType : types (.global id) = some ty) (retained : live (.global id)) (found : before.objects.lookup (.global id) = some old)
    (scalarTy : (∃ intTy, ty = .int intTy) ∨ ty = .bool)
    (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue (ordinaryOperandFrame frame checkFuel) expression ty roots typingAfter rootsAfter) :
    let outcome := execStmt (fuel + 2) config frame.interpretation.environment (.assign (.global id) expression origin) before
    AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) ambient types live regions pending ∧
      AcceptedFrame config accepted frame (Goose.Proofs.Exit.stepState outcome) types ∧
      (match outcome with | .ok flow _ => flow = .normal .unit | .stop .. => True | .escape .. | .jump .. => False) := by
  have child := ordinaryOperandFrame_accepted accepted frame checkFuel before types source
  have evaluated := evalValue_checked_binary_recursive form (fuel + 1) config accepted (ordinaryOperandFrame frame checkFuel) before
    ambient types live regions pending world child ty roots typingAfter rootsAfter checked
  change Goose.Proofs.Exit.stepState (evalValue (fuel + 1) config frame.interpretation.environment expression before) = before ∧ _ at evaluated
  cases execution : evalValue (fuel + 1) config frame.interpretation.environment expression before with
  | stop reason after =>
    have same : after = before := by simpa [execution, Goose.Proofs.Exit.stepState] using evaluated.1
    subst after
    simp [execStmt, evalPlace, execution, bind, pure, Goose.Proofs.Exit.stepState, world, source]
  | escape address carriers after =>
    exact ((evalValue_scalar_controlFree form (fuel + 1) config frame.interpretation.environment).1 before address carriers after execution).elim
  | jump target kind after =>
    exact ((evalValue_scalar_controlFree form (fuel + 1) config frame.interpretation.environment).2 before target kind after execution).elim
  | ok value after =>
    have same : after = before := by simpa [execution, Goose.Proofs.Exit.stepState] using evaluated.1
    subst after
    have valid := evaluated.2.1 value before execution
    have scalar : (∃ intTy number, value = .int intTy number) ∨ ∃ boolean, value = .bool boolean := by
      rcases scalarTy with ⟨intTy, same⟩ | same <;> rw [same] at valid <;>
        cases value <;> cases valid.represented <;> simp_all [Ty.nonfixed]
    have result := writeLoc_scalar_prefix_complete (fuel + 1) config accepted frame before ambient types live regions pending (.global id) ty old value
      world source (by intro future futureBound within equal; cases equal; omega) rootType retained found scalar valid.represented valid.pointers
    change AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState (writeLoc (fuel + 1) config.layout ⟨.global id, []⟩ value before)) ambient types live regions pending ∧ _ at result
    cases write : writeLoc (fuel + 1) config.layout ⟨.global id, []⟩ value before with
    | stop reason after =>
      simp only [write, Goose.Proofs.Exit.stepState] at result
      simp only [execStmt, evalPlace, pure, bind, execution, write, Goose.Proofs.Exit.stepState]
      exact ⟨result.1, result.2.1, trivial⟩
    | escape address carriers after | jump target kind after =>
      simp only [write] at result
      exact result.2.2.elim
    | ok valueUnit after =>
      cases valueUnit
      simp only [write, Goose.Proofs.Exit.stepState] at result
      simp only [execStmt, evalPlace, execution, bind, write, pure, Goose.Proofs.Exit.stepState]
      exact ⟨result.1, result.2.1, trivial⟩


theorem execStmt_checkedScalarAssignGlobal_prefix_complete (fuel checkFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (id : Nat) (expression : Expr) (origin : Goose.Core.OriginId) (descriptor : Global)
    (form : AcceptedBinaryExpression expression)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types)
    (available : id < frame.initialized)
    (declared : config.module.globals[id]? = some descriptor)
    (scalarTy : (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue (ordinaryOperandFrame frame checkFuel) expression descriptor.ty roots typingAfter rootsAfter) :
    let outcome := execStmt fuel config frame.interpretation.environment (.assign (.global id) expression origin) before
    AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) ambient types live regions pending ∧
      AcceptedFrame config accepted frame (Goose.Proofs.Exit.stepState outcome) types ∧
      (match outcome with | .ok flow _ => flow = .normal .unit | .stop .. => True | .escape .. | .jump .. => False) := by
  have inside := (Array.getElem?_eq_some_iff.mp declared).1
  have retained := world.globalLive id available
  have rootType := world.globalTypes id descriptor declared
  obtain ⟨other, old, otherDeclared, found, represented⟩ := world.globals.2 id available
  have same : other = descriptor := Option.some.inj (otherDeclared.symm.trans declared)
  subst other
  cases fuel with
  | zero => simp [execStmt, timeout, EvalM.stop, Goose.Proofs.Exit.stepState, world, source]
  | succ fuel =>
    cases fuel with
    | zero => simp [execStmt, evalPlace, timeout, EvalM.stop, bind, Goose.Proofs.Exit.stepState, world, source]
    | succ fuel =>
      exact execStmt_checkedScalarAssignGlobal_prefix_positive fuel checkFuel config accepted frame before ambient types live regions pending
        id expression origin descriptor.ty old form world source available rootType retained found scalarTy roots typingAfter rootsAfter checked

#print axioms execStmt_checkedScalarAssignGlobal_prefix_complete
#print axioms writeLoc_scalar_prefix_complete
end Goose.Proofs.ConstructionAcceptedExecution
