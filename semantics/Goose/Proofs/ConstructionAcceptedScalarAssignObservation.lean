import Goose.Proofs.ConstructionAcceptedScalarWriteObservation
import Goose.Proofs.ConstructionAcceptedScalarControl

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem execStmt_checkedScalarAssign_observation (fuel checkFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (place : Place) (expression : Expr) (origin : Goose.Core.OriginId) (root : Goose.Core.RootInst) (ty : Ty) (old : Value)
    (form : AcceptedBinaryExpression expression)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types)
    (resolved : ∀ runtimeFuel, evalPlace (runtimeFuel + 1) config frame.interpretation.environment place before = .ok ⟨root, []⟩ before)
    (found : before.objects.lookup root = some old) (scalarTy : (∃ intTy, ty = .int intTy) ∨ ty = .bool)
    (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue (ordinaryOperandFrame frame checkFuel) expression ty roots typingAfter rootsAfter) :
    let step := execStmt fuel config frame.interpretation.environment (.assign place expression origin) before
    let after := Goose.Proofs.Exit.stepState step
    after.nextAct = before.nextAct ∧ after.nextScope = before.nextScope ∧
      (∀ other, other ≠ root → after.objects.lookup other = before.objects.lookup other ∧
        after.objectOrdinals.lookup other = before.objectOrdinals.lookup other) ∧
      match step with
      | .ok _ _ => ∃ value, after.objects.lookup root = some value ∧
          ((∃ intTy number, value = .int intTy number) ∨ ∃ boolean, value = .bool boolean)
      | .stop .. => True
      | _ => False := by
  cases fuel with
  | zero => simp [execStmt, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
  | succ fuel =>
    cases fuel with
    | zero => simp [execStmt, evalPlace, timeout, EvalM.stop, bind, Goose.Proofs.Exit.stepState]
    | succ fuel =>
      have child := ordinaryOperandFrame_accepted accepted frame checkFuel before types source
      have evaluated := evalValue_checked_binary_recursive form (fuel + 1) config accepted (ordinaryOperandFrame frame checkFuel) before
        ambient types live regions pending world child ty roots typingAfter rootsAfter checked
      change Goose.Proofs.Exit.stepState (evalValue (fuel + 1) config frame.interpretation.environment expression before) = before ∧ _ at evaluated
      cases execution : evalValue (fuel + 1) config frame.interpretation.environment expression before with
      | escape address carriers after =>
        exact ((evalValue_scalar_controlFree form (fuel + 1) config frame.interpretation.environment).1 before address carriers after execution).elim
      | jump target kind after =>
        exact ((evalValue_scalar_controlFree form (fuel + 1) config frame.interpretation.environment).2 before target kind after execution).elim
      | stop reason after =>
        have same : after = before := by simpa [execution, Goose.Proofs.Exit.stepState] using evaluated.1
        subst after
        simp [execStmt, resolved fuel, execution, bind, Goose.Proofs.Exit.stepState]
      | ok value after =>
        have same : after = before := by simpa [execution, Goose.Proofs.Exit.stepState] using evaluated.1
        subst after
        have valid := evaluated.2.1 value before execution
        have scalar : (∃ intTy number, value = .int intTy number) ∨ ∃ boolean, value = .bool boolean := by
          rcases scalarTy with ⟨intTy, same⟩ | same <;> rw [same] at valid <;>
            cases value <;> cases valid.represented <;> simp_all [Ty.nonfixed]
        have write := writeLoc_root_observation (fuel + 1) config.layout root old value before found
        cases stored : writeLoc (fuel + 1) config.layout ⟨root, []⟩ value before with
        | escape address carriers after | jump target kind after => simp [stored] at write
        | stop reason after =>
          simp only [stored, Goose.Proofs.Exit.stepState] at write
          simpa [execStmt, resolved fuel, execution, bind, stored, Goose.Proofs.Exit.stepState] using write
        | ok unit after =>
          cases unit
          simp only [stored, Goose.Proofs.Exit.stepState] at write
          simpa only [execStmt, resolved fuel, execution, bind, stored, pure, Goose.Proofs.Exit.stepState] using
            And.intro write.1 (And.intro write.2.1 (And.intro write.2.2.1 ⟨value, write.2.2.2, scalar⟩))

#print axioms execStmt_checkedScalarAssign_observation
end Goose.Proofs.ConstructionAcceptedExecution
