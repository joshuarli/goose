import Goose.Proofs.ConstructionAcceptedUnaryCallComplete
import Goose.Proofs.ConstructionAcceptedEarlierBinaryCompose

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem evalArguments_singleByValue_lowerFuel {expression : Expr} (config : EvalConfig) (ty : Ty)
    (fuel : Nat) (accepted : AcceptedModule config) (frame : ConstructionSourceFrame) (before : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (parameterVars : Array LocalVar) (parameter : Param)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types)
    (evaluate : ∀ inner, inner + 1 ≤ fuel → EarlierScalarOutcome config accepted frame before ambient types regions pending ty
      (evalValue inner config frame.interpretation.environment expression before)) :
    ∃ nextTypes nextLive nextAmbient,
      let outcome := evalArguments fuel config frame.interpretation.environment parameterVars [parameter] [.byVal expression] before
      RootTypesExtend types nextTypes ∧ before.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      before.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      AcceptedFrame config accepted frame (Goose.Proofs.Exit.stepState outcome) nextTypes ∧
      FutureGlobalsClear config frame.initialized (Goose.Proofs.Exit.stepState outcome) ∧
      EarlierCallerObservations before.nextAct before (Goose.Proofs.Exit.stepState outcome) types nextTypes ∧
      (match outcome with
       | .ok values _ => nextAmbient = ambient ∧ ∃ value, values = [value] ∧ ValueRepresentation ty value
       | .stop .. => True | .escape .. | .jump .. => False) := by
  cases fuel with
  | zero =>
    simp only [evalArguments, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
    exact ⟨types, live, ambient, (fun _ _ found => found), Nat.le_refl _, Nat.le_refl _, world, source, source.futureGlobals,
      EarlierCallerObservations.refl before.nextAct before types, trivial⟩
  | succ fuel =>
    obtain ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, finalSource, clear, observed, result⟩ :=
      evaluate fuel (by omega)
    cases execution : evalValue fuel config frame.interpretation.environment expression before with
    | stop reason after =>
      simp only [execution, Goose.Proofs.Exit.stepState] at acts scopes finalWorld finalSource clear observed result
      simp only [evalArguments, execution, bind, Goose.Proofs.Exit.stepState]
      exact ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, finalSource, clear, observed, trivial⟩
    | escape address carriers after | jump target kind after => simp only [execution] at result
    | ok value after =>
      simp only [execution, Goose.Proofs.Exit.stepState] at acts scopes finalWorld finalSource clear observed result
      obtain ⟨ambientEq, represented⟩ := result
      cases fuel with
      | zero =>
        simp only [evalArguments, execution, bind, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
        exact ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, finalSource, clear, observed, trivial⟩
      | succ fuel =>
        simp only [evalArguments, execution, bind, pure, Goose.Proofs.Exit.stepState]
        exact ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, finalSource, clear, observed,
          ambientEq, value, rfl, represented⟩



theorem evalArguments_singleByValue_earlier {expression : Expr} (config : EvalConfig) (ty : Ty)
    (fuel : Nat) (accepted : AcceptedModule config) (frame : ConstructionSourceFrame) (before : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (parameterVars : Array LocalVar) (parameter : Param)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types)
    (evaluate : ∀ fuel, EarlierScalarOutcome config accepted frame before ambient types regions pending ty
      (evalValue fuel config frame.interpretation.environment expression before)) :
    ∃ nextTypes nextLive nextAmbient,
      let outcome := evalArguments fuel config frame.interpretation.environment parameterVars [parameter] [.byVal expression] before
      RootTypesExtend types nextTypes ∧ before.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      before.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      AcceptedFrame config accepted frame (Goose.Proofs.Exit.stepState outcome) nextTypes ∧
      FutureGlobalsClear config frame.initialized (Goose.Proofs.Exit.stepState outcome) ∧
      EarlierCallerObservations before.nextAct before (Goose.Proofs.Exit.stepState outcome) types nextTypes ∧
      (match outcome with
       | .ok values _ => nextAmbient = ambient ∧ ∃ value, values = [value] ∧ ValueRepresentation ty value
       | .stop .. => True | .escape .. | .jump .. => False) := by
  apply evalArguments_singleByValue_lowerFuel config ty fuel accepted frame before ambient types live regions pending
    parameterVars parameter world source
  intro inner bound
  exact evaluate inner

theorem evalArguments_unaryRegisterExpression {expression : Expr} (config : EvalConfig) (integer : Goose.Core.IntTy)
    (form : UnaryRegisterExpression config integer expression) (fuel : Nat) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (parameterVars : Array LocalVar) (parameter : Param) (graph : RegisterCallGraphWithCallLocals config (.int integer))
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types)
    (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue frame expression (.int integer) roots typingAfter rootsAfter) :
    ∃ nextTypes nextLive nextAmbient,
      let outcome := evalArguments fuel config frame.interpretation.environment parameterVars [parameter] [.byVal expression] before
      RootTypesExtend types nextTypes ∧ before.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      before.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      AcceptedFrame config accepted frame (Goose.Proofs.Exit.stepState outcome) nextTypes ∧
      FutureGlobalsClear config frame.initialized (Goose.Proofs.Exit.stepState outcome) ∧
      EarlierCallerObservations before.nextAct before (Goose.Proofs.Exit.stepState outcome) types nextTypes ∧
      (match outcome with
       | .ok values _ => nextAmbient = ambient ∧ ∃ value, values = [value] ∧ ValueRepresentation (.int integer) value
       | .stop .. => True | .escape .. | .jump .. => False) := by
  exact evalArguments_singleByValue_earlier config (.int integer) fuel accepted frame before ambient types live regions pending
    parameterVars parameter world source (fun inner =>
      evalValue_unaryRegisterExpression config integer form inner accepted frame before ambient types live regions pending graph
        world source roots typingAfter rootsAfter checked)

#print axioms evalArguments_singleByValue_lowerFuel
#print axioms evalArguments_singleByValue_earlier
#print axioms evalArguments_unaryRegisterExpression
end Goose.Proofs.ConstructionAcceptedExecution
