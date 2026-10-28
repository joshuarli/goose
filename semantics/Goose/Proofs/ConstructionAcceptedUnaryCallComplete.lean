import Goose.Proofs.ConstructionAcceptedEarlierCallLocalGraph
import Goose.Proofs.ConstructionAcceptedInvocationValue
import Goose.Proofs.ConstructionAcceptedNumericComplete
import Goose.Proofs.ConstructionAcceptedScalarControl

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

inductive UnaryRegisterExpression (config : EvalConfig) (integer : Goose.Core.IntTy) : Expr → Prop
  | scalar {expression : Expr} (form : AcceptedBinaryExpression expression) : UnaryRegisterExpression config integer expression
  | call (target origin : Nat) (context : Context) (callee : Impl)
      (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
      (parameters : callee.params = #[]) (results : callee.results = #[⟨.int integer, .register, none⟩]) :
      UnaryRegisterExpression config integer (.call target [] origin)
  | unary (operation : Goose.Core.UnOp) (expression : Expr) (origin : Nat)
      (operand : UnaryRegisterExpression config integer expression) :
      UnaryRegisterExpression config integer (.un operation expression origin)

theorem evalValue_unaryRegisterExpression {expression : Expr} (config : EvalConfig) (integer : Goose.Core.IntTy)
    (form : UnaryRegisterExpression config integer expression) (fuel : Nat) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (graph : RegisterCallGraphWithCallLocals config (.int integer))
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types)
    (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue frame expression (.int integer) roots typingAfter rootsAfter) :
    ∃ nextTypes nextLive nextAmbient,
      let outcome := evalValue fuel config frame.interpretation.environment expression before
      RootTypesExtend types nextTypes ∧ before.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      before.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      AcceptedFrame config accepted frame (Goose.Proofs.Exit.stepState outcome) nextTypes ∧
      FutureGlobalsClear config frame.initialized (Goose.Proofs.Exit.stepState outcome) ∧
      EarlierCallerObservations before.nextAct before (Goose.Proofs.Exit.stepState outcome) types nextTypes ∧
      (match outcome with
       | .ok value _ => nextAmbient = ambient ∧ ValueRepresentation (.int integer) value
       | .stop .. => True | .escape .. | .jump .. => False) := by
  induction form generalizing fuel frame before ambient types live roots typingAfter rootsAfter with
  | @scalar scalarExpression form =>
    have complete := evalValue_checked_binary_recursive form fuel config accepted frame before ambient types live regions pending
      world source (.int integer) roots typingAfter rootsAfter checked
    have control := evalValue_scalar_controlFree form fuel config frame.interpretation.environment
    cases evaluated : evalValue fuel config frame.interpretation.environment scalarExpression before with
    | stop reason after =>
      simp only [evaluated, Goose.Proofs.Exit.stepState] at complete
      have same := complete.1
      subst after
      exact ⟨types, live, ambient, (fun _ _ found => found), Nat.le_refl _, Nat.le_refl _, world, source,
        source.futureGlobals, EarlierCallerObservations.refl _ _ _, trivial⟩
    | escape target carriers after => exact False.elim (control.1 before target carriers after evaluated)
    | jump target kind after => exact False.elim (control.2 before target kind after evaluated)
    | ok value after =>
      have acceptedValue := complete.2.1 value after evaluated
      simp only [evaluated, Goose.Proofs.Exit.stepState] at complete
      have same := complete.1
      subst after
      exact ⟨types, live, ambient, (fun _ _ found => found), Nat.le_refl _, Nat.le_refl _, world, source,
        source.futureGlobals, EarlierCallerObservations.refl _ _ _, rfl, acceptedValue.represented⟩
  | call target origin context callee contextAt calleeAt parameters results =>
    apply evalValue_register_earlier_fromInvocation fuel config accepted frame before ambient types live regions pending
      target context callee (.int integer) origin world source contextAt calleeAt results
    intro callFuel _
    obtain ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, clear, observed, result⟩ :=
      invokeCall_recursive_register_callLocal_earlier callFuel config accepted (.int integer) (Or.inl ⟨integer, rfl⟩) graph
        frame before ambient types live regions pending target context callee origin world source contextAt calleeAt parameters results
        roots typingAfter rootsAfter checked
    exact ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld,
      source.afterEarlierObservations acts scopes observed, clear, observed, result⟩
  | unary operation expression origin operand ih =>
    cases fuel with
    | zero =>
      simp only [evalValue, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
      exact ⟨types, live, ambient, (fun _ _ found => found), Nat.le_refl _, Nat.le_refl _, world, source, source.futureGlobals,
        EarlierCallerObservations.refl before.nextAct before types, trivial⟩
    | succ fuel =>
      cases nesting : frame.typingFuel with
      | zero =>
        have typed := checked.typing
        rw [nesting] at typed
        change Except.error _ = Except.ok _ at typed
        cases typed
      | succ checkFuel =>
        obtain ⟨operandInteger, operandRoots, operandAfter, sameTy, sameRoots, operandChecked⟩ :=
          checkedValue_un_operand frame checkFuel operation expression origin (.int integer) roots typingAfter rootsAfter nesting checked
        have sameInteger : integer = operandInteger := Ty.int.inj sameTy
        subst operandInteger
        let operandFrame := ordinaryOperandFrame frame checkFuel
        have operandSource := ordinaryOperandFrame_accepted accepted frame checkFuel before types source
        obtain ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, finalOperandSource, clear, observed, result⟩ :=
          ih fuel operandFrame before ambient types live world operandSource operandRoots typingAfter operandAfter operandChecked
        have finalSource := source.afterEarlierObservations acts scopes observed
        change AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState
          (evalValue fuel config frame.interpretation.environment expression before)) nextAmbient nextTypes nextLive regions pending at finalWorld
        change AcceptedFrame config accepted frame (Goose.Proofs.Exit.stepState
          (evalValue fuel config frame.interpretation.environment expression before)) nextTypes at finalSource
        change FutureGlobalsClear config frame.initialized (Goose.Proofs.Exit.stepState
          (evalValue fuel config frame.interpretation.environment expression before)) at clear
        change EarlierCallerObservations before.nextAct before (Goose.Proofs.Exit.stepState
          (evalValue fuel config frame.interpretation.environment expression before)) types nextTypes at observed
        change before.nextAct ≤ (Goose.Proofs.Exit.stepState
          (evalValue fuel config frame.interpretation.environment expression before)).nextAct at acts
        change before.nextScope ≤ (Goose.Proofs.Exit.stepState
          (evalValue fuel config frame.interpretation.environment expression before)).nextScope at scopes
        change (match evalValue fuel config frame.interpretation.environment expression before with
          | .ok value _ => nextAmbient = ambient ∧ ValueRepresentation (.int integer) value
          | .stop .. => True | .escape .. | .jump .. => False) at result
        cases execution : evalValue fuel config frame.interpretation.environment expression before with
        | stop reason after =>
          simp only [execution, Goose.Proofs.Exit.stepState] at acts scopes finalWorld finalSource clear observed result
          simp only [evalValue, execution, bind, Goose.Proofs.Exit.stepState]
          exact ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, finalSource, clear, observed, trivial⟩
        | escape address carriers after | jump target kind after => simp only [execution] at result
        | ok value after =>
          simp only [execution, Goose.Proofs.Exit.stepState] at acts scopes finalWorld finalSource clear observed result
          obtain ⟨ambientEq, represented⟩ := result
          cases represented with
          | stored ty stored nonfixed logical => simp [Ty.nonfixed] at nonfixed
          | integer _ number =>
            cases computed : Goose.Core.evalUn config.profile operation integer number with
            | error reason =>
              simp only [evalValue, execution, bind, expectInt, pure, computed, abortAt, EvalM.stop, Goose.Proofs.Exit.stepState]
              exact ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, finalSource, clear, observed, trivial⟩
            | ok value =>
              simp only [evalValue, execution, bind, expectInt, pure, computed, Goose.Proofs.Exit.stepState]
              exact ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, finalSource, clear, observed,
                ambientEq, .integer integer value⟩

#print axioms evalValue_unaryRegisterExpression
end Goose.Proofs.ConstructionAcceptedExecution
