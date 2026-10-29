import Goose.Proofs.ConstructionAcceptedRecursiveArgumentCursor
import Goose.Proofs.ConstructionAcceptedEarlierScalarComplete
import Goose.Proofs.ConstructionAcceptedEarlierBinaryCompose
import Goose.Proofs.ConstructionAcceptedInvocationValue

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

def RecursiveArgumentCallSafety (config : EvalConfig) (accepted : AcceptedModule config) (integer : Goose.Core.IntTy)
    (bound : Nat) : Prop :=
  ∀ callFuel, callFuel < bound → ∀ (implementation : Impl) (frame : ConstructionSourceFrame) (before : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (target origin : Nat) (context : Context) (callee : Impl) (parameter : Param) (descriptor : LocalVar) (summary : Summary)
    (argument : Expr), frame.source.impl = implementation → RecursiveArgumentExpression config integer implementation argument →
    config.module.contexts[target]? = some context → config.module.impls[context.impl]? = some callee →
    callee.params = #[parameter] → parameter.mode = .byValue → callee.vars[parameter.var]? = some descriptor →
    descriptor.ty = .int integer → callee.results = #[⟨.int integer, .register, none⟩] → callee.summary = .known summary →
    AcceptedWorld config frame.initialized before ambient types live regions pending → AcceptedFrame config accepted frame before types →
    ∀ roots typingAfter rootsAfter,
      CheckedValue frame (.call target [.byVal argument] origin) (.int integer) roots typingAfter rootsAfter →
      ∃ nextTypes nextLive nextAmbient,
        let outcome := invokeCall callFuel config frame.interpretation.environment target [.byVal argument] [.register (.int integer)] origin before
        RootTypesExtend types nextTypes ∧ before.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
        before.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
        AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
        AcceptedFrame config accepted frame (Goose.Proofs.Exit.stepState outcome) nextTypes ∧
        FutureGlobalsClear config frame.initialized (Goose.Proofs.Exit.stepState outcome) ∧
        EarlierCallerObservations before.nextAct before (Goose.Proofs.Exit.stepState outcome) types nextTypes ∧
        (match outcome with
         | .ok carriers _ => nextAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation (.int integer) value
         | .stop .. => True | .escape .. | .jump .. => False)

theorem evalValue_recursiveArgument_fromCalls {config : EvalConfig} {integer : Goose.Core.IntTy} {implementation : Impl} {expression : Expr}
    (form : RecursiveArgumentExpression config integer implementation expression) (fuel bound : Nat) (accepted : AcceptedModule config)
    (calls : RecursiveArgumentCallSafety config accepted integer bound) (fuelBound : fuel ≤ bound)
    (frame : ConstructionSourceFrame) (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (implementationEq : frame.source.impl = implementation)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types) (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue frame expression (.int integer) roots typingAfter rootsAfter) :
    EarlierScalarOutcome config accepted frame before ambient types regions pending (.int integer)
      (evalValue fuel config frame.interpretation.environment expression before) := by
  induction form generalizing fuel frame before ambient types live roots typingAfter rootsAfter with
  | literal value =>
    exact evalValue_checkedBinary_earlier config integer (.numeric (.scalar (.scalar (.integer integer value)))) fuel accepted frame before ambient types live regions pending
      world source roots typingAfter rootsAfter checked
  | localRead id descriptor declared descriptorType =>
    exact evalValue_checkedBinary_earlier config integer (.numeric (.scalar (.scalar (.localRead id)))) fuel accepted frame before ambient types live regions pending
      world source roots typingAfter rootsAfter checked
  | @binary left right operation origin leftForm rightForm leftIH rightIH =>
    cases fuel with
    | zero =>
      simp only [EarlierScalarOutcome, evalValue, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
      exact ⟨types, live, ambient, (fun _ _ found => found), Nat.le_refl _, Nat.le_refl _, world, source,
        source.futureGlobals, EarlierCallerObservations.refl _ _ _, trivial⟩
    | succ fuel =>
      cases depth : frame.typingFuel with
      | zero =>
        have typed := checked.typing
        rw [depth] at typed
        change Except.error _ = Except.ok _ at typed
        cases typed
      | succ checkFuel =>
        obtain ⟨operandInteger, middle, leftRoots, rightRoots, rootMiddle, rootFinal, sameTy, sameRoots, leftChecked, rightChecked⟩ :=
          checkedValue_bin_operands frame checkFuel operation left right origin (.int integer) roots typingAfter rootsAfter depth checked
        have sameInteger : integer = operandInteger := Ty.int.inj sameTy
        subst operandInteger
        let leftFrame := ordinaryOperandFrame frame checkFuel
        let rightFrame := { leftFrame with typingCounter := middle, rootCursor := rootMiddle }
        have cursor := checkedRecursiveArgument_cursor leftForm leftFrame leftRoots middle rootMiddle
          (by simpa [leftFrame, ordinaryOperandFrame] using source.compatible.module)
          (by simpa [leftFrame, ordinaryOperandFrame] using source.compatible.rootModule) (Or.inl rfl) leftChecked
        have sameCounter : middle = frame.typingCounter := by simpa [leftFrame, ordinaryOperandFrame] using cursor.1
        have sameRoot : rootMiddle.nextVar = frame.rootCursor.nextVar := by simpa [leftFrame, ordinaryOperandFrame] using cursor.2
        have leftSource := ordinaryOperandFrame_accepted accepted frame checkFuel before types source
        obtain ⟨leftTypes, leftLive, leftAmbient, extend, acts, scopes, leftWorld, leftFinalSource, clear, observed, result⟩ :=
          leftIH fuel (by omega) leftFrame before ambient types live (by simpa [leftFrame, ordinaryOperandFrame] using implementationEq)
            world leftSource leftRoots middle rootMiddle leftChecked
        have leftSafe : EarlierScalarOutcome config accepted frame before ambient types regions pending (.int integer)
            (evalValue fuel config frame.interpretation.environment left before) := by
          refine ⟨leftTypes, leftLive, leftAmbient, extend, acts, scopes, leftWorld, ?_, clear, observed, result⟩
          exact source.afterEarlierObservations acts scopes observed
        have rightSafe : ∀ state currentTypes currentLive,
            AcceptedWorld config frame.initialized state ambient currentTypes currentLive regions pending →
            AcceptedFrame config accepted frame state currentTypes →
            EarlierScalarOutcome config accepted frame state ambient currentTypes regions pending (.int integer)
              (evalValue fuel config frame.interpretation.environment right state) := by
          intro state currentTypes currentLive currentWorld currentSource
          have rightSource : AcceptedFrame config accepted rightFrame state currentTypes := by
            simpa [rightFrame, leftFrame, ordinaryOperandFrame, sameCounter] using
              (ordinaryOperandFrame_accepted accepted frame checkFuel state currentTypes currentSource).withRootCursor rootMiddle sameRoot
          obtain ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, finalSource, clear, observed, result⟩ :=
            rightIH fuel (by omega) rightFrame state ambient currentTypes currentLive
              (by simpa [rightFrame, leftFrame, ordinaryOperandFrame] using implementationEq) currentWorld rightSource rightRoots typingAfter rootFinal rightChecked
          refine ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, ?_, clear, observed, result⟩
          exact currentSource.afterEarlierObservations acts scopes observed
        exact evalValue_binary_earlier_compose fuel config accepted frame before ambient types regions pending integer operation left right origin leftSafe rightSafe
  | @call argument target origin context callee parameter descriptor summary contextAt calleeAt parameters mode declared descriptorType results known argumentForm ih =>
    apply evalValue_registerArguments_earlier_fromInvocation fuel config accepted frame before ambient types live regions pending
      target [.byVal argument] context callee (.int integer) origin world source contextAt calleeAt results
    intro callFuel fuelEq
    exact calls callFuel (by omega) implementation frame before ambient types live regions pending target origin context callee parameter descriptor summary argument
      implementationEq argumentForm contextAt calleeAt parameters mode declared descriptorType results known world source roots typingAfter rootsAfter checked

#print axioms evalValue_recursiveArgument_fromCalls
end Goose.Proofs.ConstructionAcceptedExecution
