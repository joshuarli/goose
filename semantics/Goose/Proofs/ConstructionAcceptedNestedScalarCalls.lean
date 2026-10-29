import Goose.Proofs.ConstructionAcceptedSingleArgumentValue
import Goose.Proofs.ConstructionAcceptedEarlierScalarComplete
import Goose.Proofs.ConstructionAcceptedParameterizedScalarBody
import Goose.Proofs.ConstructionAcceptedNestedParameterCursor

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

inductive NestedScalarCallExpression (config : EvalConfig) (integer : Goose.Core.IntTy) : Expr → Prop
  | scalar {expression : Expr} : AcceptedBinaryExpression expression → NestedScalarCallExpression config integer expression
  | binary {left right : Expr} (operation : Goose.Core.BinOp) (origin : Nat) :
      NestedScalarCallExpression config integer left → NestedScalarCallExpression config integer right →
      NestedScalarCallExpression config integer (.bin operation left right origin)
  | call {argument : Expr} (target origin : Nat) (context : Context) (callee : Impl) (parameter : Param)
      (descriptor : LocalVar) (summary : Summary) (bodyExpression : Expr) :
      config.module.contexts[target]? = some context → config.module.impls[context.impl]? = some callee →
      callee.params = #[parameter] → parameter.mode = .byValue → callee.vars[parameter.var]? = some descriptor →
      descriptor.ty = .int integer → callee.results = #[⟨.int integer, .register, none⟩] →
      callee.summary = .known summary → callee.body = ⟨callee.body.scope, [], some bodyExpression⟩ →
      AcceptedBinaryExpression bodyExpression → NestedScalarCallExpression config integer argument →
      NestedScalarCallExpression config integer (.call target [.byVal argument] origin)

theorem nestedScalarCall_cursor {config : EvalConfig} {integer : Goose.Core.IntTy} {expression : Expr}
    (form : NestedScalarCallExpression config integer expression) :
    ∀ (accepted : AcceptedModule config) (frame : ConstructionSourceFrame) (before : ExecutionState) (types : RootTypes)
      (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState),
      AcceptedFrame config accepted frame before types →
      (frame.typing.resultRequests = [] ∨ frame.typing.resultRequests = [.register]) →
      CheckedValue frame expression (.int integer) roots typingAfter rootsAfter →
      typingAfter = frame.typingCounter ∧ rootsAfter.nextVar = frame.rootCursor.nextVar := by
  induction form with
  | scalar form =>
    intro accepted frame before types roots typingAfter rootsAfter source requests checked
    exact checked_binary_recursive_cursor form frame _ roots typingAfter rootsAfter checked
  | @binary left right operation origin leftForm rightForm leftIH rightIH =>
    intro accepted frame before types roots typingAfter rootsAfter source requests checked
    cases depth : frame.typingFuel with
    | zero =>
      have typed := checked.typing
      rw [depth] at typed
      change Except.error _ = Except.ok _ at typed
      cases typed
    | succ fuel =>
      obtain ⟨operandInteger, middle, leftRoots, rightRoots, rootMiddle, rootFinal, sameTy, sameRoots, leftChecked, rightChecked⟩ :=
        checkedValue_bin_operands frame fuel operation left right origin (.int integer) roots typingAfter rootsAfter depth checked
      have sameInteger : integer = operandInteger := Ty.int.inj sameTy
      subst operandInteger
      let leftFrame := ordinaryOperandFrame frame fuel
      let rightFrame := { leftFrame with typingCounter := middle, rootCursor := rootMiddle }
      have leftSource := ordinaryOperandFrame_accepted accepted frame fuel before types source
      have leftFacts := leftIH accepted leftFrame before types leftRoots middle rootMiddle leftSource (Or.inl rfl) leftChecked
      have sameCounter : middle = frame.typingCounter := by simpa [leftFrame, ordinaryOperandFrame] using leftFacts.1
      have sameRoot : rootMiddle.nextVar = frame.rootCursor.nextVar := by simpa [leftFrame, ordinaryOperandFrame] using leftFacts.2
      have rightSource : AcceptedFrame config accepted rightFrame before types := by
        simpa [rightFrame, leftFrame, ordinaryOperandFrame, sameCounter] using
          (ordinaryOperandFrame_accepted accepted frame fuel before types source).withRootCursor rootMiddle sameRoot
      have rightFacts := rightIH accepted rightFrame before types rightRoots typingAfter rootFinal rightSource (Or.inl rfl) rightChecked
      have lastRoot := nestedBin_final_nextVar frame operation left right origin roots leftRoots rightRoots rootsAfter rootMiddle rootFinal
        checked.provenance leftChecked.provenance rightChecked.provenance
      exact ⟨by simpa [leftFrame, rightFrame, ordinaryOperandFrame] using rightFacts.1.trans leftFacts.1,
        lastRoot.trans (by simpa [leftFrame, rightFrame, ordinaryOperandFrame] using rightFacts.2.trans leftFacts.2)⟩
  | @call argument target origin context callee parameter descriptor summary bodyExpression contextAt calleeAt parameters mode declared descriptorType results known body bodyForm argumentForm ih =>
    intro accepted frame before types roots typingAfter rootsAfter source requests checked
    cases depth : frame.typingFuel with
    | zero =>
      have typed := checked.typing
      rw [depth] at typed
      change Except.error _ = Except.ok _ at typed
      cases typed
    | succ remaining =>
      cases remaining with
      | zero =>
        have typed := checked.typing
        rw [depth] at typed
        simp only [typeExpr, source.compatible.module, contextAt, calleeAt, typeArguments, bind, StateT.bind, Except.bind] at typed
        change Except.error _ = Except.ok _ at typed
        cases typed
      | succ fuel =>
        obtain ⟨argumentRoots, argumentTypingAfter, argumentRootsAfter, operandSource, operandChecked⟩ :=
          checkedValue_singleByValue_argument_fromChecker frame before types target origin context callee parameter descriptor argument integer fuel
            source contextAt calleeAt parameters mode declared descriptorType depth (.int integer) roots typingAfter rootsAfter checked
        have operandFacts := ih accepted (ordinaryOperandFrame frame fuel) before types argumentRoots argumentTypingAfter argumentRootsAfter
          operandSource (Or.inl rfl) operandChecked
        have typingContext : frame.typing.module.contexts[target]? = some context := by simpa [source.compatible.module] using contextAt
        have typingCallee : frame.typing.module.impls[context.impl]? = some callee := by simpa [source.compatible.module] using calleeAt
        obtain ⟨middle, argumentsTyped⟩ := typeExpr_call_arguments (fuel + 1) frame.typing target context callee [.byVal argument]
          origin frame.typingCounter typingAfter [.int integer] typingContext typingCallee (by simpa [depth] using checked.typing)
        have argumentsTyped' : typeArguments (fuel + 1) frame.typing callee [parameter] [.byVal argument] frame.typingCounter = .ok ((), middle) := by
          simpa [parameters] using argumentsTyped
        obtain ⟨counter, typed, rest⟩ := typeArguments_scalarByValue_cons fuel frame.typing callee parameter descriptor [] argument []
          frame.typingCounter middle mode declared (Or.inl ⟨integer, descriptorType⟩) argumentsTyped'
        have sameCounter : counter = argumentTypingAfter := by
          have same := typed.symm.trans operandChecked.typing
          exact (Prod.mk.inj (Except.ok.inj same)).2
        subst counter
        cases fuel with
        | zero => change Except.error _ = Except.ok _ at rest; cases rest
        | succ fuel =>
          have middleEq : middle = argumentTypingAfter := by simpa [typeArguments, pure, StateT.pure, Except.pure] using rest.symm
          have finalTyping := typeExpr_singleByValueRegisterCall_after (fuel + 1) frame.typing target origin context callee parameter argument (.int integer)
            frame.typingCounter middle typingAfter [.int integer] typingContext typingCallee parameters results (Or.inl ⟨integer, rfl⟩) requests argumentsTyped' (by simpa [depth] using checked.typing)
          have rootContext : frame.source.mod.contexts[target]? = some context := by simpa [source.compatible.rootModule] using contextAt
          have rootCallee : frame.source.mod.impls[context.impl]? = some callee := by simpa [source.compatible.rootModule] using calleeAt
          obtain ⟨selected, actual, allRoots, rootMiddle, selectedAt, actualAt, argumentsRooted, contents⟩ := rpExpr_call_argumentChecks checked.provenance
          have sameContext : selected = context := Option.some.inj (selectedAt.symm.trans rootContext)
          subst selected
          have sameCallee : actual = callee := Option.some.inj (actualAt.symm.trans rootCallee)
          subst actual
          obtain ⟨operandRoots, operandAfter, remainingRoots, remainingAfter, operandRooted, tail⟩ :=
            rpArgs_byValue_cons frame.source argument [] frame.rootCursor rootMiddle allRoots argumentsRooted
          have sameAfter : operandAfter = argumentRootsAfter := by
            have same := operandRooted.symm.trans operandChecked.provenance
            exact (Prod.mk.inj (Except.ok.inj same)).2
          subst operandAfter
          have argsNext := rpArgs_singleByValue_nextVar operandRooted argumentsRooted
          have callNext := rpExpr_singleByValue_nextVar rootContext rootCallee parameters argumentsRooted checked.provenance
          exact ⟨finalTyping.trans (middleEq.trans (by simpa [ordinaryOperandFrame] using operandFacts.1)),
            callNext.trans (argsNext.trans (by simpa [ordinaryOperandFrame] using operandFacts.2))⟩

theorem evalValue_nestedScalarCall {config : EvalConfig} {integer : Goose.Core.IntTy} {expression : Expr}
    (form : NestedScalarCallExpression config integer expression) (fuel : Nat) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types) (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue frame expression (.int integer) roots typingAfter rootsAfter) :
    EarlierScalarOutcome config accepted frame before ambient types regions pending (.int integer)
      (evalValue fuel config frame.interpretation.environment expression before) := by
  induction form generalizing fuel frame before ambient types live roots typingAfter rootsAfter with
  | scalar form =>
    exact evalValue_checkedBinary_earlier config integer form fuel accepted frame before ambient types live regions pending
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
        have leftSource := ordinaryOperandFrame_accepted accepted frame checkFuel before types source
        have cursor := nestedScalarCall_cursor leftForm accepted leftFrame before types leftRoots middle rootMiddle leftSource (Or.inl rfl) leftChecked
        have sameCounter : middle = frame.typingCounter := by simpa [leftFrame, ordinaryOperandFrame] using cursor.1
        have sameRoot : rootMiddle.nextVar = frame.rootCursor.nextVar := by simpa [leftFrame, ordinaryOperandFrame] using cursor.2
        obtain ⟨leftTypes, leftLive, leftAmbient, extend, acts, scopes, leftWorld, leftFinalSource, clear, observed, result⟩ :=
          leftIH fuel leftFrame before ambient types live world leftSource leftRoots middle rootMiddle leftChecked
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
            rightIH fuel rightFrame state ambient currentTypes currentLive currentWorld rightSource rightRoots typingAfter rootFinal rightChecked
          refine ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, ?_, clear, observed, result⟩
          exact currentSource.afterEarlierObservations acts scopes observed
        exact evalValue_binary_earlier_compose fuel config accepted frame before ambient types regions pending integer operation left right origin leftSafe rightSafe
  | @call argument target origin context callee parameter descriptor summary bodyExpression contextAt calleeAt parameters mode declared descriptorType results known body bodyForm argumentForm ih =>
    apply evalValue_singleArgument_fromOperand fuel frame before ambient types live regions pending target origin context callee parameter descriptor
      argument integer world source contextAt calleeAt parameters mode declared descriptorType results roots typingAfter rootsAfter checked
    · intro bodyFuel argumentState argumentTypes argumentLive argumentAmbient value represented argumentWorld argumentSource
      have parameterAt : callee.params[0]? = some parameter := by simp [parameters]
      have parameterId := validated_parameter_variable config.module context.impl callee 0 parameter accepted.accepted calleeAt parameterAt
      have declared0 : callee.vars[0]? = some descriptor := by simpa [parameterId] using declared
      have pointers : PointerTypedValue argumentTypes (.int integer) value := by
        cases represented with
        | integer _ number => exact .integer integer number
        | stored _ _ nonfixed _ => cases nonfixed
      exact scalarParameterBody_parameterSummary_partial bodyFuel config accepted frame argumentState argumentAmbient argumentTypes argumentLive
        regions pending target origin context callee parameter descriptor argument bodyExpression value (.int integer) summary contextAt calleeAt
        parameters declared0 body bodyForm (Or.inl ⟨integer, descriptorType⟩) descriptorType represented pointers known results argumentWorld argumentSource
        (.int integer) roots typingAfter rootsAfter checked
    · intro checkFuel argumentRoots argumentTypingAfter argumentRootsAfter depth operandSource operandChecked inner
      exact ih inner (ordinaryOperandFrame frame checkFuel) before ambient types live world operandSource argumentRoots
        argumentTypingAfter argumentRootsAfter operandChecked

#print axioms evalValue_nestedScalarCall
#print axioms nestedScalarCall_cursor
end Goose.Proofs.ConstructionAcceptedExecution
