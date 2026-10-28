import Goose.Proofs.ConstructionAcceptedUnaryRegisterCursor
import Goose.Proofs.ConstructionAcceptedEarlierBinaryCompose

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

inductive RegisterArithmeticExpression (config : EvalConfig) (integer : Goose.Core.IntTy) : Expr → Prop
  | operand {expression : Expr} : UnaryRegisterExpression config integer expression → RegisterArithmeticExpression config integer expression
  | binary {left right : Expr} (operation : Goose.Core.BinOp) (origin : Nat) :
      RegisterArithmeticExpression config integer left → RegisterArithmeticExpression config integer right →
      RegisterArithmeticExpression config integer (.bin operation left right origin)

theorem checkedRegisterArithmetic_cursor {config : EvalConfig} {integer : Goose.Core.IntTy} {expression : Expr}
    (form : RegisterArithmeticExpression config integer expression) (frame : ConstructionSourceFrame)
    (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (typingModule : frame.typing.module = config.module) (rootModule : frame.source.mod = config.module)
    (requests : frame.typing.resultRequests = [] ∨ frame.typing.resultRequests = [.register])
    (checked : CheckedValue frame expression (.int integer) roots typingAfter rootsAfter) :
    typingAfter = frame.typingCounter ∧ rootsAfter.nextVar = frame.rootCursor.nextVar := by
  induction form generalizing frame roots typingAfter rootsAfter with
  | operand form => exact checkedUnaryRegister_cursor form frame roots typingAfter rootsAfter typingModule rootModule requests checked
  | @binary left right operation origin leftForm rightForm leftIH rightIH =>
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
      have leftFacts := leftIH leftFrame leftRoots middle rootMiddle
        (by simpa [leftFrame, ordinaryOperandFrame] using typingModule) (by simpa [leftFrame, ordinaryOperandFrame] using rootModule)
        (by simp [leftFrame, ordinaryOperandFrame]) leftChecked
      have rightFacts := rightIH rightFrame rightRoots typingAfter rootFinal
        (by simpa [rightFrame, leftFrame, ordinaryOperandFrame] using typingModule)
        (by simpa [rightFrame, leftFrame, ordinaryOperandFrame] using rootModule)
        (by simp [rightFrame, leftFrame, ordinaryOperandFrame]) rightChecked
      have lastRoot := nestedBin_final_nextVar frame operation left right origin roots leftRoots rightRoots rootsAfter rootMiddle rootFinal
        checked.provenance leftChecked.provenance rightChecked.provenance
      exact ⟨by simpa [leftFrame, rightFrame, ordinaryOperandFrame] using rightFacts.1.trans leftFacts.1,
        lastRoot.trans (by simpa [leftFrame, rightFrame, ordinaryOperandFrame] using rightFacts.2.trans leftFacts.2)⟩

theorem evalValue_registerArithmetic (config : EvalConfig) (integer : Goose.Core.IntTy) {expression : Expr}
    (form : RegisterArithmeticExpression config integer expression) (fuel : Nat) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (graph : RegisterCallGraphWithCallLocals config (.int integer))
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types)
    (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue frame expression (.int integer) roots typingAfter rootsAfter) :
    EarlierScalarOutcome config accepted frame before ambient types regions pending (.int integer)
      (evalValue fuel config frame.interpretation.environment expression before) := by
  induction form generalizing fuel frame before ambient types live roots typingAfter rootsAfter with
  | operand form =>
    exact evalValue_unaryRegisterExpression config integer form fuel accepted frame before ambient types live regions pending graph
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
        have cursor := checkedRegisterArithmetic_cursor leftForm leftFrame leftRoots middle rootMiddle
          (by simpa [leftFrame, ordinaryOperandFrame] using source.compatible.module)
          (by simpa [leftFrame, ordinaryOperandFrame] using source.compatible.rootModule)
          (by simp [leftFrame, ordinaryOperandFrame]) leftChecked
        have sameCounter : middle = frame.typingCounter := by simpa [leftFrame, ordinaryOperandFrame] using cursor.1
        have sameRoot : rootMiddle.nextVar = frame.rootCursor.nextVar := by simpa [leftFrame, ordinaryOperandFrame] using cursor.2
        have leftSource := ordinaryOperandFrame_accepted accepted frame checkFuel before types source
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


#print axioms evalValue_registerArithmetic
#print axioms checkedRegisterArithmetic_cursor
end Goose.Proofs.ConstructionAcceptedExecution
