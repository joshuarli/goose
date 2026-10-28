import Goose.Proofs.ConstructionAcceptedUnaryRegisterCursor
import Goose.Proofs.ConstructionAcceptedEarlierBinaryCompose

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem evalValue_binary_unaryRegister (fuel : Nat) (config : EvalConfig) (integer : Goose.Core.IntTy)
    (accepted : AcceptedModule config) (frame : ConstructionSourceFrame) (before : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (operation : Goose.Core.BinOp) (left right : Expr) (origin : Nat)
    (leftForm : UnaryRegisterExpression config integer left) (rightForm : UnaryRegisterExpression config integer right)
    (graph : RegisterCallGraphWithCallLocals config (.int integer))
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types)
    (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue frame (.bin operation left right origin) (.int integer) roots typingAfter rootsAfter) :
    EarlierScalarOutcome config accepted frame before ambient types regions pending (.int integer)
      (evalValue fuel config frame.interpretation.environment (.bin operation left right origin) before) := by
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
      have cursor := checkedUnaryRegister_cursor leftForm leftFrame leftRoots middle rootMiddle
        (by simpa [leftFrame, ordinaryOperandFrame] using source.compatible.module)
        (by simpa [leftFrame, ordinaryOperandFrame] using source.compatible.rootModule)
        (by simp [leftFrame, ordinaryOperandFrame]) leftChecked
      have sameCounter : middle = frame.typingCounter := by simpa [leftFrame, ordinaryOperandFrame] using cursor.1
      have sameRoot : rootMiddle.nextVar = frame.rootCursor.nextVar := by simpa [leftFrame, ordinaryOperandFrame] using cursor.2
      have leftSource := ordinaryOperandFrame_accepted accepted frame checkFuel before types source
      obtain ⟨leftTypes, leftLive, leftAmbient, extend, acts, scopes, leftWorld, leftFinalSource, clear, observed, result⟩ :=
        evalValue_unaryRegisterExpression config integer leftForm fuel accepted leftFrame before ambient types live regions pending graph
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
          evalValue_unaryRegisterExpression config integer rightForm fuel accepted rightFrame state ambient currentTypes currentLive regions pending graph
            currentWorld rightSource rightRoots typingAfter rootFinal rightChecked
        refine ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, ?_, clear, observed, result⟩
        exact currentSource.afterEarlierObservations acts scopes observed
      exact evalValue_binary_earlier_compose fuel config accepted frame before ambient types regions pending integer operation left right origin leftSafe rightSafe

#print axioms evalValue_binary_unaryRegister
end Goose.Proofs.ConstructionAcceptedExecution
