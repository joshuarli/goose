import Goose.Proofs.ConstructionAcceptedUnaryCallComplete
import Goose.Proofs.ConstructionAcceptedRecursiveCallCursor
import Goose.Proofs.ConstructionAcceptedRecursiveCallRootCursor
import Goose.Proofs.ConstructionAcceptedNestedCursor

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

theorem checkedUnaryRegister_cursor {config : EvalConfig} {integer : Goose.Core.IntTy} {expression : Expr}
    (form : UnaryRegisterExpression config integer expression) (frame : ConstructionSourceFrame)
    (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (typingModule : frame.typing.module = config.module) (rootModule : frame.source.mod = config.module)
    (requests : frame.typing.resultRequests = [] ∨ frame.typing.resultRequests = [.register])
    (checked : CheckedValue frame expression (.int integer) roots typingAfter rootsAfter) :
    typingAfter = frame.typingCounter ∧ rootsAfter.nextVar = frame.rootCursor.nextVar := by
  induction form generalizing frame roots typingAfter rootsAfter with
  | scalar form => exact checked_binary_recursive_cursor form frame _ roots typingAfter rootsAfter checked
  | call target origin context callee contextAt calleeAt parameters results =>
    have rootContext : frame.source.mod.contexts[target]? = some context := by simpa [rootModule] using contextAt
    have rootCallee : frame.source.mod.impls[context.impl]? = some callee := by simpa [rootModule] using calleeAt
    have rootCursor := rpExpr_zeroArgument_nextVar rootContext rootCallee parameters checked.provenance
    cases depth : frame.typingFuel with
    | zero =>
      have typed := checked.typing
      rw [depth] at typed
      change Except.error _ = Except.ok _ at typed
      cases typed
    | succ n =>
      cases n with
      | zero =>
        have typed := checked.typing
        rw [depth] at typed
        simp only [typeExpr, typingModule, contextAt, calleeAt, typeArguments, bind, StateT.bind, Except.bind] at typed
        change Except.error _ = Except.ok _ at typed
        cases typed
      | succ n =>
        have typingContext : frame.typing.module.contexts[target]? = some context := by simpa [typingModule] using contextAt
        have typingCallee : frame.typing.module.impls[context.impl]? = some callee := by simpa [typingModule] using calleeAt
        have cursor := typeExpr_zeroArgumentRegisterCall_cursor n frame.typing target origin context callee (.int integer)
          frame.typingCounter typingAfter [.int integer] typingContext typingCallee parameters results (Or.inl ⟨integer, rfl⟩) requests
          (by simpa [depth] using checked.typing)
        exact ⟨cursor, rootCursor⟩
  | unary operation expression origin operand ih =>
    cases depth : frame.typingFuel with
    | zero =>
      have typed := checked.typing
      rw [depth] at typed
      change Except.error _ = Except.ok _ at typed
      cases typed
    | succ n =>
      obtain ⟨operandInteger, operandRoots, operandAfter, sameTy, sameRoots, operandChecked⟩ :=
        checkedValue_un_operand frame n operation expression origin (.int integer) roots typingAfter rootsAfter depth checked
      have sameInteger : integer = operandInteger := Ty.int.inj sameTy
      subst operandInteger
      obtain ⟨otherRoots, otherAfter, otherRooted, nextVar⟩ := rpExpr_un_nextVar frame.source operation expression origin
        frame.rootCursor rootsAfter roots checked.provenance
      have same : operandAfter = otherAfter := by
        have pair := operandChecked.provenance.symm.trans otherRooted
        exact (Prod.mk.inj (Except.ok.inj pair)).2
      subst otherAfter
      have facts := ih (ordinaryOperandFrame frame n) operandRoots typingAfter operandAfter
        (by simpa [ordinaryOperandFrame] using typingModule) (by simpa [ordinaryOperandFrame] using rootModule)
        (by simp [ordinaryOperandFrame]) operandChecked
      exact ⟨by simpa [ordinaryOperandFrame] using facts.1,
        nextVar.trans (by simpa [ordinaryOperandFrame] using facts.2)⟩

#print axioms checkedUnaryRegister_cursor
end Goose.Proofs.ConstructionAcceptedExecution
