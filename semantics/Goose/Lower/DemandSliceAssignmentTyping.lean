import Goose.Lower.DemandSliceAssignmentStopped
import Goose.Lower.Validation.ExpressionTypingSliceOps
import Goose.Lower.Validation.SourceStatementTypingStorage

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Lower.Validation

theorem StmtSource.sliceAssignment_reference {cfg : Cfg} {env : Env} {state : St}
    {reference : Expr} {mutability : Mutability} {global : GlobalId} {sliceOrigin origin : OriginId}
    {intType : IntTy} {number : Int}
    (source : StmtSource cfg env (.assign (.deref reference)
      (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin) origin) state) :
    ∃ ty, sliceRefTy source.typingEnv reference = some ty := by
  obtain ⟨info, childStart, placed, valueTyped, shape, writable, output⟩ := tyStmt_assign_children source.typed
  obtain ⟨element, writableView, viewStart, viewFinish, lowFinish, highFinish, viewTyped, lowTyped, highTyped, valueShape⟩ :=
    tyExpr_slice_children valueTyped
  have flat : element.flat = true := by
    rw [valueShape] at shape
    simp only [Ty.flat, Ty.isSlice, Bool.false_or, Bool.and_eq_true] at shape
    exact shape.1
  cases special : sliceRefTy source.typingEnv reference with
  | some ty => exact ⟨ty, rfl⟩
  | none =>
    simp only [tyPlace, special] at placed
    obtain ⟨referent, next, input, rest⟩ := (st_bind_ok _ _ _ _).mp placed
    obtain ⟨childTy, childFinish, childTyped, input⟩ := (st_bind_ok _ _ _ _).mp input
    by_cases referenceSlice : childTy.isRefSlice = true
    · simp [referenceSlice, chk] at input
    · simp only [referenceSlice] at input
      have same : referent = childTy := congrArg Prod.fst ((st_pure_ok _ _ _).mp input)
      subst referent
      cases childTy with
      | ref mu target =>
        have pair := (st_pure_ok _ _ _).mp rest
        have targetShape : info.ty = target := congrArg (fun pair => pair.1.ty) pair
        rw [valueShape] at targetShape
        subst target
        simp [Ty.isRefSlice, flat] at referenceSlice
      | _ => exact ((rej_ok _ _ _ _).mp rest).elim

#print axioms StmtSource.sliceAssignment_reference
theorem accepted_generated_slice_assignment_accepted_stopped_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) (reference : Expr) (mutability : Mutability) (global : GlobalId)
    (intType : IntTy) (number : Int) (sliceOrigin origin : OriginId) :
    GeneratedStoppedStatementPrefixFamily cx results selected loop (.assign (.deref reference)
      (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin) origin) :=
  accepted_generated_slice_assignment_stopped_family selected loop reference mutability global intType number sliceOrigin origin
    (fun source => source.sliceAssignment_reference)

#print axioms accepted_generated_slice_assignment_accepted_stopped_family
end Goose.Lower
