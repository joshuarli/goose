import Goose.Lower.Validation.SourceRootShape
import Goose.Lower.Validation.ExpressionTypingCallOps
import Goose.Lower.Validation.SummaryPreservationArgumentReplay
import Goose.Lower.Validation.SummaryPreservationReplayArgumentSource

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

theorem sourceScalarArgRoots {typingEnv : TEnv} {env : PEnv} {callee : Impl}
    (tables : SourceRootTables typingEnv env) (parameters : List Param)
    {arguments : List Arg} {argumentRoots : List (List RootRef)}
    {start finish : Nat} {before after : RState}
    (typed : Core.tyArgs typingEnv callee parameters arguments start = .ok ((), finish))
    (replayed : Core.rpArgs env arguments before = .ok (argumentRoots, after))
    {index : Nat} {parameter : Param} {localVar : LocalVar}
    (parameterAt : parameters[index]? = some parameter)
    (variableAt : callee.vars[parameter.var]? = some localVar)
    (scalar : localVar.ty.isRefLike = false) :
    argumentRoots[index]?.getD [] = [] := by
  induction parameters generalizing arguments argumentRoots start before index with
  | nil => simp at parameterAt
  | cons head rest ih =>
    cases arguments with
    | nil =>
      have empty : argumentRoots = [] := congrArg Prod.fst ((st_pure_ok _ _ _).mp replayed)
      simp [empty]
    | cons argument arguments =>
      obtain ⟨roots, middle, remaining, firstReplay, restReplay, rfl⟩ := rpArgs_cons_contract replayed
      cases index with
      | zero =>
        have same : head = parameter := by simpa using parameterAt
        subst head
        cases argument with
        | byVal expression =>
          obtain ⟨found, type, childStart, childFinish, _, row, childTyped, passable, _⟩ := tyArgs_byVal_head typed
          rw [variableAt] at row
          cases row
          have nonref := (source_passable_refLike_eq passable).trans scalar
          have empty := source_expression_nonref_roots_empty expression tables childTyped nonref firstReplay
          simp [empty]
        | byRef mutability place =>
          obtain ⟨found, info, childFinish, _, row, childTyped, _, passable, _⟩ := tyArgs_byRef_head typed
          rw [variableAt] at row
          cases row
          have impossible := (source_passable_refLike_eq passable).trans scalar
          simp [Ty.isRefLike] at impossible
      | succ index =>
        obtain ⟨next, _, tailTyped⟩ := tyArgs_cons_children typed
        exact ih tailTyped restReplay (by simpa using parameterAt)

end Goose.Lower.Validation.ReplacementContentFlowSource
