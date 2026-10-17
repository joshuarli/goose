import Goose.Lower.Validation.SourceReplacementWriterLedgerChildTypesExpressions
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlGraphExtensions
import Goose.Lower.Validation.SummaryPreservationLowerIfE

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR ReplacementContentFlowSource SummaryPreservation

theorem setCur_extension_types (current : Option BlockId) (env : LEnv) (before : LS) :
    TypePrefix before (setCur current env before).2 := types_setCur current env before _ _ rfl

theorem Fragment.finish_ext_types (fragment : Fragment) (env : LEnv) (before : LS) :
    TypePrefix before (fragment.finish env before) := by
  cases fragment with
  | expression expression => exact (types_lowerExpr expression env before _ _ rfl)
  | place place => exact (types_lowerPlace place env before _ _ rfl)
  | view view => exact (types_lowerView view env before _ _ rfl)
  | bound bound => exact (types_lowerBound bound env before _ _ rfl)
  | statement loop statement => exact (types_lowerStmt loop statement env before _ _ rfl)
  | block loop bindings want block => exact (types_lowerBlock loop bindings want block env before _ _ rfl)

theorem shortCircuitChild_span_types {env : LEnv} {before start : LS} {isAnd : Bool} {left : ValueId}
    {right : Expr} {child : Fragment}
    (row : shortCircuitChild env before isAnd left right = some (child, start)) :
    TypePrefix before start ∧ TypePrefix (child.finish env start) (shortCircuit isAnd left (lowerExpr right) env before).2 := by
  unfold shortCircuitChild at row
  split at row
  · rename_i live
    let split := scFork isAnd left env before
    let entry := (setCur (some split.1.1) env split.2).2
    have same : (.expression right, entry) = (child, start) := Option.some.inj row
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
    have entrySpan : TypePrefix before entry :=
      (types_scFork isAnd left env before _ _ rfl).trans (setCur_extension_types _ _ _)
    obtain ⟨current, currentAt⟩ := Option.isSome_iff_exists.mp live
    have whole : (shortCircuit isAnd left (lowerExpr right) env before).2 =
        (setCur (some split.1.2.1) env
          (emitTerm (.br split.1.2.1 [(lowerExpr right env entry).1]) env (lowerExpr right env entry).2).2).2 := by
      simp only [shortCircuit, whenLive_some _ _ _ currentAt, bind_run, split, entry, pure_run]
    refine ⟨entrySpan, ?_⟩
    rw [whole]
    exact (types_emitTerm _ env _ _ _ rfl).trans (setCur_extension_types _ _ _)
  · simp at row

theorem Fragment.shortCircuit_child_span_types (isAnd : Bool) {left right : Expr} {child : Fragment}
    {env : LEnv} {before start : LS} {index : Nat}
    (row : (Fragment.expression (if isAnd then .and left right else .or left right)).child? env before index = some (child, start)) :
    TypePrefix before start ∧ TypePrefix (child.finish env start)
      ((Fragment.expression (if isAnd then .and left right else .or left right)).finish env before) := by
  have member := Fragment.child_member row
  have children : (Fragment.expression (if isAnd then .and left right else .or left right)).children env before =
      [some (.expression left, before), shortCircuitChild env (lowerExpr left env before).2 isAnd
        (lowerExpr left env before).1 right] := by cases isAnd <;> rfl
  rw [children] at member
  have whole : ((Fragment.expression (if isAnd then .and left right else .or left right)).finish env before) =
      (shortCircuit isAnd (lowerExpr left env before).1 (lowerExpr right) env (lowerExpr left env before).2).2 := by
    cases isAnd <;> rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
    rw [whole]
    exact ⟨.refl _, (types_shortCircuit isAnd _ (types_lowerExpr right) env _ _ _ rfl)⟩
  · have span := shortCircuitChild_span_types same.symm
    exact ⟨(types_lowerExpr left env before _ _ rfl).trans span.1, whole ▸ span.2⟩

theorem Fragment.ifE_child_span_types {condition : Expr} {yes no : Core.Block} {child : Fragment}
    {env : LEnv} {before start : LS} {index : Nat}
    (row : (Fragment.expression (.ifE condition yes no)).child? env before index = some (child, start)) :
    TypePrefix before start ∧ TypePrefix (child.finish env start) ((Fragment.expression (.ifE condition yes no)).finish env before) := by
  have member := Fragment.child_member row
  simp only [Fragment.children, List.mem_cons] at member
  rcases member with same | member
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
    exact ⟨.refl _, bind_suffix_ext_types (lowerExpr condition) _
      (fun value => types_ifE_core value (sourceBlockScope yes) (types_lowerBlock none [] true yes)
        (types_lowerBlock none [] true no)) env _⟩
  · unfold branchChildren at member
    split at member
    · rename_i live
      let tested := lowerExpr condition env before
      let split := fork tested.1 env tested.2
      let yesStart := (setCur (some split.1.1) env split.2).2
      let yesOut := lowerBlock none [] true yes env yesStart
      let noStart := (setCur (some split.1.2) env yesOut.2).2
      let noOut := lowerBlock none [] true no env noStart
      let joined := joinValue yesOut.2.cur yesOut.1 noOut.2.cur noOut.1 env noOut.2
      have prefixYes : TypePrefix before yesStart := (types_lowerExpr condition env before _ _ rfl).trans
        ((types_fork tested.1 env tested.2 _ _ rfl).trans (setCur_extension_types _ _ _))
      have between : TypePrefix yesOut.2 noStart := setCur_extension_types _ _ _
      have suffix : TypePrefix noOut.2 ((Fragment.expression (.ifE condition yes no)).finish env before) := by
        obtain ⟨current, currentAt⟩ := Option.isSome_iff_exists.mp live
        have whole := lowerExpr_ifE_after_branches (le := env) (condition := condition) (yes := yes) (no := no)
          (rfl : lowerExpr condition env before = tested) currentAt
          (rfl : fork tested.1 env tested.2 = split)
          (rfl : lowerBlock none [] true yes env yesStart = yesOut)
          (rfl : lowerBlock none [] true no env noStart = noOut)
        change TypePrefix noOut.2 (lowerExpr (.ifE condition yes no) env before).2
        rw [whole]
        exact (types_joinValue _ _ _ _ env noOut.2 _ _ rfl).trans
          (types_recordValueRootRecipe joined.1 (sourceBlockScope yes) env joined.2 _ _ rfl)
      change some (child, start) ∈ [some (.block none [] true yes, yesStart), some (.block none [] true no, noStart)] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same
      · obtain ⟨rfl, same⟩ := Prod.mk.inj (Option.some.inj same)
        subst start
        exact ⟨prefixYes, between.trans ((types_lowerBlock none [] true no env noStart _ _ rfl).trans suffix)⟩
      · obtain ⟨rfl, same⟩ := Prod.mk.inj (Option.some.inj same)
        subst start
        exact ⟨prefixYes.trans ((types_lowerBlock none [] true yes env yesStart _ _ rfl).trans between), suffix⟩
    · simp at member

theorem Fragment.blockE_child_span_types {block : Core.Block} {child : Fragment}
    {env : LEnv} {before start : LS} {index : Nat}
    (row : (Fragment.expression (.blockE block)).child? env before index = some (child, start)) :
    TypePrefix before start ∧ TypePrefix (child.finish env start) ((Fragment.expression (.blockE block)).finish env before) := by
  have member := Fragment.child_member row
  simp only [Fragment.children, List.mem_singleton] at member
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj member)
  exact ⟨.refl _, .refl _⟩

#print axioms Fragment.shortCircuit_child_span_types
#print axioms Fragment.ifE_child_span_types
#print axioms Fragment.blockE_child_span_types

end Goose.Lower.Validation.SourceReplacementWriterLedger
