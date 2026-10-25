import Goose.Lower.Validation.SourceReplacementWriterLedgerCoverageActions

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR

def ChildRowsCovered (property : Inst → Prop) (env : LEnv) (rows : List Child) : Prop :=
  ∀ child start, some (child,start) ∈ rows → EmitsOnly property start (child.finish env start)

theorem ChildrenCovered.rows {property : Inst → Prop} {fragment : Fragment} {env : LEnv} {before : LS}
    (children : ChildrenCovered property fragment env before) :
    ChildRowsCovered property env (fragment.children env before) := by
  intro child start member
  obtain ⟨index, row⟩ := List.mem_iff_getElem?.mp member
  exact children.at_index index (by simp only [Fragment.child?, row, Option.join_some])

theorem expressionChildren_covered {property : Inst → Prop} {env : LEnv} {before : LS}
    {expressions : List Expr} (children : ChildRowsCovered property env (expressionChildren env expressions before)) :
    At property env before (lowerExprs expressions) := by
  induction expressions generalizing before with
  | nil => exact At.pure _ _ _ _
  | cons expression expressions ih =>
    unfold lowerExprs
    apply At.bind
    · exact children (.expression expression) before (List.mem_cons_self)
    · apply At.bind
      · apply ih
        intro child start member
        exact children child start (List.mem_cons_of_mem _ member)
      · exact At.pure _ _ _ _

theorem argumentChildren_covered {property : Inst → Prop} {env : LEnv} {before : LS}
    {arguments : List Arg}
    (neutral : ∀ instruction, NeutralInstruction instruction → property instruction)
    (children : ChildRowsCovered property env (argumentChildren env arguments before)) :
    At property env before (lowerArgs arguments) := by
  induction arguments generalizing before with
  | nil => exact At.pure _ _ _ _
  | cons argument arguments ih =>
    unfold lowerArgs
    apply At.bind
    · cases argument with
      | byVal expression => exact children (.expression expression) before (List.mem_cons_self)
      | byRef mutability place =>
        unfold lowerArg
        apply At.bind
        · exact children (.place place) before (List.mem_cons_self)
        · exact At.neutral neutral (neutral_borrowTo _ _)
    · apply At.bind
      · apply ih
        intro child start member
        exact children child start (List.mem_cons_of_mem _ member)
      · exact At.pure _ _ _ _

theorem printChildren_covered {property : Inst → Prop} {env : LEnv} {before : LS}
    {arguments : List PrintArg}
    (children : ChildRowsCovered property env (printChildren env arguments before)) :
    At property env before (lowerPrintArgs arguments) := by
  induction arguments generalizing before with
  | nil => exact At.pure _ _ _ _
  | cons argument arguments ih =>
    cases argument with
    | text text =>
      unfold lowerPrintArgs
      apply At.bind
      · apply ih
        intro child start member
        exact children child start (List.mem_cons_of_mem _ member)
      · exact At.pure _ _ _ _
    | expr expression =>
      unfold lowerPrintArgs
      apply At.bind
      · exact children (.expression expression) before (List.mem_cons_self)
      · apply At.bind
        · apply ih
          intro child start member
          exact children child start (List.mem_cons_of_mem _ member)
        · exact At.pure _ _ _ _

#print axioms expressionChildren_covered
#print axioms argumentChildren_covered
#print axioms printChildren_covered

end Goose.Lower.Validation.SourceReplacementWriterLedger
