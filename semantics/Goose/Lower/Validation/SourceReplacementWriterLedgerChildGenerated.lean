import Goose.Lower.Validation.SourceReplacementWriterLedgerChildSpansControlsComplete
import Goose.Lower.GeneratedBuilder

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR

def Fragment.loopTargets : Fragment → LS → Prop
  | .statement loop _, state | .block loop _ _ _, state => LoopBuilderTargets loop state
  | _, _ => True

def ChildrenGenerated : List Child → Prop
  | [] => True
  | none :: rest => ChildrenGenerated rest
  | some (child, before) :: rest =>
      (GeneratedBuilderState before ∧ child.loopTargets before) ∧ ChildrenGenerated rest

theorem ChildrenGenerated.append {left right : List Child}
    (first : ChildrenGenerated left) (second : ChildrenGenerated right) : ChildrenGenerated (left ++ right) := by
  induction left with
  | nil => exact second
  | cons entry rest ih =>
    cases entry with
    | none => exact ih first
    | some pair => exact ⟨first.1, ih first.2⟩

theorem ChildrenGenerated.member {children : List Child} (checked : ChildrenGenerated children)
    {child : Fragment} {before : LS} (member : some (child, before) ∈ children) :
    GeneratedBuilderState before ∧ child.loopTargets before := by
  induction children with
  | nil => simp at member
  | cons entry rest ih =>
    cases entry with
    | none => exact ih checked (by simpa using member)
    | some pair =>
      rcases List.mem_cons.mp member with same | member
      · cases Option.some.inj same
        exact checked.1
      · exact ih checked.2 member

theorem expressionChildren_generated (env : LEnv) (expressions : List Expr) (before : LS)
    (checked : GeneratedBuilderState before) : ChildrenGenerated (expressionChildren env expressions before) := by
  induction expressions generalizing before with
  | nil => trivial
  | cons expression rest ih => exact ⟨⟨checked, trivial⟩, ih _ (checked.lowerExpr expression rfl)⟩

theorem argumentChildren_generated (env : LEnv) (arguments : List Arg) (before : LS)
    (checked : GeneratedBuilderState before) : ChildrenGenerated (argumentChildren env arguments before) := by
  induction arguments generalizing before with
  | nil => trivial
  | cons argument rest ih =>
    cases argument <;> exact ⟨⟨checked, trivial⟩, ih _ (checked.lowerArg _ rfl)⟩

theorem printChildren_generated (env : LEnv) (arguments : List PrintArg) (before : LS)
    (checked : GeneratedBuilderState before) : ChildrenGenerated (printChildren env arguments before) := by
  induction arguments generalizing before with
  | nil => trivial
  | cons argument rest ih =>
    cases argument with
    | text text => exact ih _ checked
    | expr expression => exact ⟨⟨checked, trivial⟩, ih _ (checked.lowerExpr expression rfl)⟩

theorem statementChildren_generated (env : LEnv) (loop : Option LoopCtx) (statements : List Stmt) (before : LS)
    (checked : GeneratedBuilderState before) (bounds : LoopBuilderTargets loop before) :
    ChildrenGenerated (statementChildren env loop statements before) := by
  induction statements generalizing before with
  | nil => trivial
  | cons statement rest ih =>
    simp only [statementChildren]
    split
    · exact ⟨⟨checked, bounds⟩, ih _ (checked.lowerStmt loop statement bounds rfl)
        (bounds.mono (advB_lowerStmt loop statement env before _ _ rfl).ext.1)⟩
    · exact ih _ checked bounds

theorem fork_entry_generated (condition : ValueId) (env : LEnv) (before : LS)
    (checked : GeneratedBuilderState before) :
    GeneratedBuilderState (setCur (some (fork condition env before).1.1) env (fork condition env before).2).2 := by
  obtain ⟨_, _, _, yesBound, noBound⟩ := adv_fork_step (.refl before)
    (rfl : fork condition env before = ((fork condition env before).1, (fork condition env before).2))
  exact (checked.fork condition (env := env) rfl).setCur _ (env := env) (by intro current same; cases Option.some.inj same; exact yesBound) rfl

theorem shortCircuitChild_generated (env : LEnv) (before : LS) (isAnd : Bool) (left : ValueId) (right : Expr)
    (checked : GeneratedBuilderState before) :
    ChildrenGenerated [shortCircuitChild env before isAnd left right] := by
  unfold shortCircuitChild
  split
  · rename_i live
    obtain ⟨current, currentAt⟩ := Option.isSome_iff_exists.mp live
    have rightBound : (scFork isAnd left env before).1.1 < (scFork isAnd left env before).2.blocks.size := by
      rw [scFork_run _ _ _ currentAt]
      simp
      exact Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_succ_self _)
    refine ⟨⟨(checked.scFork isAnd left (env := env) rfl).setCur _ (env := env) ?_ rfl, trivial⟩, trivial⟩
    intro target same
    cases Option.some.inj same
    exact rightBound
  · trivial

theorem branchChildren_generated (env : LEnv) (before : LS) (condition : ValueId)
    (loop : Option LoopCtx) (want : Bool) (yes : Core.Block) (no : Option Core.Block)
    (checked : GeneratedBuilderState before) (bounds : LoopBuilderTargets loop before) :
    ChildrenGenerated (branchChildren env before condition loop want yes no) := by
  unfold branchChildren
  split
  · have entered := fork_entry_generated condition env before checked
    have growth : before.Ext (setCur (some (fork condition env before).1.1) env (fork condition env before).2).2 := (advB_fork condition env before _ _ rfl).ext.trans (setCur_extension _ _ _)
    have nextBounds := bounds.mono growth.1
    refine ⟨⟨entered, nextBounds⟩, ?_⟩
    cases no with
    | none => trivial
    | some no =>
      have afterYes := entered.lowerBlock loop [] want yes nextBounds (env := env) rfl
      have afterGrowth := (advB_lowerBlock loop [] want yes env
        (setCur (some (fork condition env before).1.1) env (fork condition env before).2).2 _ _ rfl).ext
      have noBound := Nat.lt_of_lt_of_le (fork_entry_liveBound condition env before).2
        (by simpa only [setCur_run] using afterGrowth.1)
      refine ⟨⟨afterYes.setCur _ (env := env) ?_ rfl, ?_⟩, trivial⟩
      · intro target same
        cases Option.some.inj same
        exact noBound
      · exact nextBounds.mono (afterGrowth.trans (setCur_extension _ _ _)).1

  · trivial

#print axioms statementChildren_generated
#print axioms branchChildren_generated

end Goose.Lower.Validation.SourceReplacementWriterLedger
