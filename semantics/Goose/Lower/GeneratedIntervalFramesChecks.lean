import Goose.Lower.GeneratedIntervalFramesFunctions
import Goose.Core.Validate

namespace Goose.Lower.GeneratedIntervalFramesChecks
open Goose.Core Goose.GIR Goose.Lower.Validation
private def ownerType : Ty := .growshrink (.int .i64)
private def replacement : Expr := .ifE (.bool true)
  (.mk 2 [] (some (.arrLit ownerType []))) (.mk 3 [] (some (.arrLit ownerType [])))
private def expression : Expr := .and (.bool true)
  (.blockE (.mk 1 [.assignWhole (.global 0) replacement 0] (some (.bool true))))
private def main : Core.Impl :=
  { name := "main", params := #[], results := #[], vars := #[],
    body := .mk 0 [.expr expression 0] none, summary := .unknown }
private def module : Core.Module :=
  { files := #["replacement-continuation"], types := #[],
    globals := #[⟨"owner", ownerType, .mutable, .arrLit ownerType [], 0⟩],
    impls := #[main],
    contexts := #[⟨0, "main", [], [], []⟩], entry := 0,
    origins := #[⟨0, 1, "expr"⟩], profile := .shrink }
#guard (Core.validate module).toBool
private def env : LEnv := lowerEnv module #[] []
private def started : LS := (setCur (some 0) env (newBlock [] env initState).2).2
private def condition := lowerExpr (.bool true) env started
private def forked := scFork true condition.1 env condition.2
private def entered := setCur (some forked.1.1) env forked.2
private def scopedState : LS := (pushScope 1 env (emitEffect (.enter 1) env entered.2).2).2
private def addressed := lowerPlace (.global 0) env scopedState
private def cleared := (emitEffect (.clear addressed.1 (some 0)) env addressed.2).2
private def captured := lowerExpr replacement env cleared
private def finished := (lowerExpr expression env started).2
private def hasTerm (term : Term) (inst : Inst) : Bool :=
  match term, inst with
  | .br target args, .term (.br next values) => target == next && args == values
  | .condbr value left leftArgs right rightArgs, .term (.condbr other yes yesArgs no noArgs) =>
      value == other && left == yes && leftArgs == yesArgs && right == no && rightArgs == noArgs
  | _, _ => false

private def framedBetween (lower upper : Nat) (captured after : LS) : Bool :=
  after.blocks.toList.zipIdx.all fun (body, source) =>
    body.insts.toList.all fun inst => match inst with
      | .term term => term.successors.all fun target =>
          if lower ≤ target && target < upper then
            match captured.blocks[source]? with
            | some old => old.insts.toList.any (hasTerm term)
            | none => false
          else true
      | _ => true

private theorem hasTerm_sound {term : Term} {inst : Inst} (same : hasTerm term inst = true) : inst = .term term := by
  cases term <;> cases inst <;> simp only [hasTerm, Bool.false_eq_true] at same
  all_goals
    rename_i actual
    cases actual <;> simp [Bool.and_eq_true, beq_iff_eq] at same
    all_goals first
      | rcases same with ⟨rfl, rfl⟩; rfl
      | rcases same with ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩; rfl

private theorem framedBetween_sound {before captured after : LS}
    (checked : framedBetween before.blocks.size captured.blocks.size captured after = true) :
    IntervalEdgesFramed before captured after := by
  intro source body term target row member successor lower upper
  have pair : (body, source) ∈ after.blocks.toList.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr (by simpa using row)
  have atBody := List.all_eq_true.mp checked (body, source) pair
  have atTerm := List.all_eq_true.mp atBody (.term term) member
  have atTarget := List.all_eq_true.mp atTerm target successor
  simp only [show decide (before.blocks.size ≤ target) = true from decide_eq_true lower,
    show decide (target < captured.blocks.size) = true from decide_eq_true upper,
    Bool.and_self, ite_true] at atTarget
  cases found : captured.blocks[source]? with
  | none => simp [found] at atTarget
  | some old =>
    simp only [found] at atTarget
    obtain ⟨inst, oldMember, same⟩ := List.any_eq_true.mp atTarget
    exact ⟨old, rfl, (hasTerm_sound same) ▸ oldMember⟩

#guard cleared.blocks.size == 3
#guard captured.2.blocks.size == 6
#guard forked.1.2.1 < cleared.blocks.size
#guard framedBetween cleared.blocks.size captured.2.blocks.size captured.2 finished
#guard !(framedBetween 0 captured.2.blocks.size captured.2 finished)

#guard !(framedBetween cleared.blocks.size captured.2.blocks.size captured.2
  (patchTerm 5 (.br cleared.blocks.size []) env finished).2)

end Goose.Lower.GeneratedIntervalFramesChecks
