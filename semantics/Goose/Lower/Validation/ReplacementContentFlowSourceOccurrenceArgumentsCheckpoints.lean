import Goose.Lower.Validation.DeadFrontier

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR

theorem lowerArgs_append_run (earlier later : List Arg) (env : LEnv) (initial : LS) :
    lowerArgs (earlier ++ later) env initial =
      let first := lowerArgs earlier env initial
      let last := lowerArgs later env first.2
      (first.1 ++ last.1, last.2) := by
  induction earlier generalizing initial with
  | nil => simp only [List.nil_append, lowerArgs, pure_run, List.nil_append]
  | cons argument rest ih =>
    simpa only [List.cons_append, lowerArgs, bind_run, pure_run] using
      congrArg (fun result : List ValueId × LS =>
        ((lowerArg argument env initial).1 :: result.1, result.2))
        (ih (lowerArg argument env initial).2)

theorem lowerArgs_argument_checkpoint {arguments : List Arg} {argument : Arg}
    {index : Nat} (selected : arguments[index]? = some argument) (env : LEnv) (initial : LS) :
    ∃ earlier later,
      arguments = earlier ++ argument :: later ∧ earlier.length = index ∧
      (lowerArgs arguments env initial).1[index]? =
        some (lowerArg argument env (lowerArgs earlier env initial).2).1 ∧
      (lowerArgs later env (lowerArg argument env (lowerArgs earlier env initial).2).2).2 =
        (lowerArgs arguments env initial).2 ∧
      (lowerArg argument env (lowerArgs earlier env initial).2).2.Adv
        (lowerArgs arguments env initial).2 := by
  induction arguments generalizing initial index with
  | nil => simp at selected
  | cons first rest ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at selected
      subst argument
      refine ⟨[], rest, rfl, rfl, ?_, ?_, ?_⟩
      · rfl
      · rfl
      · exact advB_lowerArgs rest env (lowerArg first env initial).2 _ _ rfl
    | succ index =>
      simp only [List.getElem?_cons_succ] at selected
      obtain ⟨earlier, later, split, length, value, finish, advance⟩ :=
        ih selected (lowerArg first env initial).2
      refine ⟨first :: earlier, later, by simp [split], by simp [length], ?_, ?_, ?_⟩
      · simpa only [lowerArgs, bind_run, pure_run, List.getElem?_cons_succ] using value
      · simpa only [lowerArgs, bind_run, pure_run] using finish
      · simpa only [lowerArgs, bind_run, pure_run] using advance

theorem lowerArgs_argument_checkpoint_live {arguments : List Arg} {argument : Arg}
    {index : Nat} (selected : arguments[index]? = some argument) (env : LEnv) (initial : LS)
    (live : (lowerArgs arguments env initial).2.cur.isSome = true) :
    ∃ earlier later,
      arguments = earlier ++ argument :: later ∧ earlier.length = index ∧
      (lowerArgs arguments env initial).1[index]? =
        some (lowerArg argument env (lowerArgs earlier env initial).2).1 ∧
      (lowerArg argument env (lowerArgs earlier env initial).2).2.Adv
        (lowerArgs arguments env initial).2 ∧
      (lowerArgs earlier env initial).2.cur.isSome = true ∧
      (lowerArg argument env (lowerArgs earlier env initial).2).2.cur.isSome = true := by
  obtain ⟨earlier, later, split, length, value, finish, advance⟩ :=
    lowerArgs_argument_checkpoint selected env initial
  have suffixLive :
      (lowerArgs later env (lowerArg argument env (lowerArgs earlier env initial).2).2).2.cur.isSome = true := by
    rw [finish]
    exact live
  have childLive := (dead_lowerArgs later).live_before rfl suffixLive
  exact ⟨earlier, later, split, length, value, advance,
    (dead_lowerArg argument).live_before rfl childLive, childLive⟩

theorem lowerArgs_argument_run {arguments : List Arg} {argument : Arg}
    {index : Nat} {env : LEnv} {initial final : LS} {values : List ValueId} {value : ValueId}
    (run : lowerArgs arguments env initial = (values, final))
    (sourceRow : arguments[index]? = some argument) (nativeRow : values[index]? = some value) :
    ∃ earlier later after,
      arguments = earlier ++ argument :: later ∧ earlier.length = index ∧
      lowerArg argument env (lowerArgs earlier env initial).2 = (value, after) ∧
      (lowerArgs later env after).2 = final ∧ after.Adv final := by
  obtain ⟨earlier, later, split, length, selected, suffix, advance⟩ :=
    lowerArgs_argument_checkpoint sourceRow env initial
  have identity : value = (lowerArg argument env (lowerArgs earlier env initial).2).1 := by
    rw [run, nativeRow] at selected
    exact Option.some.inj selected
  subst value
  refine ⟨earlier, later, (lowerArg argument env (lowerArgs earlier env initial).2).2,
    split, length, rfl, ?_, ?_⟩
  · simpa only [run] using suffix
  · simpa only [run] using advance

#print axioms lowerArgs_append_run
#print axioms lowerArgs_argument_checkpoint
#print axioms lowerArgs_argument_checkpoint_live
#print axioms lowerArgs_argument_run

end Goose.Lower.Validation.ReplacementContentFlowSource
