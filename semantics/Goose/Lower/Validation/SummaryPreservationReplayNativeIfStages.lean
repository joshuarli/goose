import Goose.Lower.Validation.SummaryPreservationReplayNativeTypes
import Goose.Lower.Validation.SummaryPreservationLowerIfE

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

theorem native_if_condition {vt : Array (Option VTy)} {condition : Expr} {yes no : Core.Block}
    {le : LEnv} {initial : LS}
    (native : NativeRows vt (lowerExpr (.ifE condition yes no) le initial).2) :
    NativeRows vt (lowerExpr condition le initial).2 :=
  native.of_prefix (types_ifE_core (lowerExpr condition le initial).1
    (sourceBlockScope yes) (types_lowerBlock none [] true yes) (types_lowerBlock none [] true no)
    le (lowerExpr condition le initial).2 _ _ rfl)

theorem native_if_branches {vt : Array (Option VTy)} {condition : Expr} {yes no : Core.Block}
    {le : LEnv} {initial : LS}
    (generated : GeneratedBuilderState initial)
    (native : NativeRows vt (lowerExpr (.ifE condition yes no) le initial).2)
    (live : (lowerExpr condition le initial).2.cur.isSome = true) :
    let lowered := lowerExpr condition le initial
    let forked := (fork lowered.1 le lowered.2).2
    let yesStart := { forked with cur := some lowered.2.blocks.size }
    let yesResult := lowerBlock none [] true yes le yesStart
    let noStart := { yesResult.2 with cur := some (lowered.2.blocks.size + 1) }
    GeneratedBuilderState yesStart ∧ GeneratedBuilderState noStart ∧
      NativeRows vt yesResult.2 ∧ NativeRows vt (lowerBlock none [] true no le noStart).2 := by
  dsimp only
  let lowered := lowerExpr condition le initial
  let forked := (fork lowered.1 le lowered.2).2
  let yesStart := { forked with cur := some lowered.2.blocks.size }
  let yesResult := lowerBlock none [] true yes le yesStart
  let noStart := { yesResult.2 with cur := some (lowered.2.blocks.size + 1) }
  let noResult := lowerBlock none [] true no le noStart
  obtain ⟨block, current⟩ := Option.isSome_iff_exists.mp live
  have selected : lowered.2.cur = some block := current
  have forkSize : forked.blocks.size = lowered.2.blocks.size + 2 := by
    simp [forked, fork_run _ _ selected]
  have conditionGenerated := generated.lowerExpr condition (rfl : lowerExpr condition le initial = lowered)
  have forkGenerated := conditionGenerated.fork lowered.1 (rfl : fork lowered.1 le lowered.2 = ((fork lowered.1 le lowered.2).1, forked))
  have yesGenerated : GeneratedBuilderState yesStart := by
    apply forkGenerated.setCur (env := le) (some lowered.2.blocks.size) _ rfl
    intro target row
    cases row
    change lowered.2.blocks.size < forked.blocks.size
    rw [forkSize]
    omega
  have yesResultGenerated := yesGenerated.lowerBlock none [] true yes trivial
    (rfl : lowerBlock none [] true yes le yesStart = yesResult)
  have yesGrowth := advB_lowerBlock none [] true yes le yesStart yesResult.1 yesResult.2 rfl
  have noGenerated : GeneratedBuilderState noStart := by
    apply yesResultGenerated.setCur (env := le) (some (lowered.2.blocks.size + 1)) _ rfl
    intro target row
    cases row
    apply Nat.lt_of_lt_of_le (m := yesStart.blocks.size) _ yesGrowth.ext.1
    change lowered.2.blocks.size + 1 < forked.blocks.size
    rw [forkSize]
    omega
  have whole : lowerExpr (.ifE condition yes no) le initial =
      (Goose.Lower.joinValue yesResult.2.cur yesResult.1 noResult.2.cur noResult.1 >>= fun value => do
        recordValueRootRecipe value (sourceBlockScope yes)
        pure value) le noResult.2 := by
    apply lowerExpr_ifE_after_branches (rfl : lowerExpr condition le initial = lowered) selected
      (forked := forked) (yesLS := yesResult.2) (noLS := noResult.2)
      (yesBlock := lowered.2.blocks.size) (noBlock := lowered.2.blocks.size + 1)
    · change fork lowered.1 le lowered.2 = ((lowered.2.blocks.size, lowered.2.blocks.size + 1), forked)
      simp only [forked, fork_run _ _ selected]
    · rfl
    · rfl
  have noNative : NativeRows vt noResult.2 := by
    apply native.of_prefix
    rw [whole]
    exact (TypeRun.bind (types_joinValue yesResult.2.cur yesResult.1 noResult.2.cur noResult.1) fun value =>
      TypeRun.bind (types_recordValueRootRecipe value (sourceBlockScope yes)) fun _ =>
        TypeRun.pure value) le noResult.2 _ _ rfl
  have yesNative : NativeRows vt yesResult.2 :=
    noNative.of_prefix ((types_setCur (some (lowered.2.blocks.size + 1)) le yesResult.2 _ _ rfl).trans
      (types_lowerBlock none [] true no le noStart noResult.1 noResult.2 rfl))
  exact ⟨yesGenerated, noGenerated, yesNative, noNative⟩

#print axioms native_if_condition
#print axioms native_if_branches

end Goose.Lower.Validation.SummaryPreservation
