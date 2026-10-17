import Goose.Lower.Validation.ReplacementSourceSitesLoops

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem ReplacementSitesAt.fork_actions_generated {le : LEnv} {before : LS} {loop : Option LoopCtx}
    (condition : ValueId) {first : B α} {second : B β}
    {join : Option BlockId → α → Option BlockId → β → B γ}
    (generated : GeneratedBuilderState before) (bounds : LoopBuilderTargets loop before)
    (firstDense : DenseRun first) (firstTargets : GeneratedTargetRun loop first)
    (one : ∀ state, GeneratedBuilderState state → LoopBuilderTargets loop state → ReplacementSitesAt le state first)
    (two : ∀ state, GeneratedBuilderState state → LoopBuilderTargets loop state → ReplacementSitesAt le state second)
    (joining : ∀ endT valueT endF valueF state, ReplacementSitesAt le state (join endT valueT endF valueF)) :
    ReplacementSitesAt le before (do
      let (thenBlock, elseBlock) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some thenBlock)
      let thenValue ← first
      let thenEnd ← Goose.Lower.curBlock
      Goose.Lower.setCur (some elseBlock)
      let elseValue ← second
      let elseEnd ← Goose.Lower.curBlock
      join thenEnd thenValue elseEnd elseValue) := by
  let forked := Goose.Lower.fork condition le before
  let enteredT := Goose.Lower.setCur (some forked.1.1) le forked.2
  let endedT := first le enteredT.2
  let enteredF := Goose.Lower.setCur (some forked.1.2) le endedT.2
  have forkGenerated := generated.fork condition (show Goose.Lower.fork condition le before = forked from rfl)
  have ids : forked.1 = (before.blocks.size, before.blocks.size + 1) ∧
      forked.2.blocks.size = before.blocks.size + 2 := fork_ids rfl
  have forkGrows : before.blocks.size ≤ forked.2.blocks.size := by rw [ids.2]; nat_omega
  have thenBound : forked.1.1 < forked.2.blocks.size := by
    simp only [ids.1, ids.2]
    nat_omega
  have elseBound : forked.1.2 < forked.2.blocks.size := by
    simp only [ids.1, ids.2]
    nat_omega
  have thenGenerated := forkGenerated.setCur (some forked.1.1)
    (by intro current same; cases same; exact thenBound)
    (show Goose.Lower.setCur _ le forked.2 = enteredT from rfl)
  have thenBounds : LoopBuilderTargets loop enteredT.2 := bounds.mono forkGrows
  have thenFacts := firstDense le enteredT.2 endedT.1 endedT.2 rfl thenGenerated.dense thenGenerated.live
  have endedGenerated := thenGenerated.of_runs firstDense firstTargets thenBounds
    (show first le enteredT.2 = endedT from rfl)
  have laterElse : forked.1.2 < endedT.2.blocks.size := Nat.lt_of_lt_of_le elseBound thenFacts.2.2
  have elseGenerated := endedGenerated.setCur (some forked.1.2)
    (by intro current same; cases same; exact laterElse)
    (show Goose.Lower.setCur _ le endedT.2 = enteredF from rfl)
  have elseBounds : LoopBuilderTargets loop enteredF.2 := thenBounds.mono thenFacts.2.2
  apply (ReplacementSitesAt.fork _ _ _).bind
  apply (ReplacementSitesAt.setCur _ _ _).bind
  apply (one enteredT.2 thenGenerated thenBounds).bind
  apply (ReplacementSitesAt.curBlock _ _).bind
  simp only [curBlock_run]
  apply (ReplacementSitesAt.setCur _ _ _).bind
  apply (two enteredF.2 elseGenerated elseBounds).bind
  apply (ReplacementSitesAt.curBlock _ _).bind
  simp only [curBlock_run]
  exact joining _ _ _ _ _

end Goose.Lower.Validation
