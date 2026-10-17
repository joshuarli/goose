import Goose.Lower.Validation.EmittedTypingSourceResults
import Goose.Lower.Validation.EmittedTypingBranches

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem emitted_checked_generated_branches {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (generated : GeneratedBuilderState before)
    (condition : ValueId)
    (conditionBound : before.cur.isSome = true → condition < before.vals.size)
    (first second : B ValueId)
    (firstChecked : ∀ initial started, EmittedBuilder le initial started → GeneratedBuilderState started →
      TypePrefix before started → before.blocks.size ≤ started.blocks.size →
      EmittedBuilder le initial (first le started).2 ∧ GeneratedBuilderState (first le started).2)
    (secondChecked : ∀ initial started, EmittedBuilder le initial started → GeneratedBuilderState started →
      TypePrefix before started → before.blocks.size ≤ started.blocks.size →
      EmittedBuilder le initial (second le started).2 ∧ GeneratedBuilderState (second le started).2)
    (firstAdvance : AdvB first) (secondAdvance : AdvB second) (firstTypes : TypeRun first)
    (tail : Option BlockId → ValueId → Option BlockId → ValueId → B α)
    (tailChecked : ∀ initial startedT evaluatedT valueT startedF evaluatedF valueF,
      EmittedBuilder le initial evaluatedF → GeneratedBuilderState evaluatedF → first le startedT = (valueT, evaluatedT) →
      second le startedF = (valueF, evaluatedF) → evaluatedT.vals.size ≤ evaluatedF.vals.size →
      EmittedBuilder le initial (tail evaluatedT.cur valueT evaluatedF.cur valueF le evaluatedF).2 ∧
      GeneratedBuilderState (tail evaluatedT.cur valueT evaluatedF.cur valueF le evaluatedF).2)
    {result : α} {after : LS}
    (run : (do
      let (tb, eb) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some tb)
      let valueT ← first
      let endT ← Goose.Lower.curBlock
      Goose.Lower.setCur (some eb)
      let valueF ← second
      let endF ← Goose.Lower.curBlock
      tail endT valueT endF valueF) le before = (result, after)) :
    EmittedBuilder le initial after ∧ GeneratedBuilderState after := by
  simp only [bind_eq] at run
  obtain ⟨⟨tb, eb⟩, forked, forkRun, u1, startedT, startTRun, valueT, evaluatedT, firstRun,
    endT, readT, curTRun, u2, startedF, startFRun, valueF, evaluatedF, secondRun,
    endF, readF, curFRun, tailRun⟩ := run
  rw [curBlock_run] at curTRun curFRun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj curTRun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj curFRun
  have ids := fork_ids forkRun
  obtain ⟨tbId, ebId⟩ := Prod.mk.inj ids.1
  subst tbId ebId
  have forkBuilder := builder.fork condition conditionBound
  rw [forkRun] at forkBuilder
  dsimp only at forkBuilder
  have forkGenerated := generated.fork condition forkRun
  have startedTBuilder := forkBuilder.setCur (some before.blocks.size) (by
    intro block same
    have id := Option.some.inj same
    subst block
    have size := ids.2
    nat_omega)
  rw [startTRun] at startedTBuilder
  dsimp only at startedTBuilder
  have startTTypes := (types_fork condition le before _ _ forkRun).trans
    (types_setCur (some before.blocks.size) le forked _ _ startTRun)
  have startTBound : ∀ block, some before.blocks.size = some block → block < forked.blocks.size := by
    intro block same
    have id := Option.some.inj same
    subst block
    have size := ids.2
    nat_omega
  have startedTGenerated := forkGenerated.setCur _ startTBound startTRun
  have startTGrows : before.blocks.size ≤ startedT.blocks.size := by
    have grow := (advB_fork condition le before _ _ forkRun).ext.1
    rw [setCur_run] at startTRun
    have same := congrArg (fun pair => pair.2.blocks.size) startTRun
    simp only at same
    nat_omega
  have evaluatedTBuilder := firstChecked initial startedT startedTBuilder startedTGenerated startTTypes startTGrows
  rw [firstRun] at evaluatedTBuilder
  dsimp only at evaluatedTBuilder
  have firstAdv := firstAdvance le startedT _ _ firstRun
  have startedFBuilder := evaluatedTBuilder.1.setCur (some (before.blocks.size + 1)) (by
    intro block same
    have id := Option.some.inj same
    subst block
    have size : startedT.blocks.size = forked.blocks.size := by
      rw [setCur_run] at startTRun
      exact congrArg (fun pair => pair.2.blocks.size) startTRun.symm
    have forkSize := ids.2
    have evaluatedSize := firstAdv.ext.1
    nat_omega)
  rw [startFRun] at startedFBuilder
  dsimp only at startedFBuilder
  have startFTypes := startTTypes.trans ((firstTypes le startedT _ _ firstRun).trans
    (types_setCur (some (before.blocks.size + 1)) le evaluatedT _ _ startFRun))
  have startFBound : ∀ block, some (before.blocks.size + 1) = some block → block < evaluatedT.blocks.size := by
    intro block same
    have id := Option.some.inj same
    subst block
    have size : startedT.blocks.size = forked.blocks.size := by
      rw [setCur_run] at startTRun
      exact congrArg (fun pair => pair.2.blocks.size) startTRun.symm
    have forkSize := ids.2
    have evaluatedSize := firstAdv.ext.1
    nat_omega
  have startedFGenerated := evaluatedTBuilder.2.setCur _ startFBound startFRun
  have startFGrows : before.blocks.size ≤ startedF.blocks.size := by
    have grow := firstAdv.ext.1
    rw [setCur_run] at startFRun
    have same := congrArg (fun pair => pair.2.blocks.size) startFRun
    simp only at same
    nat_omega
  have evaluatedFBuilder := secondChecked initial startedF startedFBuilder startedFGenerated startFTypes startFGrows
  rw [secondRun] at evaluatedFBuilder
  dsimp only at evaluatedFBuilder
  have secondAdv := secondAdvance le startedF _ _ secondRun
  have firstValues : evaluatedT.vals.size ≤ evaluatedF.vals.size := by
    have size : startedF.vals.size = evaluatedT.vals.size := by
      rw [setCur_run] at startFRun
      exact congrArg (fun pair => pair.2.vals.size) startFRun.symm
    rw [← size]
    exact secondAdv.vals
  have finished := tailChecked initial startedT evaluatedT valueT startedF evaluatedF valueF
    evaluatedFBuilder.1 evaluatedFBuilder.2 firstRun secondRun firstValues
  rw [tailRun] at finished
  exact finished

theorem emitted_checked_generated_ifValue {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (generated : GeneratedBuilderState before)
    (condition : ValueId)
    (conditionBound : before.cur.isSome = true → condition < before.vals.size)
    (first second : B ValueId)
    (firstChecked : ∀ initial started, EmittedBuilder le initial started → GeneratedBuilderState started →
      TypePrefix before started → before.blocks.size ≤ started.blocks.size →
      EmittedBuilder le initial (first le started).2 ∧ GeneratedBuilderState (first le started).2)
    (secondChecked : ∀ initial started, EmittedBuilder le initial started → GeneratedBuilderState started →
      TypePrefix before started → before.blocks.size ≤ started.blocks.size →
      EmittedBuilder le initial (second le started).2 ∧ GeneratedBuilderState (second le started).2)
    (firstAdvance : AdvB first) (secondAdvance : AdvB second) (firstTypes : TypeRun first)
    (firstBound : ValueRun first) (secondBound : ValueRun second) :
    let after := ((Goose.Lower.whenLive 0 fun _ => do
      let (tb, eb) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some tb)
      let valueT ← first
      let endT ← Goose.Lower.curBlock
      Goose.Lower.setCur (some eb)
      let valueF ← second
      let endF ← Goose.Lower.curBlock
      Goose.Lower.joinValue endT valueT endF valueF) le before).2
    EmittedBuilder le initial after ∧ GeneratedBuilderState after := by
  dsimp only
  cases live : before.cur with
  | none => rw [whenLive_none _ _ _ live]; exact ⟨builder, generated⟩
  | some block =>
    rw [whenLive_some _ _ _ live]
    exact emitted_checked_generated_branches builder generated condition conditionBound first second firstChecked secondChecked
      firstAdvance secondAdvance firstTypes (fun endT valueT endF valueF => Goose.Lower.joinValue endT valueT endF valueF)
      (fun _ startedT evaluatedT valueT startedF evaluatedF valueF builder generated firstRun secondRun growth =>
        ⟨builder.joinValue evaluatedT.cur evaluatedF.cur valueT valueF
          (fun live => Nat.lt_of_lt_of_le (firstBound le startedT _ _ firstRun live) growth)
          (fun live => secondBound le startedF _ _ secondRun live),
          generated.joinValue evaluatedT.cur valueT evaluatedF.cur valueF rfl⟩) rfl


theorem emitted_checked_generated_ifArms {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (generated : GeneratedBuilderState before)
    (condition : ValueId)
    (conditionBound : before.cur.isSome = true → condition < before.vals.size)
    (first second : B ValueId)
    (firstChecked : ∀ initial started, EmittedBuilder le initial started → GeneratedBuilderState started →
      TypePrefix before started → before.blocks.size ≤ started.blocks.size →
      EmittedBuilder le initial (first le started).2 ∧ GeneratedBuilderState (first le started).2)
    (secondChecked : ∀ initial started, EmittedBuilder le initial started → GeneratedBuilderState started →
      TypePrefix before started → before.blocks.size ≤ started.blocks.size →
      EmittedBuilder le initial (second le started).2 ∧ GeneratedBuilderState (second le started).2)
    (firstAdvance : AdvB first) (secondAdvance : AdvB second) (firstTypes : TypeRun first) :
    let after := ((Goose.Lower.whenLive () fun _ => do
      let (tb, eb) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some tb)
      let valueT ← first
      let endT ← Goose.Lower.curBlock
      Goose.Lower.setCur (some eb)
      let valueF ← second
      let endF ← Goose.Lower.curBlock
      Goose.Lower.joinArms endT endF) le before).2
    EmittedBuilder le initial after ∧ GeneratedBuilderState after := by
  dsimp only
  cases live : before.cur with
  | none => rw [whenLive_none _ _ _ live]; exact ⟨builder, generated⟩
  | some block =>
    rw [whenLive_some _ _ _ live]
    exact emitted_checked_generated_branches builder generated condition conditionBound first second firstChecked secondChecked
      firstAdvance secondAdvance firstTypes (fun endT _ endF _ => Goose.Lower.joinArms endT endF)
      (fun _ _ evaluatedT _ _ evaluatedF _ builder generated _ _ _ =>
        ⟨builder.joinArms evaluatedT.cur evaluatedF.cur, generated.joinArms evaluatedT.cur evaluatedF.cur rfl⟩) rfl

end Goose.Lower.Validation
