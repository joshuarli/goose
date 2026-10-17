import Goose.Lower.Validation.EmittedTypingControlCheckpoints

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem emitted_checked_branches {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (condition : ValueId)
    (conditionBound : before.cur.isSome = true → condition < before.vals.size)
    (first second : B ValueId)
    (firstChecked : ∀ initial started, EmittedBuilder le initial started → TypePrefix before started → EmittedBuilder le initial (first le started).2)
    (secondChecked : ∀ initial started, EmittedBuilder le initial started → TypePrefix before started → EmittedBuilder le initial (second le started).2)
    (firstAdvance : AdvB first) (secondAdvance : AdvB second) (firstTypes : TypeRun first)
    (tail : Option BlockId → ValueId → Option BlockId → ValueId → B α)
    (tailChecked : ∀ initial startedT evaluatedT valueT startedF evaluatedF valueF,
      EmittedBuilder le initial evaluatedF → first le startedT = (valueT, evaluatedT) →
      second le startedF = (valueF, evaluatedF) → evaluatedT.vals.size ≤ evaluatedF.vals.size →
      EmittedBuilder le initial (tail evaluatedT.cur valueT evaluatedF.cur valueF le evaluatedF).2)
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
    EmittedBuilder le initial after := by
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
  have evaluatedTBuilder := firstChecked initial startedT startedTBuilder startTTypes
  rw [firstRun] at evaluatedTBuilder
  dsimp only at evaluatedTBuilder
  have firstAdv := firstAdvance le startedT _ _ firstRun
  have startedFBuilder := evaluatedTBuilder.setCur (some (before.blocks.size + 1)) (by
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
  have evaluatedFBuilder := secondChecked initial startedF startedFBuilder startFTypes
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
    evaluatedFBuilder firstRun secondRun firstValues
  rw [tailRun] at finished
  exact finished

theorem emitted_checked_ifValue {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (condition : ValueId)
    (conditionBound : before.cur.isSome = true → condition < before.vals.size)
    (first second : B ValueId)
    (firstChecked : ∀ initial started, EmittedBuilder le initial started → TypePrefix before started → EmittedBuilder le initial (first le started).2)
    (secondChecked : ∀ initial started, EmittedBuilder le initial started → TypePrefix before started → EmittedBuilder le initial (second le started).2)
    (firstAdvance : AdvB first) (secondAdvance : AdvB second) (firstTypes : TypeRun first)
    (firstBound : ValueRun first) (secondBound : ValueRun second) :
    EmittedBuilder le initial ((Goose.Lower.whenLive 0 fun _ => do
      let (tb, eb) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some tb)
      let valueT ← first
      let endT ← Goose.Lower.curBlock
      Goose.Lower.setCur (some eb)
      let valueF ← second
      let endF ← Goose.Lower.curBlock
      Goose.Lower.joinValue endT valueT endF valueF) le before).2 := by
  cases live : before.cur with
  | none => rw [whenLive_none _ _ _ live]; exact builder
  | some block =>
    rw [whenLive_some _ _ _ live]
    exact emitted_checked_branches builder condition conditionBound first second firstChecked secondChecked
      firstAdvance secondAdvance firstTypes (fun endT valueT endF valueF => Goose.Lower.joinValue endT valueT endF valueF)
      (fun _ startedT evaluatedT valueT startedF evaluatedF valueF builder firstRun secondRun growth =>
        builder.joinValue evaluatedT.cur evaluatedF.cur valueT valueF
          (fun live => Nat.lt_of_lt_of_le (firstBound le startedT _ _ firstRun live) growth)
          (fun live => secondBound le startedF _ _ secondRun live)) rfl


theorem emitted_checked_ifArms {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (condition : ValueId)
    (conditionBound : before.cur.isSome = true → condition < before.vals.size)
    (first second : B ValueId)
    (firstChecked : ∀ initial started, EmittedBuilder le initial started → TypePrefix before started → EmittedBuilder le initial (first le started).2)
    (secondChecked : ∀ initial started, EmittedBuilder le initial started → TypePrefix before started → EmittedBuilder le initial (second le started).2)
    (firstAdvance : AdvB first) (secondAdvance : AdvB second) (firstTypes : TypeRun first) :
    EmittedBuilder le initial ((Goose.Lower.whenLive () fun _ => do
      let (tb, eb) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some tb)
      let valueT ← first
      let endT ← Goose.Lower.curBlock
      Goose.Lower.setCur (some eb)
      let valueF ← second
      let endF ← Goose.Lower.curBlock
      Goose.Lower.joinArms endT endF) le before).2 := by
  cases live : before.cur with
  | none => rw [whenLive_none _ _ _ live]; exact builder
  | some block =>
    rw [whenLive_some _ _ _ live]
    exact emitted_checked_branches builder condition conditionBound first second firstChecked secondChecked
      firstAdvance secondAdvance firstTypes (fun endT _ endF _ => Goose.Lower.joinArms endT endF)
      (fun _ _ evaluatedT _ _ evaluatedF _ builder _ _ _ => builder.joinArms evaluatedT.cur evaluatedF.cur) rfl


theorem emitted_checked_ifThen {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (condition : ValueId)
    (conditionBound : before.cur.isSome = true → condition < before.vals.size) (body : B ValueId)
    (bodyChecked : ∀ initial started, EmittedBuilder le initial started → TypePrefix before started → EmittedBuilder le initial (body le started).2)
    (bodyAdvance : AdvB body) :
    EmittedBuilder le initial ((Goose.Lower.whenLive () fun _ => do
      let (tb, xb) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some tb)
      let _ ← body
      Goose.Lower.emitTerm (.br xb [])
      Goose.Lower.setCur (some xb)) le before).2 := by
  generalize run : (Goose.Lower.whenLive () fun _ => do
      let (tb, xb) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some tb)
      let _ ← body
      Goose.Lower.emitTerm (.br xb [])
      Goose.Lower.setCur (some xb)) le before = result
  obtain ⟨resultValue, after⟩ := result
  dsimp only
  cases live : before.cur with
  | none =>
    rw [whenLive_none _ _ _ live] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact builder
  | some current =>
    rw [whenLive_some _ _ _ live] at run
    simp only [bind_eq] at run
    obtain ⟨⟨tb, xb⟩, forked, forkRun, u1, started, startRun,
      value, evaluated, bodyRun, u2, closed, closeRun, resumeRun⟩ := run
    have ids := fork_ids forkRun
    obtain ⟨tbId, xbId⟩ := Prod.mk.inj ids.1
    subst tbId xbId
    have forkBuilder := builder.fork condition conditionBound
    rw [forkRun] at forkBuilder
    dsimp only at forkBuilder
    have startBuilder := forkBuilder.setCur (some before.blocks.size) (by
      intro block same
      have id := Option.some.inj same
      subst block
      have size := ids.2
      nat_omega)
    rw [startRun] at startBuilder
    dsimp only at startBuilder
    have startedTypes := (types_fork condition le before _ _ forkRun).trans
      (types_setCur (some before.blocks.size) le forked _ _ startRun)
    have evaluatedBuilder := bodyChecked initial started startBuilder startedTypes
    rw [bodyRun] at evaluatedBuilder
    dsimp only at evaluatedBuilder
    have bodyAdv := bodyAdvance le started _ _ bodyRun
    have closedBuilder := evaluatedBuilder.emitTerm (.br (before.blocks.size + 1) [])
      (by intro active value member; simp [Term.uses] at member)
    rw [closeRun] at closedBuilder
    dsimp only at closedBuilder
    have closeAdv := adv_emitTerm closeRun
    have resumedBuilder := closedBuilder.setCur (some (before.blocks.size + 1)) (by
      intro block same
      have id := Option.some.inj same
      subst block
      have size : started.blocks.size = forked.blocks.size := by
        rw [setCur_run] at startRun
        exact congrArg (fun pair => pair.2.blocks.size) startRun.symm
      have forkSize := ids.2
      have bodySize := bodyAdv.ext.1
      have closedSize := closeAdv.ext.1
      nat_omega)
    rw [resumeRun] at resumedBuilder
    exact resumedBuilder

theorem emitted_checked_assert {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (condition : ValueId) (origin : OriginId)
    (conditionBound : before.cur.isSome = true → condition < before.vals.size) :
    EmittedBuilder le initial ((Goose.Lower.whenLive () fun _ => do
      let (pass, fail) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some fail)
      Goose.Lower.emitTerm (.abort .assert (some origin))
      Goose.Lower.setCur (some pass)) le before).2 := by
  generalize run : (Goose.Lower.whenLive () fun _ => do
      let (pass, fail) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some fail)
      Goose.Lower.emitTerm (.abort .assert (some origin))
      Goose.Lower.setCur (some pass)) le before = result
  obtain ⟨resultValue, after⟩ := result
  dsimp only
  cases live : before.cur with
  | none =>
    rw [whenLive_none _ _ _ live] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact builder
  | some current =>
    rw [whenLive_some _ _ _ live] at run
    simp only [bind_eq] at run
    obtain ⟨⟨pass, fail⟩, forked, forkRun, u1, started, startRun, u2, closed, closeRun, resumeRun⟩ := run
    have ids := fork_ids forkRun
    obtain ⟨passId, failId⟩ := Prod.mk.inj ids.1
    subst passId failId
    have forkBuilder := builder.fork condition conditionBound
    rw [forkRun] at forkBuilder
    dsimp only at forkBuilder
    have startBuilder := forkBuilder.setCur (some (before.blocks.size + 1)) (by
      intro block same
      have id := Option.some.inj same
      subst block
      have size := ids.2
      nat_omega)
    rw [startRun] at startBuilder
    dsimp only at startBuilder
    have closedBuilder := startBuilder.emitTerm (.abort .assert (some origin))
      (by intro active value member; simp [Term.uses] at member)
    rw [closeRun] at closedBuilder
    dsimp only at closedBuilder
    have closeAdv := adv_emitTerm closeRun
    have resumedBuilder := closedBuilder.setCur (some before.blocks.size) (by
      intro block same
      have id := Option.some.inj same
      subst block
      have size : started.blocks.size = forked.blocks.size := by
        rw [setCur_run] at startRun
        exact congrArg (fun pair => pair.2.blocks.size) startRun.symm
      have forkSize := ids.2
      have closedSize := closeAdv.ext.1
      nat_omega)
    rw [resumeRun] at resumedBuilder
    exact resumedBuilder

end Goose.Lower.Validation
