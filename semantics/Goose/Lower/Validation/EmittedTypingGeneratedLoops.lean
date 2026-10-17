import Goose.Lower.Validation.EmittedTypingSourceResults
import Goose.Lower.Validation.EmittedTypingLoops

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem emitted_checked_generated_loopBody {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (generated : GeneratedBuilderState before)
    (condition : ValueId)
    (conditionBound : before.cur.isSome = true → condition < before.vals.size)
    (body : Nat → BlockId → B ValueId) (back : B Unit)
    (bodyChecked : ∀ depth target initial started, EmittedBuilder le initial started →
      GeneratedBuilderState started → TypePrefix before started →
      before.blocks.size ≤ started.blocks.size → target < started.blocks.size →
      EmittedBuilder le initial (body depth target le started).2 ∧ GeneratedBuilderState (body depth target le started).2)
    (bodyAdvance : ∀ depth target, AdvB (body depth target))
    (bodyTypes : ∀ depth target, TypeRun (body depth target))
    (backChecked : ∀ initial evaluated, EmittedBuilder le initial evaluated → GeneratedBuilderState evaluated → TypePrefix before evaluated →
      before.blocks.size ≤ evaluated.blocks.size →
      EmittedBuilder le initial (back le evaluated).2 ∧ GeneratedBuilderState (back le evaluated).2)
    (backAdvance : AdvB back) :
    let after := (Goose.Lower.loopBody condition body back le before).2
    EmittedBuilder le initial after ∧ GeneratedBuilderState after := by
  generalize run : Goose.Lower.loopBody condition body back le before = result
  obtain ⟨resultValue, after⟩ := result
  dsimp only
  simp only [Goose.Lower.loopBody, bind_eq] at run
  obtain ⟨observedStack, observed, observeRun, ⟨tb, xb⟩, forked, forkRun, u1, started, startRun,
    value, evaluated, bodyRun, u2, closed, backRun, resumeRun⟩ := run
  simp only [get_apply, Prod.mk.injEq] at observeRun
  obtain ⟨rfl, rfl⟩ := observeRun
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
  have startedValues := (types_fork condition le before _ _ forkRun).trans
    (types_setCur (some before.blocks.size) le forked _ _ startRun)
  have forkGenerated := generated.fork condition forkRun
  have startBound : ∀ block, some before.blocks.size = some block → block < forked.blocks.size := by
    intro block same
    have id := Option.some.inj same
    subst block
    have size := ids.2
    nat_omega
  have startGenerated := forkGenerated.setCur _ startBound startRun
  have startSize : started.blocks.size = forked.blocks.size := by
    rw [setCur_run] at startRun
    exact congrArg (fun pair => pair.2.blocks.size) startRun.symm
  have startGrows : before.blocks.size ≤ started.blocks.size := by
    have size := ids.2
    nat_omega
  have targetBound : before.blocks.size + 1 < started.blocks.size := by
    have size := ids.2
    nat_omega
  have evaluatedBuilder := bodyChecked before.stack.length (before.blocks.size + 1) initial started
    startBuilder startGenerated startedValues startGrows targetBound
  rw [bodyRun] at evaluatedBuilder
  dsimp only at evaluatedBuilder
  have values := (types_fork condition le before _ _ forkRun).trans
    ((types_setCur (some before.blocks.size) le forked _ _ startRun).trans
      (bodyTypes before.stack.length (before.blocks.size + 1) le started _ _ bodyRun))
  have bodyAdv := bodyAdvance before.stack.length (before.blocks.size + 1) le started _ _ bodyRun
  have evaluatedGrows : before.blocks.size ≤ evaluated.blocks.size := Nat.le_trans startGrows bodyAdv.ext.1
  have closedBuilder := backChecked initial evaluated evaluatedBuilder.1 evaluatedBuilder.2 values evaluatedGrows
  rw [backRun] at closedBuilder
  dsimp only at closedBuilder
  have backAdv := backAdvance le evaluated _ _ backRun
  have resumedBuilder := closedBuilder.1.setCur (some (before.blocks.size + 1)) (by
    intro block same
    have id := Option.some.inj same
    subst block
    have size : started.blocks.size = forked.blocks.size := by
      rw [setCur_run] at startRun
      exact congrArg (fun pair => pair.2.blocks.size) startRun.symm
    have forkSize := ids.2
    have bodySize := bodyAdv.ext.1
    have backSize := backAdv.ext.1
    nat_omega)
  rw [resumeRun] at resumedBuilder
  have resumeBound : ∀ block, some (before.blocks.size + 1) = some block → block < closed.blocks.size := by
    intro block same
    have id := Option.some.inj same
    subst block
    exact Nat.lt_of_lt_of_le targetBound (Nat.le_trans bodyAdv.ext.1 backAdv.ext.1)
  have resumeGenerated := closedBuilder.2.setCur _ resumeBound resumeRun
  exact ⟨resumedBuilder, resumeGenerated⟩

theorem emitted_checked_generated_lowerWhile {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (generated : GeneratedBuilderState before)
    (header : BlockId) (headerBound : header < before.blocks.size) (condition : B ValueId)
    (body : Nat → BlockId → B ValueId)
    (conditionChecked : ∀ initial before, EmittedBuilder le initial before → GeneratedBuilderState before →
      EmittedBuilder le initial (condition le before).2 ∧ GeneratedBuilderState (condition le before).2)
    (conditionBound : ValueRun condition) (conditionAdvance : AdvB condition)
    (bodyChecked : ∀ depth target initial started, EmittedBuilder le initial started →
      GeneratedBuilderState started → header < started.blocks.size → target < started.blocks.size →
      EmittedBuilder le initial (body depth target le started).2 ∧ GeneratedBuilderState (body depth target le started).2)
    (bodyAdvance : ∀ depth target, AdvB (body depth target))
    (bodyTypes : ∀ depth target, TypeRun (body depth target)) :
    let after := (Goose.Lower.lowerWhile header condition body le before).2
    EmittedBuilder le initial after ∧ GeneratedBuilderState after := by
  generalize run : Goose.Lower.lowerWhile header condition body le before = result
  obtain ⟨resultValue, after⟩ := result
  dsimp only
  simp only [Goose.Lower.lowerWhile, bind_eq] at run
  obtain ⟨value, evaluated, conditionRun, bodyRun⟩ := run
  have evaluatedBuilder := conditionChecked initial before builder generated
  rw [conditionRun] at evaluatedBuilder
  dsimp only at evaluatedBuilder
  have headerEvaluated := Nat.lt_of_lt_of_le headerBound (conditionAdvance le before _ _ conditionRun).ext.1
  cases live : evaluated.cur with
  | none =>
    rw [whenLive_none _ _ _ live] at bodyRun
    obtain ⟨_, rfl⟩ := Prod.mk.inj bodyRun
    exact evaluatedBuilder
  | some current =>
    rw [whenLive_some _ _ _ live] at bodyRun
    have output := emitted_checked_generated_loopBody evaluatedBuilder.1 evaluatedBuilder.2 value
      (fun active => conditionBound le before _ _ conditionRun active) body (Goose.Lower.emitTerm (.br header []))
      (fun depth target initial started builder generated _ grows targetBound =>
        bodyChecked depth target initial started builder generated (Nat.lt_of_lt_of_le headerEvaluated grows) targetBound)
      bodyAdvance bodyTypes
      (fun _ _ builder generated _ grows =>
        ⟨builder.emitTerm (.br header []) (by intro active value member; simp [Term.uses] at member),
          generated.emitTerm (.br header []) (by
            intro target member
            have same : target = header := by simpa [Term.successors] using member
            subst target
            exact Nat.lt_of_lt_of_le headerEvaluated grows) rfl⟩)
      (advB_emitTerm _)
    rw [bodyRun] at output
    exact output

end Goose.Lower.Validation
