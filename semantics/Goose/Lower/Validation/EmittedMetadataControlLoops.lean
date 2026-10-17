import Goose.Lower.Validation.EmittedMetadataControlBuilder
import Goose.Lower.Validation.EmittedTypingLoops

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem metadata_control_loopBody {le : LEnv} {before : LS}
    (builder : EmittedMetadata le before) (generated : GeneratedBuilderState before)
    (condition : ValueId)
    (conditionTyped : before.cur.isSome = true → before.vals[condition]? = some (some (.data .bool)))
    (body : Nat → BlockId → B ValueId) (back : B Unit)
    (bodyChecked : ∀ depth target started, EmittedMetadata le started →
      GeneratedBuilderState started → TypePrefix before started →
      before.blocks.size ≤ started.blocks.size → target < started.blocks.size → started.cur.isSome = true →
      EmittedMetadata le (body depth target le started).2 ∧ GeneratedBuilderState (body depth target le started).2)
    (bodyAdvance : ∀ depth target, AdvB (body depth target))
    (bodyTypes : ∀ depth target, TypeRun (body depth target))
    (backChecked : ∀ evaluated, EmittedMetadata le evaluated → GeneratedBuilderState evaluated → TypePrefix before evaluated →
      before.blocks.size ≤ evaluated.blocks.size →
      EmittedMetadata le (back le evaluated).2 ∧ GeneratedBuilderState (back le evaluated).2)
    (backAdvance : AdvB back) :
    let after := (Goose.Lower.loopBody condition body back le before).2
    EmittedMetadata le after ∧ GeneratedBuilderState after := by
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
  have forkBuilder := builder.fork condition conditionTyped
  rw [forkRun] at forkBuilder
  dsimp only at forkBuilder
  have startBuilder := forkBuilder.setCur (some before.blocks.size)
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
  have startLive : started.cur.isSome = true := by
    rw [setCur_run] at startRun
    obtain ⟨_, rfl⟩ := Prod.mk.inj startRun
    rfl
  have evaluatedBuilder := bodyChecked before.stack.length (before.blocks.size + 1) started
    startBuilder startGenerated startedValues startGrows targetBound startLive
  rw [bodyRun] at evaluatedBuilder
  dsimp only at evaluatedBuilder
  have values := (types_fork condition le before _ _ forkRun).trans
    ((types_setCur (some before.blocks.size) le forked _ _ startRun).trans
      (bodyTypes before.stack.length (before.blocks.size + 1) le started _ _ bodyRun))
  have bodyAdv := bodyAdvance before.stack.length (before.blocks.size + 1) le started _ _ bodyRun
  have evaluatedGrows : before.blocks.size ≤ evaluated.blocks.size := Nat.le_trans startGrows bodyAdv.ext.1
  have closedBuilder := backChecked evaluated evaluatedBuilder.1 evaluatedBuilder.2 values evaluatedGrows
  rw [backRun] at closedBuilder
  dsimp only at closedBuilder
  have backAdv := backAdvance le evaluated _ _ backRun
  have resumedBuilder := closedBuilder.1.setCur (some (before.blocks.size + 1))
  rw [resumeRun] at resumedBuilder
  have resumeBound : ∀ block, some (before.blocks.size + 1) = some block → block < closed.blocks.size := by
    intro block same
    have id := Option.some.inj same
    subst block
    exact Nat.lt_of_lt_of_le targetBound (Nat.le_trans bodyAdv.ext.1 backAdv.ext.1)
  have resumeGenerated := closedBuilder.2.setCur _ resumeBound resumeRun
  exact ⟨resumedBuilder, resumeGenerated⟩

theorem EmittedMetadata.rangeBack {le : LEnv} {before : LS}
    (checked : EmittedMetadata le before) (hint : IntTy) (counter header : ValueId) :
    EmittedMetadata le (Goose.Lower.rangeBack hint counter header le before).2 := by
  cases live : before.cur with
  | none =>
    simpa only [Goose.Lower.rangeBack, bind_run, isLive_none live, Bool.false_eq_true, reduceIte, pure_run] using checked
  | some block =>
    have advanced := checked.emitDef (.next hint counter)
    have branched := advanced.emitTerm (.br header [(Goose.Lower.emitDef (.next hint counter) le before).1]) (fun _ => .br _ _)
    have active : Goose.Lower.isLive le before = (true, before) := by
      simp [Goose.Lower.isLive, Goose.Lower.curBlock, bind_run, live, pure_run]
    simpa only [Goose.Lower.rangeBack, bind_run, active, reduceIte] using branched

theorem metadata_control_lowerWhile {le : LEnv} {before : LS}
    (builder : EmittedMetadata le before) (generated : GeneratedBuilderState before)
    (header : BlockId) (headerBound : header < before.blocks.size) (condition : B ValueId)
    (body : Nat → BlockId → B ValueId)
    (conditionChecked : ∀ before, EmittedMetadata le before → GeneratedBuilderState before →
      EmittedMetadata le (condition le before).2 ∧ GeneratedBuilderState (condition le before).2)
    (conditionTyped : ∀ state value after, GeneratedBuilderState state → condition le state = (value, after) →
      after.cur.isSome = true → after.vals[value]? = some (some (.data .bool))) (conditionAdvance : AdvB condition)
    (bodyChecked : ∀ depth target started, EmittedMetadata le started →
      GeneratedBuilderState started → header < started.blocks.size → target < started.blocks.size → started.cur.isSome = true →
      EmittedMetadata le (body depth target le started).2 ∧ GeneratedBuilderState (body depth target le started).2)
    (bodyAdvance : ∀ depth target, AdvB (body depth target))
    (bodyTypes : ∀ depth target, TypeRun (body depth target)) :
    let after := (Goose.Lower.lowerWhile header condition body le before).2
    EmittedMetadata le after ∧ GeneratedBuilderState after := by
  generalize run : Goose.Lower.lowerWhile header condition body le before = result
  obtain ⟨resultValue, after⟩ := result
  dsimp only
  simp only [Goose.Lower.lowerWhile, bind_eq] at run
  obtain ⟨value, evaluated, conditionRun, bodyRun⟩ := run
  have evaluatedBuilder := conditionChecked before builder generated
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
    have output := metadata_control_loopBody evaluatedBuilder.1 evaluatedBuilder.2 value
      (fun active => conditionTyped before _ _ generated conditionRun active) body (Goose.Lower.emitTerm (.br header []))
      (fun depth target started builder generated _ grows targetBound active =>
        bodyChecked depth target started builder generated (Nat.lt_of_lt_of_le headerEvaluated grows) targetBound active)
      bodyAdvance bodyTypes
      (fun _ builder generated _ grows =>
        ⟨builder.emitTerm (.br header []) (fun _ => .br _ _),
          generated.emitTerm (.br header []) (by
            intro target member
            have same : target = header := by simpa [Term.successors] using member
            subst target
            exact Nat.lt_of_lt_of_le headerEvaluated grows) rfl⟩)
      (advB_emitTerm _)
    rw [bodyRun] at output
    exact output

theorem metadata_control_lowerRange {le : LEnv} {before : LS}
    (builder : EmittedMetadata le before) (generated : GeneratedBuilderState before)
    (header : BlockId) (headerBound : header < before.blocks.size) (type : IntTy)
    (counter upper : ValueId) {current : BlockId} (live : before.cur = some current)
    (counterTyped : before.vals[counter]? = some (some (.data (.int type))))
    (upperTyped : before.vals[upper]? = some (some (.data (.int type))))
    (body : Nat → BlockId → B ValueId)
    (bodyChecked : ∀ depth target started, EmittedMetadata le started →
      GeneratedBuilderState started → started.vals[counter]? = some (some (.data (.int type))) →
      TypePrefix before started → header < started.blocks.size → target < started.blocks.size → started.cur.isSome = true →
      EmittedMetadata le (body depth target le started).2 ∧ GeneratedBuilderState (body depth target le started).2)
    (bodyAdvance : ∀ depth target, AdvB (body depth target))
    (bodyTypes : ∀ depth target, TypeRun (body depth target)) :
    let after := (Goose.Lower.lowerRange type counter upper header body le before).2
    EmittedMetadata le after ∧ GeneratedBuilderState after := by
  have success : (Op.cmp .lt type counter upper).resultTy (tyEnv le before) = .ok (.data .bool) := by
    simp [Op.resultTy, TyEnv.intTy, TyEnv.dataTy, TyEnv.valTy, tyEnv,
      counterTyped, upperTyped, pure, Except.pure, bind, Except.bind]
  let compared := Goose.Lower.emitDef (.cmp .lt type counter upper) le before
  have comparedBuilder := builder.emitDef (.cmp .lt type counter upper)
  have comparisonTyped := (emitDef_recorded live success).2.2.1
  have retainedCounter := (types_emitDef (.cmp .lt type counter upper) le before _ _ rfl) counter (.data (.int type)) counterTyped
  have comparedGenerated : GeneratedBuilderState compared.2 := generated.emitDef (.cmp .lt type counter upper) rfl
  have headerCompared : header < compared.2.blocks.size :=
    Nat.lt_of_lt_of_le headerBound (advB_emitDef (.cmp .lt type counter upper) le before _ _ rfl).ext.1
  have output := metadata_control_loopBody comparedBuilder comparedGenerated compared.1
    (fun _ => comparisonTyped) body
    (Goose.Lower.rangeBack type counter header)
    (fun depth target started builder generated retained grows targetBound active =>
      bodyChecked depth target started builder generated (retained counter (.data (.int type)) retainedCounter)
        ((types_emitDef (.cmp .lt type counter upper) le before _ _ rfl).trans retained)
        (Nat.lt_of_lt_of_le headerCompared grows) targetBound active)
    bodyAdvance bodyTypes
    (fun state builder generated retained grows => by
      have dense := dense_rangeBack type counter header le state _ _ rfl generated.dense generated.live
      have bounded := generatedTargets_rangeBack (env := le) type counter header rfl generated.targets (Nat.lt_of_lt_of_le headerCompared grows)
      exact ⟨builder.rangeBack type counter header,
        ⟨dense.1, dense.2.1, bounded⟩⟩)
    (advB_rangeBack _ _ _)
  exact output

end Goose.Lower.Validation
