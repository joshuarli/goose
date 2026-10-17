import Goose.Lower.Validation.EmittedTypingControlCheckpoints
import Goose.Lower.Validation.EmittedTypingCoercions

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def EmittedLoopTypes (loop : Option LoopCtx) (state : LS) : Prop :=
  match loop with
  | none => True
  | some context => match context.cont with
    | .jump _ => True
    | .next _ type counter => state.vals[counter]? = some (some (.data (.int type)))

theorem EmittedLoopTypes.retained {loop : Option LoopCtx} {before after : LS}
    (typed : EmittedLoopTypes loop before) (retained : TypePrefix before after) : EmittedLoopTypes loop after := by
  cases loop with
  | none => trivial
  | some context => cases current : context.cont with
    | jump header => simp only [EmittedLoopTypes, current]
    | next header type counter =>
      have row : before.vals[counter]? = some (some (.data (.int type))) := by
        simpa only [EmittedLoopTypes, current] using typed
      simpa only [EmittedLoopTypes, current] using retained counter (.data (.int type)) row

theorem EmittedBuilder.rangeBack {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (type : IntTy) (counter header : ValueId)
    (typed : before.vals[counter]? = some (some (.data (.int type)))) :
    EmittedBuilder le initial (Goose.Lower.rangeBack type counter header le before).2 := by
  cases live : before.cur with
  | none =>
    have same : (Goose.Lower.rangeBack type counter header le before).2 = before := by
      simp only [Goose.Lower.rangeBack, bind_run, isLive_none live, Bool.false_eq_true, reduceIte, pure_run]
    rw [same]
    exact builder
  | some block =>
    have success : (Op.next type counter).resultTy (tyEnv le before) = .ok (.data (.int type)) := by
      simp [Op.resultTy, TyEnv.intTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, typed,
        pure, Except.pure, bind, Except.bind]
    have advanced := builder.emitDef (.next type counter) (fun _ => ⟨.data (.int type), success⟩) (by
      intro active operand member
      have same : operand = counter := by simpa [Op.uses] using member
      subst operand
      exact (Array.getElem?_eq_some_iff.mp typed).1)
    have recorded := (emitDef_recorded live success).2.2.1
    have branched := advanced.emitTerm (.br header [(Goose.Lower.emitDef (.next type counter) le before).1]) (by
      intro active operand member
      have same : operand = (Goose.Lower.emitDef (.next type counter) le before).1 := by simpa [Term.uses] using member
      subst operand
      exact (Array.getElem?_eq_some_iff.mp recorded).1)
    have active : Goose.Lower.isLive le before = (true, before) := by
      simp [Goose.Lower.isLive, Goose.Lower.curBlock, bind_run, live, pure_run]
    simpa only [Goose.Lower.rangeBack, bind_run, active, reduceIte] using branched

theorem emitted_checked_loopBody {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (condition : ValueId)
    (conditionBound : before.cur.isSome = true → condition < before.vals.size)
    (body : Nat → BlockId → B ValueId) (back : B Unit)
    (bodyChecked : ∀ depth target initial started, EmittedBuilder le initial started →
      TypePrefix before started → EmittedBuilder le initial (body depth target le started).2)
    (bodyAdvance : ∀ depth target, AdvB (body depth target))
    (bodyTypes : ∀ depth target, TypeRun (body depth target))
    (backChecked : ∀ initial evaluated, EmittedBuilder le initial evaluated → TypePrefix before evaluated →
      EmittedBuilder le initial (back le evaluated).2)
    (backAdvance : AdvB back) :
    EmittedBuilder le initial (Goose.Lower.loopBody condition body back le before).2 := by
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
  have evaluatedBuilder := bodyChecked before.stack.length (before.blocks.size + 1) initial started startBuilder startedValues
  rw [bodyRun] at evaluatedBuilder
  dsimp only at evaluatedBuilder
  have values := (types_fork condition le before _ _ forkRun).trans
    ((types_setCur (some before.blocks.size) le forked _ _ startRun).trans
      (bodyTypes before.stack.length (before.blocks.size + 1) le started _ _ bodyRun))
  have closedBuilder := backChecked initial evaluated evaluatedBuilder values
  rw [backRun] at closedBuilder
  dsimp only at closedBuilder
  have bodyAdv := bodyAdvance before.stack.length (before.blocks.size + 1) le started _ _ bodyRun
  have backAdv := backAdvance le evaluated _ _ backRun
  have resumedBuilder := closedBuilder.setCur (some (before.blocks.size + 1)) (by
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
  exact resumedBuilder


theorem emitted_checked_lowerWhile {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (header : BlockId) (condition : B ValueId)
    (body : Nat → BlockId → B ValueId)
    (conditionChecked : ∀ initial before, EmittedBuilder le initial before → EmittedBuilder le initial (condition le before).2)
    (conditionBound : ValueRun condition)
    (bodyChecked : ∀ depth target initial before, EmittedBuilder le initial before →
      EmittedBuilder le initial (body depth target le before).2)
    (bodyAdvance : ∀ depth target, AdvB (body depth target))
    (bodyTypes : ∀ depth target, TypeRun (body depth target)) :
    EmittedBuilder le initial (Goose.Lower.lowerWhile header condition body le before).2 := by
  generalize run : Goose.Lower.lowerWhile header condition body le before = result
  obtain ⟨resultValue, after⟩ := result
  dsimp only
  simp only [Goose.Lower.lowerWhile, bind_eq] at run
  obtain ⟨value, evaluated, conditionRun, bodyRun⟩ := run
  have evaluatedBuilder := conditionChecked initial before builder
  rw [conditionRun] at evaluatedBuilder
  dsimp only at evaluatedBuilder
  cases live : evaluated.cur with
  | none =>
    rw [whenLive_none _ _ _ live] at bodyRun
    obtain ⟨_, rfl⟩ := Prod.mk.inj bodyRun
    exact evaluatedBuilder
  | some current =>
    rw [whenLive_some _ _ _ live] at bodyRun
    have output := emitted_checked_loopBody evaluatedBuilder value
      (fun active => conditionBound le before _ _ conditionRun active) body (Goose.Lower.emitTerm (.br header []))
      (fun depth target initial started builder _ => bodyChecked depth target initial started builder) bodyAdvance bodyTypes
      (fun _ _ builder _ => builder.emitTerm (.br header []) (by intro active value member; simp [Term.uses] at member))
      (advB_emitTerm _)
    rw [bodyRun] at output
    exact output

theorem emitted_checked_lowerRange {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (header : BlockId) (type : IntTy)
    (counter upper : ValueId) {current : BlockId} (live : before.cur = some current)
    (counterTyped : before.vals[counter]? = some (some (.data (.int type))))
    (upperTyped : before.vals[upper]? = some (some (.data (.int type))))
    (body : Nat → BlockId → B ValueId)
    (bodyChecked : ∀ depth target initial started, EmittedBuilder le initial started →
      started.vals[counter]? = some (some (.data (.int type))) → TypePrefix before started →
      EmittedBuilder le initial (body depth target le started).2)
    (bodyAdvance : ∀ depth target, AdvB (body depth target))
    (bodyTypes : ∀ depth target, TypeRun (body depth target)) :
    EmittedBuilder le initial (Goose.Lower.lowerRange type counter upper header body le before).2 := by
  have success : (Op.cmp .lt type counter upper).resultTy (tyEnv le before) = .ok (.data .bool) := by
    simp [Op.resultTy, TyEnv.intTy, TyEnv.dataTy, TyEnv.valTy, tyEnv,
      counterTyped, upperTyped, pure, Except.pure, bind, Except.bind]
  let compared := Goose.Lower.emitDef (.cmp .lt type counter upper) le before
  have comparedBuilder := builder.emitDef (.cmp .lt type counter upper) (fun _ => ⟨.data .bool, success⟩) (by
    intro active value member
    have either : value = counter ∨ value = upper := by simpa [Op.uses] using member
    rcases either with rfl | rfl
    · exact (Array.getElem?_eq_some_iff.mp counterTyped).1
    · exact (Array.getElem?_eq_some_iff.mp upperTyped).1)
  have comparisonTyped := (emitDef_recorded live success).2.2.1
  have retainedCounter := (types_emitDef (.cmp .lt type counter upper) le before _ _ rfl) counter (.data (.int type)) counterTyped
  have output := emitted_checked_loopBody comparedBuilder compared.1
    (fun _ => (Array.getElem?_eq_some_iff.mp comparisonTyped).1) body
    (Goose.Lower.rangeBack type counter header)
    (fun depth target initial started builder retained =>
      bodyChecked depth target initial started builder (retained counter (.data (.int type)) retainedCounter)
        ((types_emitDef (.cmp .lt type counter upper) le before _ _ rfl).trans retained))
    bodyAdvance bodyTypes
    (fun _ _ builder retained => builder.rangeBack type counter header (retained counter (.data (.int type)) retainedCounter))
    (advB_rangeBack _ _ _)
  exact output

end Goose.Lower.Validation
