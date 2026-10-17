import Goose.Lower.Validation.EmittedTypingCheckpoints
import Goose.Lower.Validation.EmittedTypingControl

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem EmittedBuilder.fork {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (condition : ValueId)
    (conditionBound : before.cur.isSome = true → condition < before.vals.size) :
    EmittedBuilder le initial (Goose.Lower.fork condition le before).2 := by
  let first := Goose.Lower.newBlock [] le before
  let second := Goose.Lower.newBlock [] le first.2
  have firstBuilder := builder.newBlock []
  have secondBuilder := firstBuilder.newBlock []
  have closed := secondBuilder.emitTerm (.condbr condition first.1.1 [] second.1.1 []) (by
    intro active value member
    have same : value = condition := by simpa [Term.uses] using member
    subst value
    exact conditionBound active)
  simpa only [Goose.Lower.fork, bind_run, pure_run, first, second] using closed

theorem EmittedBuilder.scFork {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (isAnd : Bool) (condition : ValueId)
    (conditionBound : before.cur.isSome = true → condition < before.vals.size) :
    EmittedBuilder le initial (Goose.Lower.scFork isAnd condition le before).2 := by
  let first := Goose.Lower.newBlock [] le before
  let second := Goose.Lower.newBlock [.data .bool] le first.2
  have firstBuilder := builder.newBlock []
  have secondBuilder := firstBuilder.newBlock [.data .bool]
  have retainedBound : before.vals.size ≤ second.2.vals.size := by
    dsimp [first, second]
    simp [newBlock_run_general, array_size_pushParamTypes]
  cases isAnd
  · have closed := secondBuilder.emitTerm (.condbr condition second.1.1 [condition] first.1.1 []) (by
      intro active value member
      have same : value = condition := by simpa [Term.uses] using member
      subst value
      exact Nat.lt_of_lt_of_le (conditionBound active) retainedBound)
    simpa only [Goose.Lower.scFork, bind_run, pure_run, first, second, Bool.false_eq_true, reduceIte] using closed
  · have closed := secondBuilder.emitTerm (.condbr condition first.1.1 [] second.1.1 [condition]) (by
      intro active value member
      have same : value = condition := by simpa [Term.uses] using member
      subst value
      exact Nat.lt_of_lt_of_le (conditionBound active) retainedBound)
    simpa only [Goose.Lower.scFork, bind_run, pure_run, first, second, reduceIte] using closed

theorem EmittedBuilder.pushScope {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (scope : ScopeId) :
    EmittedBuilder le initial (Goose.Lower.pushScope scope le before).2 :=
  builder.of_unchanged _ rfl rfl rfl

theorem EmittedBuilder.popScope {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) :
    EmittedBuilder le initial (Goose.Lower.popScope le before).2 :=
  builder.of_unchanged _ rfl rfl rfl

theorem EmittedBuilder.leaveAll {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (scopes : List ScopeId) :
    EmittedBuilder le initial (Goose.Lower.leaveAll scopes le before).2 := by
  induction scopes generalizing before with
  | nil => exact builder
  | cons scope rest inductionHypothesis =>
    have left := builder.emitEffect (.leave scope) (by intro active value member; simp [Effect.uses] at member)
    exact inductionHypothesis left

theorem EmittedBuilder.leaveTo {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (depth : Nat) :
    EmittedBuilder le initial (Goose.Lower.leaveTo depth le before).2 :=
  builder.leaveAll _


theorem EmittedBuilder.patchBrs {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (join : BlockId) (incoming : List (BlockId × ValueId))
    (bounded : ∀ pair ∈ incoming, pair.2 < before.vals.size) :
    EmittedBuilder le initial (Goose.Lower.patchBrs join incoming le before).2 := by
  induction incoming generalizing before with
  | nil => exact builder
  | cons pair rest inductionHypothesis =>
    have patched := builder.patchTerm pair.1 (.br join [pair.2]) (by
      intro value member
      have same : value = pair.2 := by simpa [Term.uses] using member
      subst value
      exact bounded pair (by simp))
    exact inductionHypothesis patched (fun next member => bounded next (by simp [member]))

theorem EmittedBuilder.patchBrs0 {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (join : BlockId) (incoming : List BlockId) :
    EmittedBuilder le initial (Goose.Lower.patchBrs0 join incoming le before).2 := by
  induction incoming generalizing before with
  | nil => exact builder
  | cons block rest inductionHypothesis =>
    have patched := builder.patchTerm block (.br join []) (by intro value member; simp [Term.uses] at member)
    exact inductionHypothesis patched

theorem EmittedBuilder.joinLive {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (incoming : List (BlockId × ValueId))
    (bounded : ∀ pair ∈ incoming, pair.2 < before.vals.size) :
    EmittedBuilder le initial ((do
      let type ← Goose.Lower.valTy (incoming.headD (0, 0)).2
      let (join, params) ← Goose.Lower.newBlock [type]
      Goose.Lower.patchBrs join incoming
      Goose.Lower.setCur (some join)
      Pure.pure (params.headD 0) : B ValueId) le before).2 := by
  let type := (Goose.Lower.valTy (incoming.headD (0, 0)).2 le before).1
  let allocated := Goose.Lower.newBlock [type] le before
  let patched := Goose.Lower.patchBrs allocated.1.1 incoming le allocated.2
  have allocatedBuilder := builder.newBlock [type]
  have patchedBuilder := allocatedBuilder.patchBrs allocated.1.1 incoming (by
    intro pair member
    exact Nat.lt_of_lt_of_le (bounded pair member) (emittedTypePrefix_newBlock [type] le before).size)
  have resumed := patchedBuilder.setCur (some allocated.1.1) (by
    intro block current
    have same : block = before.blocks.size := (Option.some.inj current).symm
    subst block
    have size : allocated.2.blocks.size = patched.2.blocks.size := patchBrs_size incoming rfl
    rw [← size]
    simp [allocated, newBlock_run_general])
  simpa only [bind_run, valTy_run, pure_run, type, allocated, patched] using resumed

theorem EmittedBuilder.joinEmpty {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (incoming : List BlockId) :
    EmittedBuilder le initial ((do
      let (join, _) ← Goose.Lower.newBlock []
      Goose.Lower.patchBrs0 join incoming
      Goose.Lower.setCur (some join) : B Unit) le before).2 := by
  let allocated := Goose.Lower.newBlock [] le before
  let patched := Goose.Lower.patchBrs0 allocated.1.1 incoming le allocated.2
  have allocatedBuilder := builder.newBlock []
  have patchedBuilder := allocatedBuilder.patchBrs0 allocated.1.1 incoming
  have resumed := patchedBuilder.setCur (some allocated.1.1) (by
    intro block current
    have same : block = before.blocks.size := (Option.some.inj current).symm
    subst block
    have size : allocated.2.blocks.size = patched.2.blocks.size := patchBrs0_size incoming rfl
    rw [← size]
    simp [allocated, newBlock_run_general])
  simpa only [bind_run, allocated, patched] using resumed

theorem EmittedBuilder.joinValue {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (thenEnd elseEnd : Option BlockId)
    (left right : ValueId) (leftBound : thenEnd.isSome = true → left < before.vals.size)
    (rightBound : elseEnd.isSome = true → right < before.vals.size) :
    EmittedBuilder le initial (Goose.Lower.joinValue thenEnd left elseEnd right le before).2 := by
  cases thenEnd <;> cases elseEnd
  · exact builder.setCur none (by intros; contradiction)
  all_goals
    apply builder.joinLive
    intro pair member
    simp only [Option.map_some, Option.map_none, Option.toList_none, Option.toList_some,
      List.nil_append, List.append_nil, List.mem_append, List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false] at member
    first
    | (subst pair; exact leftBound rfl)
    | (subst pair; exact rightBound rfl)
    | (rcases member with rfl | rfl
       · exact leftBound rfl
       · exact rightBound rfl)

theorem EmittedBuilder.joinArms {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (thenEnd elseEnd : Option BlockId) :
    EmittedBuilder le initial (Goose.Lower.joinArms thenEnd elseEnd le before).2 := by
  cases thenEnd <;> cases elseEnd
  · exact builder.setCur none (by intros; contradiction)
  all_goals exact builder.joinEmpty _


theorem emitted_checked_shortCircuit {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (isAnd : Bool) (condition : ValueId)
    (conditionBound : before.cur.isSome = true → condition < before.vals.size) (rhs : B ValueId)
    (rhsChecked : ∀ initial before, EmittedBuilder le initial before → EmittedBuilder le initial (rhs le before).2)
    (rhsAdvance : AdvB rhs) (rhsBound : ValueRun rhs) :
    EmittedBuilder le initial (Goose.Lower.shortCircuit isAnd condition rhs le before).2 := by
  generalize actionRun : Goose.Lower.shortCircuit isAnd condition rhs le before = actionResult
  obtain ⟨resultValue, after⟩ := actionResult
  dsimp only
  cases live : before.cur with
  | none =>
    simp only [Goose.Lower.shortCircuit, whenLive_none _ _ _ live] at actionRun
    obtain ⟨_, rfl⟩ := Prod.mk.inj actionRun
    exact builder
  | some current =>
    simp only [Goose.Lower.shortCircuit, whenLive_some _ _ _ live, bind_eq] at actionRun
    obtain ⟨⟨rightBlock, joinBlock, parameter⟩, forked, forkRun, u1, started, startRun,
      result, evaluated, rhsRun, u2, closed, closeRun, u3, resumed, resumeRun, pureRun⟩ := actionRun
    have ids := scFork_ids forkRun
    obtain ⟨rightId, restIds⟩ := Prod.mk.inj ids.1
    obtain ⟨joinId, parameterId⟩ := Prod.mk.inj restIds
    subst rightId joinId parameterId
    have forkBuilder := builder.scFork isAnd condition conditionBound
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
    have evaluatedBuilder := rhsChecked initial started startBuilder
    rw [rhsRun] at evaluatedBuilder
    dsimp only at evaluatedBuilder
    have rhsAdv := rhsAdvance le started _ _ rhsRun
    have closedBuilder := evaluatedBuilder.emitTerm (.br (before.blocks.size + 1) [result]) (by
      intro active value member
      have same : value = result := by simpa [Term.uses] using member
      subst value
      exact rhsBound le started result evaluated rhsRun active)
    rw [closeRun] at closedBuilder
    dsimp only at closedBuilder
    have closeAdv := adv_emitTerm closeRun
    have resumedBuilder := closedBuilder.setCur (some (before.blocks.size + 1)) (by
      intro block same
      have id := Option.some.inj same
      subst block
      have size : started.blocks.size = forked.blocks.size := by rw [setCur_run] at startRun; exact congrArg (fun pair => pair.2.blocks.size) startRun.symm
      have forkSize := ids.2
      have evaluatedSize := rhsAdv.ext.1
      have closedSize := closeAdv.ext.1
      nat_omega)
    rw [resumeRun] at resumedBuilder
    dsimp only at resumedBuilder
    rw [pure_run] at pureRun
    obtain ⟨_, rfl⟩ := Prod.mk.inj pureRun
    exact resumedBuilder

end Goose.Lower.Validation
