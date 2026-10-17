import Goose.Lower.Validation.SummaryPreservationReplayLoopsBuilder

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.GIR

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

set_option maxHeartbeats 1200000

theorem loopBody (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (condition : ValueId) (conditionBound : condition < ls.vals.size)
    (live : ls.cur.isSome = true)
    (body : Nat → BlockId → B ValueId) (back : B Unit)
    (bodyAdv : ∀ depth exit, AdvB (body depth exit)) (backAdv : AdvB back)
    (bodyStep : ∀ depth exit state provenance,
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      exit < state.blocks.size → ls.blocks.size ≤ state.blocks.size → ls.vals.size ≤ state.vals.size →
      (∀ index, index < upper.vals.size → rootsAt provenance.vals index = rootsAt upper.vals index) →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots (body depth exit le state).2 next ∧
        ∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index)
    (backStep : ∀ state provenance,
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      ls.blocks.size ≤ state.blocks.size → ls.vals.size ≤ state.vals.size →
      (∀ index, index < upper.vals.size → rootsAt provenance.vals index = rootsAt upper.vals index) →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots (back le state).2 next ∧
        ∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (Goose.Lower.loopBody condition body back le ls).2 next ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  cases current : ls.cur with
  | none => simp [current] at live
  | some block =>
    let split := fork condition le ls
    have splitReady := ready.loopFork condition conditionBound
    have ids := fork_ids (show fork condition le ls = (split.1, split.2) from rfl)
    have bodyBound : split.1.1 < split.2.blocks.size := by
      rw [ids.1, ids.2]
      dsimp only
      exact Nat.lt_add_of_pos_right (by decide : 0 < 2)
    have exitBound : split.1.2 < split.2.blocks.size := by
      rw [ids.1, ids.2]
      dsimp only
      exact Nat.add_lt_add_left (by decide : 1 < 2) ls.blocks.size
    have splitValues : split.2.vals = ls.vals := by simp [split, fork_run _ _ current]
    let started := (Goose.Lower.setCur (some split.1.1) le split.2).2
    have startReady := splitReady.setCur (some split.1.1) (by intro b row; cases row; exact bodyBound)
    have startBlocks : started.blocks.size = split.2.blocks.size := by rfl
    have startValues : started.vals = ls.vals := splitValues
    have blocksGrow : ls.blocks.size ≤ started.blocks.size := by omega
    have valuesGrow : ls.vals.size ≤ started.vals.size := by
      rw [startValues]
      exact Nat.le_refl _
    obtain ⟨bodyProv, bodyReady, bodyGrowth⟩ := bodyStep ls.stack.length split.1.2 started upper
      startReady (by simpa only [startBlocks] using exitBound) blocksGrow valuesGrow (fun _ _ => rfl)
    let bodyState := (body ls.stack.length split.1.2 le started).2
    have bodyAdvanced := bodyAdv ls.stack.length split.1.2 le started
      (body ls.stack.length split.1.2 le started).1 bodyState rfl
    have bodyBlocks : ls.blocks.size ≤ bodyState.blocks.size := Nat.le_trans blocksGrow bodyAdvanced.ext.1
    have bodyValues : ls.vals.size ≤ bodyState.vals.size := Nat.le_trans valuesGrow bodyAdvanced.vals
    obtain ⟨next, backReady, backGrowth⟩ := backStep bodyState bodyProv bodyReady bodyBlocks bodyValues bodyGrowth
    let backState := (back le bodyState).2
    have backAdvanced := backAdv le bodyState (back le bodyState).1 backState rfl
    have finalExit : split.1.2 < backState.blocks.size :=
      Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le exitBound bodyAdvanced.ext.1) backAdvanced.ext.1
    have finished := backReady.setCur (some split.1.2) (by intro b row; cases row; exact finalExit)
    have whole : Goose.Lower.loopBody condition body back le ls =
        Goose.Lower.setCur (some split.1.2) le backState := by
      simp only [Goose.Lower.loopBody, bind_run, get_apply]
      rfl
    refine ⟨next, ?_, ?_⟩
    · simpa only [whole] using finished
    · intro index bound
      have bodySize : upper.vals.size ≤ bodyProv.vals.size := by
        rw [ready.roots.valueSize, bodyReady.roots.valueSize]
        exact bodyValues
      rw [backGrowth index (Nat.lt_of_lt_of_le bound bodySize), bodyGrowth index bound]

theorem loopWhile (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (header : BlockId) (condition : B ValueId) (body : Nat → BlockId → B ValueId)
    (headerBound : header < ls.blocks.size) (conditionAdv : AdvB condition)
    (bodyAdv : ∀ depth exit, AdvB (body depth exit))
    (conditionStep : ∃ next, ReplayBuilder module results vt func target le scopeCount slots (condition le ls).2 next ∧
      ((condition le ls).2.cur.isSome = true → (condition le ls).1 < (condition le ls).2.vals.size) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index)
    (bodyStep : ∀ depth exit state provenance,
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      header < state.blocks.size → exit < state.blocks.size →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots (body depth exit le state).2 next ∧
        ∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerWhile header condition body le ls).2 next ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  obtain ⟨conditionProv, conditionReady, conditionBound, conditionGrowth⟩ := conditionStep
  have advanced := conditionAdv le ls (condition le ls).1 (condition le ls).2 rfl
  have headerStill := Nat.lt_of_lt_of_le headerBound advanced.ext.1
  cases current : (condition le ls).2.cur with
  | none =>
    have whole : lowerWhile header condition body le ls = ((), (condition le ls).2) := by
      simp only [lowerWhile, bind_run, whenLive_none _ _ _ current]
    exact ⟨conditionProv, by simpa only [whole] using conditionReady, conditionGrowth⟩
  | some block =>
    have live : (condition le ls).2.cur.isSome = true := by simp [current]
    obtain ⟨next, nextReady, growth⟩ := conditionReady.loopBody (condition le ls).1 (conditionBound live) live
      body (emitTerm (.br header [])) bodyAdv (advB_emitTerm _)
      (by
        intro depth exit state provenance ready exitBound blocks values priorRoots
        exact bodyStep depth exit state provenance ready (Nat.lt_of_lt_of_le headerStill blocks) exitBound)
      (by
        intro state provenance ready blocks values priorRoots
        exact ⟨provenance, ready.loopBranch header [] (Nat.lt_of_lt_of_le headerStill blocks)
          (by simp) (by simp), fun _ _ => rfl⟩)
    have whole : lowerWhile header condition body le ls =
        Goose.Lower.loopBody (condition le ls).1 body (emitTerm (.br header [])) le (condition le ls).2 := by
      simp only [lowerWhile, bind_run, whenLive_some _ _ _ current]
    refine ⟨next, by simpa only [whole] using nextReady, ?_⟩
    intro index bound
    have bound' : index < conditionProv.vals.size := by
      rw [conditionReady.roots.valueSize]
      exact Nat.lt_of_lt_of_le (by simpa only [ready.roots.valueSize] using bound) advanced.vals
    rw [growth index bound', conditionGrowth index bound]

#print axioms loopBody
#print axioms loopWhile

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
