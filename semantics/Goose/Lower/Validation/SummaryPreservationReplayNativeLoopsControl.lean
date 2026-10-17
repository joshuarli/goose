import Goose.Lower.Validation.SummaryPreservationReplayNativeLoopsStages

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.GIR

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem loopBodyNative (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (expected : List RootRef) (condition : ValueId) (conditionBound : condition < ls.vals.size)
    (live : ls.cur.isSome = true) (body : Nat → BlockId → B ValueId) (back : B Unit)
    (generated : GeneratedBuilderState ls)
    (native : NativeRows vt (Goose.Lower.loopBody condition body back le ls).2)
    (bodyAdv : ∀ depth exit, AdvB (body depth exit)) (backAdv : AdvB back)
    (backTypes : TypeRun back) (backReturns : ReturnFrameRun back)
    (bodyStep :
      let split := fork condition le ls
      let started := loopBodyEntry condition le ls
      ReplayBuilder module results vt func target le scopeCount slots started upper →
      GeneratedBuilderState started →
      NativeRows vt (body ls.stack.length split.1.2 le started).2 →
      split.1.2 < started.blocks.size → ls.blocks.size ≤ started.blocks.size → ls.vals.size ≤ started.vals.size →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (body ls.stack.length split.1.2 le started).2 next ∧
        (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
        ReturnBoundsPreserved expected started upper (body ls.stack.length split.1.2 le started).2 next)
    (backStep : ∀ state provenance,
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      ls.blocks.size ≤ state.blocks.size → ls.vals.size ≤ state.vals.size →
      (∀ old, old < upper.vals.size → rootsAt provenance.vals old = rootsAt upper.vals old) →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots (back le state).2 next ∧
        ∀ old, old < provenance.vals.size → rootsAt next.vals old = rootsAt provenance.vals old) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (Goose.Lower.loopBody condition body back le ls).2 next ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      ReturnBoundsPreserved expected ls upper (Goose.Lower.loopBody condition body back le ls).2 next := by
  cases current : ls.cur with
  | none => simp [current] at live
  | some block =>
    let split := fork condition le ls
    let started := loopBodyEntry condition le ls
    have splitReady := ready.loopFork condition conditionBound
    have ids := fork_ids (show fork condition le ls = (split.1, split.2) from rfl)
    have bodyBound : split.1.1 < split.2.blocks.size := by
      rw [ids.1, ids.2]
      exact Nat.lt_add_of_pos_right (by decide : 0 < 2)
    have exitBound : split.1.2 < split.2.blocks.size := by
      rw [ids.1, ids.2]
      exact Nat.add_lt_add_left (by decide : 1 < 2) ls.blocks.size
    have startReady := splitReady.setCur (some split.1.1) (by intro b row; cases row; exact bodyBound)
    have startValues : started.vals = ls.vals := by
      change split.2.vals = ls.vals
      simp [split, fork_run _ _ current]
    have blocksGrow : ls.blocks.size ≤ started.blocks.size := by
      change ls.blocks.size ≤ split.2.blocks.size
      rw [ids.2]
      omega
    have valuesGrow : ls.vals.size ≤ started.vals.size := by rw [startValues]; exact Nat.le_refl _
    obtain ⟨startedGenerated, bodyNative, entryReturns, finalReturns⟩ := native_loopBody_stages generated native backTypes backReturns
    obtain ⟨bodyProv, bodyReady, bodyGrowth, bodyTransfer⟩ := bodyStep startReady startedGenerated bodyNative exitBound blocksGrow valuesGrow
    let produced := body ls.stack.length split.1.2 le started
    have advanced := bodyAdv ls.stack.length split.1.2 le started produced.1 produced.2 rfl
    obtain ⟨next, backReady, backGrowth⟩ := backStep produced.2 bodyProv bodyReady
      (Nat.le_trans blocksGrow advanced.ext.1) (Nat.le_trans valuesGrow advanced.vals) bodyGrowth
    let backed := back le produced.2
    have backAdvanced := backAdv le produced.2 backed.1 backed.2 rfl
    have finalExit : split.1.2 < backed.2.blocks.size :=
      Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le exitBound advanced.ext.1) backAdvanced.ext.1
    have finalReady := backReady.setCur (some split.1.2) (by intro b row; cases row; exact finalExit)
    have whole : Goose.Lower.loopBody condition body back le ls = Goose.Lower.setCur (some split.1.2) le backed.2 := by
      simp only [Goose.Lower.loopBody, bind_run, get_apply]
      rfl
    have entryTransfer : ReturnBoundsPreserved expected ls upper started upper :=
      .frame ready.symbols ready.roots.valueSize (fun _ _ => rfl) entryReturns
    have finalTransfer : ReturnBoundsPreserved expected produced.2 bodyProv
        (Goose.Lower.loopBody condition body back le ls).2 next :=
      .frame bodyReady.symbols bodyReady.roots.valueSize backGrowth finalReturns
    refine ⟨next, by simpa only [whole] using finalReady, ?_, entryTransfer.trans (bodyTransfer.trans finalTransfer)⟩
    intro old bound
    have bodyBound : old < bodyProv.vals.size := by
      rw [bodyReady.roots.valueSize]
      exact Nat.lt_of_lt_of_le (by simpa only [ready.roots.valueSize] using bound) (Nat.le_trans valuesGrow advanced.vals)
    rw [backGrowth old bodyBound, bodyGrowth old bound]

#print axioms loopBodyNative

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
