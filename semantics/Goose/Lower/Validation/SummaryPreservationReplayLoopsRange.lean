import Goose.Lower.Validation.SummaryPreservationReplayLoopsControl

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.GIR

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem loopRange (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (type : IntTy) (counter bound : ValueId) (header : BlockId) (body : Nat → BlockId → B ValueId)
    (live : ls.cur.isSome = true) (headerBound : header < ls.blocks.size)
    (counterBound : counter < ls.vals.size) (boundBound : bound < ls.vals.size)
    (counterScalar : rootsAt upper.vals counter = [])
    (bodyAdv : ∀ depth exit, AdvB (body depth exit))
    (bodyStep : ∀ depth exit state provenance,
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      header < state.blocks.size → exit < state.blocks.size → counter < state.vals.size →
      rootsAt provenance.vals counter = [] →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots (body depth exit le state).2 next ∧
        ∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerRange type counter bound header body le ls).2 next ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  let compare := Goose.Lower.emitDef (.cmp .lt type counter bound) le ls
  obtain ⟨compareProv, compareReady, compareValue, compareGrowth⟩ :=
    ready.emitTypedDef (.cmp .lt type counter bound) [] (.data .bool)
      (by simp [Op.uses, counterBound, boundBound]) (by simp [Op.origin]) (by simp [Op.SymbolRefsValid])
      (effectRefinement_empty func target) (fun _ member => by cases member) (fun _ => rfl)
  have compareAdvanced := advB_emitDef (.cmp .lt type counter bound) le ls compare.1 compare.2 rfl
  have headerStill := Nat.lt_of_lt_of_le headerBound compareAdvanced.ext.1
  have counterStill := Nat.lt_of_lt_of_le counterBound compareAdvanced.vals
  have compareLive : compare.2.cur.isSome = true := by
    cases current : ls.cur with
    | none => simp [current] at live
    | some block => simpa [compare, emitDef_run _ _ current, current]
  have counterOld : counter < upper.vals.size := by simpa only [ready.roots.valueSize] using counterBound
  have counterRoots : rootsAt compareProv.vals counter = [] := (compareGrowth counter counterOld).trans counterScalar
  obtain ⟨next, nextReady, growth⟩ := compareReady.loopBody compare.1 (compareValue compareLive).bound compareLive
    body (rangeBack type counter header) bodyAdv (advB_rangeBack _ _ _)
    (by
      intro depth exit state provenance stateReady stateEq stateLive exitBound blocks values priorRoots
      have oldBound : counter < compareProv.vals.size := by
        simpa only [compareReady.roots.valueSize] using counterStill
      exact bodyStep depth exit state provenance stateReady (Nat.lt_of_lt_of_le headerStill blocks)
        exitBound (Nat.lt_of_lt_of_le counterStill values)
        ((priorRoots counter oldBound).trans counterRoots))
    (by
      intro state provenance stateReady blocks values priorRoots
      exact stateReady.loopRangeBack type counter header (Nat.lt_of_lt_of_le headerStill blocks)
        (Nat.lt_of_lt_of_le counterStill values))
  refine ⟨next, ?_, ?_⟩
  · simpa only [lowerRange, bind_run] using nextReady
  · intro index oldBound
    have compareBound : index < compareProv.vals.size := by
      rw [compareReady.roots.valueSize]
      exact Nat.lt_of_lt_of_le (by simpa only [ready.roots.valueSize] using oldBound) compareAdvanced.vals
    rw [growth index compareBound, compareGrowth index oldBound]

#print axioms loopRange

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
