import Goose.Lower.Validation.SummaryPreservationReplayNativeLoopsControl

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.GIR

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

def nativeRangeBody (type : IntTy) (counter bound : ValueId) (le : LEnv) (state : LS) : LS :=
  let compared := Goose.Lower.emitDef (.cmp .lt type counter bound) le state
  loopBodyEntry compared.1 le compared.2

theorem loopRangeNative (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (expected : List RootRef) (type : IntTy) (counter bound : ValueId) (header : BlockId)
    (body : Nat → BlockId → B ValueId)
    (live : ls.cur.isSome = true) (headerBound : header < ls.blocks.size)
    (counterBound : counter < ls.vals.size) (boundBound : bound < ls.vals.size)
    (counterScalar : rootsAt upper.vals counter = [])
    (generated : GeneratedBuilderState ls)
    (native : NativeRows vt (lowerRange type counter bound header body le ls).2)
    (bodyAdv : ∀ depth exit, AdvB (body depth exit)) (bodyTypes : ∀ depth exit, TypeRun (body depth exit))
    (bodyStep : ∀ provenance,
      let compared := Goose.Lower.emitDef (.cmp .lt type counter bound) le ls
      let split := fork compared.1 le compared.2
      let started := nativeRangeBody type counter bound le ls
      ReplayBuilder module results vt func target le scopeCount slots started provenance →
      GeneratedBuilderState started → NativeRows vt (body compared.2.stack.length split.1.2 le started).2 →
      header < started.blocks.size → split.1.2 < started.blocks.size → counter < started.vals.size →
      rootsAt provenance.vals counter = [] →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (body compared.2.stack.length split.1.2 le started).2 next ∧
        (∀ old, old < provenance.vals.size → rootsAt next.vals old = rootsAt provenance.vals old) ∧
        ReturnBoundsPreserved expected started provenance (body compared.2.stack.length split.1.2 le started).2 next) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots (lowerRange type counter bound header body le ls).2 next ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      ReturnBoundsPreserved expected ls upper (lowerRange type counter bound header body le ls).2 next := by
  let compare := Goose.Lower.emitDef (.cmp .lt type counter bound) le ls
  obtain ⟨compareProv, compareReady, compareValue, compareGrowth⟩ := ready.emitTypedDef (.cmp .lt type counter bound) [] (.data .bool)
    (by simp [Op.uses, counterBound, boundBound]) (by simp [Op.origin]) (by simp [Op.SymbolRefsValid])
    (effectRefinement_empty func target) (fun _ member => by cases member) (fun _ => rfl)
  have compareAdv := advB_emitDef (.cmp .lt type counter bound) le ls compare.1 compare.2 rfl
  have compareGenerated := generated.emitDef _ (rfl : Goose.Lower.emitDef (.cmp .lt type counter bound) le ls = compare)
  have compareLive : compare.2.cur.isSome = true := by
    cases current : ls.cur with
    | none => simp [current] at live
    | some block => simpa [compare, emitDef_run _ _ current, current]
  have headerStill := Nat.lt_of_lt_of_le headerBound compareAdv.ext.1
  have counterStill := Nat.lt_of_lt_of_le counterBound compareAdv.vals
  have counterOld : counter < upper.vals.size := by simpa only [ready.roots.valueSize] using counterBound
  have counterRoots := (compareGrowth counter counterOld).trans counterScalar
  have nativeLoop : NativeRows vt (Goose.Lower.loopBody compare.1 body (rangeBack type counter header) le compare.2).2 := native
  have backReturns : ReturnFrameRun (rangeBack type counter header) :=
    .of_absence (fun _ => ReturnFrames.returnAbsent_rangeBack type counter header)
  obtain ⟨next, nextReady, growth, transfer⟩ := compareReady.loopBodyNative expected compare.1 (compareValue compareLive).bound
    compareLive body (rangeBack type counter header) compareGenerated nativeLoop bodyAdv (advB_rangeBack _ _ _)
    (types_rangeBack _ _ _) backReturns
    (by
      dsimp only
      intro stateReady stateGenerated stateNative exitBound blocks values
      exact bodyStep compareProv stateReady stateGenerated stateNative (Nat.lt_of_lt_of_le headerStill blocks) exitBound
        (Nat.lt_of_lt_of_le counterStill values) counterRoots)
    (by
      intro state provenance stateReady blocks values priorRoots
      exact stateReady.loopRangeBack type counter header (Nat.lt_of_lt_of_le headerStill blocks) (Nat.lt_of_lt_of_le counterStill values))
  have compareReturns : ReturnMembershipFrame ls compare.2 :=
    ReturnFrameRun.of_absence (fun _ => ReturnFrames.returnAbsent_emitDef _) le ls compare.1 compare.2 rfl
  have compareTransfer : ReturnBoundsPreserved expected ls upper compare.2 compareProv :=
    .frame ready.symbols ready.roots.valueSize compareGrowth compareReturns
  refine ⟨next, nextReady, ?_, compareTransfer.trans transfer⟩
  intro old bound
  have compareBound : old < compareProv.vals.size := by
    rw [compareReady.roots.valueSize]
    exact Nat.lt_of_lt_of_le (by simpa only [ready.roots.valueSize] using bound) compareAdv.vals
  rw [growth old compareBound, compareGrowth old bound]

theorem native_range_body_stack (type : IntTy) (counter bound : ValueId) (le : LEnv) (state : LS) :
    (nativeRangeBody type counter bound le state).stack = state.stack := by
  exact (native_loopBody_entry_stack _ _ _).trans (advB_emitDef (.cmp .lt type counter bound) le state _ _ rfl).stack

#print axioms loopRangeNative

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
