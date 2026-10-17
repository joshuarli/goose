import Goose.Lower.Validation.SummaryPreservationReplayLoopsRange
import Goose.Lower.Validation.SummaryPreservationReplayReferences
import Goose.Lower.Validation.SummaryPreservationRefinedEffects

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

private theorem loop_read_refinement {func : Func}
    {upper : Prov} {sourceRoots : List RootRef} {address : ValueId} {target : Core.Eff}
    (closed : ParameterRootsClosed func)
    (refined : RootsRefine func (rootsAt upper.vals address) sourceRoots)
    (reads : ∀ item ∈ func.storageTargets (rootsTargets sourceRoots), item ∈ func.storageTargets target.reads) :
    EffectRefinement func { ({} : Core.Eff) with reads := addTargets [] (rootsTargets (rootsAt upper.vals address)) } target := by
  have read := effectRefinement_addReads closed (effectRefinement_empty func ({} : Core.Eff)) refined
  have empty := effectRefinement_empty func target
  refine ⟨?_, empty.writes, empty.grows, empty.shrinks, empty.rebinds, empty.aborts, empty.outputs, empty.unknown⟩
  intro item member
  have bounded := read.reads item member
  rcases storageTargets_addTargets_origin bounded with impossible | actual
  · simpa [Func.storageTargets] using impossible
  · exact reads item actual

namespace ReplayBuilder

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem loopEachSampled (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (regrow : Bool) (view : ValueId) (viewBound : view < ls.vals.size) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots (eachSampled regrow view le ls).2 next ∧
      (regrow = false → (eachSampled regrow view le ls).2.cur.isSome = true →
        ReplayValue func next (eachSampled regrow view le ls).2 (eachSampled regrow view le ls).1 [] (.data (.int .i64))) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  cases regrow with
  | true => exact ⟨upper, ready, by simp, fun _ _ => rfl⟩
  | false =>
    obtain ⟨next, nextReady, value, growth⟩ := ready.emitTypedDef (.viewLen view) [] (.data (.int .i64))
      (by simpa [Op.uses] using viewBound) (by simp [Op.origin]) (by simp [Op.SymbolRefsValid])
      (effectRefinement_empty func target) (fun _ member => by cases member) (fun _ => rfl)
    exact ⟨next, nextReady, fun _ => value, growth⟩

theorem loopEachLength (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (regrow : Bool) (owner : Option ValueId) (sampled : ValueId) (sourceRoots : List RootRef)
    (closed : ParameterRootsClosed func)
    (input : regrow = true → owner.getD 0 < ls.vals.size ∧ RootsRefine func (rootsAt upper.vals (owner.getD 0)) sourceRoots)
    (reads : regrow = true → ∀ item ∈ func.storageTargets (rootsTargets sourceRoots), item ∈ func.storageTargets target.reads)
    (sample : regrow = false → ReplayValue func upper ls sampled [] (.data (.int .i64))) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots (eachLen regrow owner sampled le ls).2 next ∧
      ((eachLen regrow owner sampled le ls).2.cur.isSome = true →
        ReplayValue func next (eachLen regrow owner sampled le ls).2 (eachLen regrow owner sampled le ls).1 [] (.data (.int .i64))) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  cases regrow with
  | false => exact ⟨upper, ready, fun _ => sample rfl, fun _ _ => rfl⟩
  | true =>
    obtain ⟨bound, refined⟩ := input rfl
    exact ready.emitTypedDef (.arrayLen (owner.getD 0)) [] (.data (.int .i64))
      (by simpa [Op.uses] using bound) (by simp [Op.origin]) (by simp [Op.SymbolRefsValid])
      (loop_read_refinement closed refined (reads rfl)) (fun _ member => by cases member) (fun _ => rfl)

theorem loopEachBorrow (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (variableId : VarId) (address : ValueId) (mutability : Mutability) (element : Ty) (sourceRoots : List RootRef)
    {localVar : LocalVar} (row : le.vars[variableId]? = some localVar) (type : localVar.ty = .ref mutability element)
    (input : ls.cur.isSome = true → address < ls.vals.size ∧ RootsRefine func (rootsAt upper.vals address) sourceRoots) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots (eachElemValue variableId true address le ls).2 next ∧
      ((eachElemValue variableId true address le ls).2.cur.isSome = true →
        ReplayValue func next (eachElemValue variableId true address le ls).2
          (eachElemValue variableId true address le ls).1 sourceRoots (.data (.ref mutability element))) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  simpa only [eachElemValue, ite_true, bind_run, read_apply, row, type] using
    ready.borrowReference mutability element address sourceRoots input

theorem loopEachCopy (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (variableId : VarId) (address : ValueId) (element : Ty) (sourceRoots : List RootRef)
    (closed : ParameterRootsClosed func)
    (input : ls.cur.isSome = true → address < ls.vals.size ∧ RootsRefine func (rootsAt upper.vals address) sourceRoots)
    (reads : ∀ item ∈ func.storageTargets (rootsTargets sourceRoots), item ∈ func.storageTargets target.reads)
    (scalarType : ls.cur.isSome = true → valRefLike vt ls.vals.size = false) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots (eachElemValue variableId false address le ls).2 next ∧
      ((eachElemValue variableId false address le ls).2.cur.isSome = true →
        ReplayValue func next (eachElemValue variableId false address le ls).2
          (eachElemValue variableId false address le ls).1 [] (.data element)) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  apply ready.emitTypedDef_live (.load address) [] (.data element)
  · intro live
    simpa [Op.uses] using (input live).1
  · simp [Op.origin]
  · simp [Op.SymbolRefsValid]
  · intro live
    exact loop_read_refinement closed (input live).2 reads
  · intro live
    simp [rootsOfDef, scalarType live, RootsRefine]
  · intro live _
    simp [rootsOfDef, scalarType live, RootsRefine]

theorem loopEach (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (regrow : Bool) (owner : Option ValueId) (sampled counter : ValueId) (header : BlockId)
    (sourceRoots : List RootRef) (body : Nat → BlockId → B ValueId)
    (live : ls.cur.isSome = true) (headerBound : header < ls.blocks.size)
    (counterBound : counter < ls.vals.size) (counterScalar : rootsAt upper.vals counter = [])
    (closed : ParameterRootsClosed func)
    (input : regrow = true → owner.getD 0 < ls.vals.size ∧ RootsRefine func (rootsAt upper.vals (owner.getD 0)) sourceRoots)
    (reads : regrow = true → ∀ item ∈ func.storageTargets (rootsTargets sourceRoots), item ∈ func.storageTargets target.reads)
    (sample : regrow = false → ReplayValue func upper ls sampled [] (.data (.int .i64)))
    (bodyAdv : ∀ depth exit, AdvB (body depth exit))
    (bodyStep : ∀ depth exit state provenance,
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      header < state.blocks.size → exit < state.blocks.size → counter < state.vals.size → rootsAt provenance.vals counter = [] →
      (∀ index, index < upper.vals.size → rootsAt provenance.vals index = rootsAt upper.vals index) →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots (body depth exit le state).2 next ∧
        ∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots (lowerEach regrow owner sampled header counter body le ls).2 next ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  obtain ⟨lengthProv, lengthReady, lengthValue, lengthGrowth⟩ := ready.loopEachLength regrow owner sampled sourceRoots closed input reads sample
  let length := eachLen regrow owner sampled le ls
  have lengthAdv := advB_eachLen regrow owner sampled le ls length.1 length.2 rfl
  have lengthLive : length.2.cur.isSome = true := by
    cases regrow with
    | false => simpa [length, eachLen, pure_run] using live
    | true =>
      cases current : ls.cur with
      | none => simp [current] at live
      | some block => simpa [length, eachLen, emitDef_run _ _ current, current]
  have oldCounter : counter < upper.vals.size := by simpa only [ready.roots.valueSize] using counterBound
  have lengthCounter : rootsAt lengthProv.vals counter = [] := (lengthGrowth counter oldCounter).trans counterScalar
  let compare := Goose.Lower.emitDef (.cmp .lt .i64 counter length.1) le length.2
  obtain ⟨compareProv, compareReady, compareValue, compareGrowth⟩ :=
    lengthReady.emitTypedDef (.cmp .lt .i64 counter length.1) [] (.data .bool)
      (by
        intro value member
        simp only [Op.uses, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact Nat.lt_of_lt_of_le counterBound lengthAdv.vals
        · exact (lengthValue lengthLive).bound)
      (by simp [Op.origin]) (by simp [Op.SymbolRefsValid])
      (effectRefinement_empty func target) (fun _ member => by cases member) (fun _ => rfl)
  have compareAdv := advB_emitDef (.cmp .lt .i64 counter length.1) le length.2 compare.1 compare.2 rfl
  have compareLive : compare.2.cur.isSome = true := by
    cases current : length.2.cur with
    | none => simp [current] at lengthLive
    | some block => simpa [compare, emitDef_run _ _ current, current]
  have counterLengthBound : counter < lengthProv.vals.size := by
    simpa only [lengthReady.roots.valueSize] using Nat.lt_of_lt_of_le counterBound lengthAdv.vals
  have compareCounter := (compareGrowth counter counterLengthBound).trans lengthCounter
  have headerStill := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le headerBound lengthAdv.ext.1) compareAdv.ext.1
  have counterStill := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le counterBound lengthAdv.vals) compareAdv.vals
  obtain ⟨next, nextReady, growth⟩ := compareReady.loopBody compare.1 (compareValue compareLive).bound compareLive
    body (rangeBack .i64 counter header) bodyAdv (advB_rangeBack _ _ _)
    (by
      intro depth exit state provenance stateReady exitBound blocks values priorRoots
      have compareCounterBound : counter < compareProv.vals.size := by
        simpa only [compareReady.roots.valueSize] using counterStill
      apply bodyStep depth exit state provenance stateReady (Nat.lt_of_lt_of_le headerStill blocks)
        exitBound (Nat.lt_of_lt_of_le counterStill values) ((priorRoots counter compareCounterBound).trans compareCounter)
      intro index bound
      have lengthBound : index < lengthProv.vals.size := by
        rw [lengthReady.roots.valueSize]
        exact Nat.lt_of_lt_of_le (by simpa only [ready.roots.valueSize] using bound) lengthAdv.vals
      have compareBound : index < compareProv.vals.size := by
        rw [compareReady.roots.valueSize]
        exact Nat.lt_of_lt_of_le (by simpa only [lengthReady.roots.valueSize] using lengthBound) compareAdv.vals
      rw [priorRoots index compareBound, compareGrowth index lengthBound, lengthGrowth index bound])
    (by
      intro state provenance stateReady blocks values priorRoots
      exact stateReady.loopRangeBack .i64 counter header (Nat.lt_of_lt_of_le headerStill blocks)
        (Nat.lt_of_lt_of_le counterStill values))
  refine ⟨next, ?_, ?_⟩
  · simpa only [lowerEach, bind_run] using nextReady
  · intro index bound
    have lengthBound : index < lengthProv.vals.size := by
      rw [lengthReady.roots.valueSize]
      exact Nat.lt_of_lt_of_le (by simpa only [ready.roots.valueSize] using bound) lengthAdv.vals
    have compareBound : index < compareProv.vals.size := by
      rw [compareReady.roots.valueSize]
      exact Nat.lt_of_lt_of_le (by simpa only [lengthReady.roots.valueSize] using lengthBound) compareAdv.vals
    rw [growth index compareBound, compareGrowth index lengthBound, lengthGrowth index bound]

#print axioms loopEachSampled
#print axioms loopEachLength
#print axioms loopEachBorrow
#print axioms loopEachCopy
#print axioms loopEach

end ReplayBuilder

end Goose.Lower.Validation.SummaryPreservation
