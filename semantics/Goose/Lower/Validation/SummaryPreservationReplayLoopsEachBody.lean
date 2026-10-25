import Goose.Lower.Validation.SummaryPreservationReplayLoopsEachContracts

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

private theorem each_emit_cur (op : Op) (le : LEnv) (ls : LS) :
    (Goose.Lower.emitDef op le ls).2.cur = ls.cur := by
  cases current : ls.cur <;> simp [emitDef_run, current, emitDef_none]

private theorem each_borrow_cur (mu : Mutability) (value : ValueId) (le : LEnv) (ls : LS) :
    (borrowTo mu value le ls).2.cur = ls.cur := by
  rcases borrowTo_ref_cases (show borrowTo mu value le ls = ((borrowTo mu value le ls).1, (borrowTo mu value le ls).2) from rfl) with same | frozen | borrowed
  · exact congrArg LS.cur same.2
  · exact (congrArg (fun run => run.2.cur) frozen).symm.trans (each_emit_cur _ _ _)
  · exact (congrArg (fun run => run.2.cur) borrowed).symm.trans (each_emit_cur _ _ _)

namespace ReplayBuilder

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem loopEachAddress (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (view counter : ValueId) (element : Ty) (sourceRoots : List RootRef)
    (viewBound : view < ls.vals.size) (counterBound : counter < ls.vals.size)
    (refined : RootsRefine func (rootsAt upper.vals view) sourceRoots) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (Goose.Lower.emitDef (.refElem view counter) le ls).2 next ∧
      ((Goose.Lower.emitDef (.refElem view counter) le ls).2.cur.isSome = true →
        ReplayValue func next (Goose.Lower.emitDef (.refElem view counter) le ls).2
          (Goose.Lower.emitDef (.refElem view counter) le ls).1 sourceRoots (.data (.ref .readOnly element))) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  apply ready.emitTypedDef (.refElem view counter) sourceRoots (.data (.ref .readOnly element))
  · intro value member
    simp only [Op.uses, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact viewBound
    · exact counterBound
  · simp [Op.origin]
  · simp [Op.SymbolRefsValid]
  · exact effectRefinement_empty func target
  · exact refined
  · simp [VTy.refLike, Ty.isRefLike]

theorem loopEachValue (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (variableId address : Nat) (byRef : Bool) (element : Ty) (sourceRoots : List RootRef)
    (live : ls.cur.isSome = true)
    (input : address < ls.vals.size ∧ RootsRefine func (rootsAt upper.vals address) sourceRoots)
    (closed : ParameterRootsClosed func)
    (reference : byRef = true → ∃ localVar mu, le.vars[variableId]? = some localVar ∧ localVar.ty = .ref mu element)
    (reads : byRef = false → ∀ item ∈ func.storageTargets (rootsTargets sourceRoots), item ∈ func.storageTargets target.reads)
    (scalarType : byRef = false → valRefLike vt ls.vals.size = false)
    (flat : element.isRefLike = false) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots (eachElemValue variableId byRef address le ls).2 next ∧
      (eachElemValue variableId byRef address le ls).2.cur.isSome = true ∧
      (eachElemValue variableId byRef address le ls).1 < (eachElemValue variableId byRef address le ls).2.vals.size ∧
      (byRef = true → RootsRefine func (rootsAt next.vals (eachElemValue variableId byRef address le ls).1) sourceRoots) ∧
      (byRef = false → rootsAt next.vals (eachElemValue variableId byRef address le ls).1 = []) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  cases byRef with
  | true =>
    obtain ⟨localVar, mu, row, type⟩ := reference rfl
    obtain ⟨next, nextReady, value, growth⟩ := ready.loopEachBorrow variableId address mu element sourceRoots row type (fun _ => input)
    have nextLive : (eachElemValue variableId true address le ls).2.cur.isSome = true := by
      simpa only [eachElemValue, ite_true, bind_run, read_apply, row, type, each_borrow_cur] using live
    exact ⟨next, nextReady, nextLive, (value nextLive).bound, fun _ => (value nextLive).refined, by simp, growth⟩
  | false =>
    obtain ⟨next, nextReady, value, growth⟩ := ready.loopEachCopy variableId address element sourceRoots closed (fun _ => input) (reads rfl) (fun _ => scalarType rfl)
    have nextLive : (eachElemValue variableId false address le ls).2.cur.isSome = true := by
      simpa only [eachElemValue, Bool.false_eq_true, ite_false, each_emit_cur] using live
    exact ⟨next, nextReady, nextLive, (value nextLive).bound, by simp,
      fun _ => (value nextLive).scalar (by simpa [VTy.refLike] using flat), growth⟩

theorem loopEachBody (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (variableId : VarId) (indexVar : Option VarId) (byRef : Bool) (view counter : ValueId)
    (element : Ty) (sourceRoots : List RootRef) (origin : OriginId)
    (depth : Nat) (header exit : BlockId) (body : Core.Block)
    (live : ls.cur.isSome = true) (viewBound : view < ls.vals.size) (counterBound : counter < ls.vals.size)
    (refined : RootsRefine func (rootsAt upper.vals view) sourceRoots)
    (counterScalar : rootsAt upper.vals counter = [])
    (closed : ParameterRootsClosed func)
    (reference : byRef = true → ∃ localVar mu, le.vars[variableId]? = some localVar ∧ localVar.ty = .ref mu element)
    (reads : byRef = false → ∀ item ∈ func.storageTargets (rootsTargets sourceRoots), item ∈ func.storageTargets target.reads)
    (scalarType : byRef = false → valRefLike vt (Goose.Lower.emitDef (.refElem view counter) le ls).2.vals.size = false)
    (flat : element.isRefLike = false)
    (binding : byRef = true → ∀ actual, RootsRefine func actual sourceRoots →
      ∀ root ∈ actual, root ∈ rootsAt slots variableId)
    (bodyStep : ∀ value state provenance,
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      ls.blocks.size ≤ state.blocks.size →
      (∀ item ∈ (variableId, value, origin) :: indexVar.toList.map (fun j => (j, counter, origin)), item.2.1 < state.vals.size) →
      (∀ item ∈ (variableId, value, origin) :: indexVar.toList.map (fun j => (j, counter, origin)),
        ∀ root ∈ rootsAt provenance.vals item.2.1, root ∈ rootsAt slots item.1) →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩)
          ((variableId, value, origin) :: indexVar.toList.map (fun j => (j, counter, origin))) false body le state).2 next ∧
        ∀ i, i < provenance.vals.size → rootsAt next.vals i = rootsAt provenance.vals i) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
      ((do
        let address ← Goose.Lower.emitDef (.refElem view counter)
        let value ← eachElemValue variableId byRef address
        lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩)
          ((variableId, value, origin) :: indexVar.toList.map (fun j => (j, counter, origin))) false body) le ls).2 next ∧
      ∀ i, i < upper.vals.size → rootsAt next.vals i = rootsAt upper.vals i := by
  let address := Goose.Lower.emitDef (.refElem view counter) le ls
  obtain ⟨addressProv, addressReady, addressValue, addressGrowth⟩ := ready.loopEachAddress view counter element sourceRoots viewBound counterBound refined
  have addressLive : address.2.cur.isSome = true := by simpa only [address, each_emit_cur] using live
  have addressAdv := advB_emitDef (.refElem view counter) le ls address.1 address.2 rfl
  let value := eachElemValue variableId byRef address.1 le address.2
  obtain ⟨valueProv, valueReady, valueLive, valueBound, valueReference, valueScalar, valueGrowth⟩ :=
    addressReady.loopEachValue variableId address.1 byRef element sourceRoots addressLive
      ⟨(addressValue addressLive).bound, (addressValue addressLive).refined⟩ closed reference reads scalarType flat
  have valueAdv := advB_eachElemValue variableId byRef address.1 le address.2 value.1 value.2 rfl
  have counterOld : counter < upper.vals.size := by simpa only [ready.roots.valueSize] using counterBound
  have counterAddress : counter < addressProv.vals.size := by
    rw [addressReady.roots.valueSize]
    exact Nat.lt_of_lt_of_le counterBound addressAdv.vals
  have counterEmpty : rootsAt valueProv.vals counter = [] :=
    (valueGrowth counter counterAddress).trans ((addressGrowth counter counterOld).trans counterScalar)
  obtain ⟨next, nextReady, bodyGrowth⟩ := bodyStep value.1 value.2 valueProv valueReady (Nat.le_trans addressAdv.ext.1 valueAdv.ext.1)
    (by
      intro item member
      simp only [List.mem_cons, List.mem_map] at member
      rcases member with rfl | ⟨j, _, rfl⟩
      · exact valueBound
      · exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le counterBound addressAdv.vals) valueAdv.vals)
    (by
      intro item member root rootMember
      simp only [List.mem_cons, List.mem_map] at member
      rcases member with rfl | ⟨j, _, rfl⟩
      · cases byRef with
        | true => exact binding rfl _ (valueReference rfl) root rootMember
        | false =>
          have empty := valueScalar rfl
          change rootsAt valueProv.vals value.1 = [] at empty
          rw [empty] at rootMember
          exact False.elim (List.not_mem_nil rootMember)
      · rw [counterEmpty] at rootMember
        exact False.elim (List.not_mem_nil rootMember))
  refine ⟨next, ?_, ?_⟩
  · simpa only [bind_run] using nextReady
  · intro i bound
    have addressBound : i < addressProv.vals.size := by
      rw [addressReady.roots.valueSize]
      exact Nat.lt_of_lt_of_le (by simpa only [ready.roots.valueSize] using bound) addressAdv.vals
    have valueBound : i < valueProv.vals.size := by
      rw [valueReady.roots.valueSize]
      exact Nat.lt_of_lt_of_le (by simpa only [addressReady.roots.valueSize] using addressBound) valueAdv.vals
    rw [bodyGrowth i valueBound, valueGrowth i addressBound, addressGrowth i bound]

#print axioms loopEachBody

#print axioms loopEachAddress
#print axioms loopEachValue

end ReplayBuilder
end Goose.Lower.Validation.SummaryPreservation
