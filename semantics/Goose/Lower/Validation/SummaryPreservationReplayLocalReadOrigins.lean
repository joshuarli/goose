import Goose.Lower.Validation.SummaryPreservationReplayLiveEmit
import Goose.Lower.Validation.SummaryPreservationReads

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

theorem recordReadValueRootRecipe_frame (value : ValueId) (place : Place) (le : LEnv) (state : LS) :
    (Goose.Lower.recordReadValueRootRecipe value place le state).2 =
      { state with valueRootRecipes := (Goose.Lower.recordReadValueRootRecipe value place le state).2.valueRootRecipes } := by
  cases place with
  | var variableId =>
    simp only [Goose.Lower.recordReadValueRootRecipe_run]
    by_cases source : (le.vars[variableId]?).any (fun localVar => localVar.ty.isRefSlice) = true
    · simp only [source, ite_true, Goose.Lower.recordValueRootSource_run]
    · simp [source]
  | global _ => rfl
  | deref _ => rfl
  | field _ _ => rfl
  | elem _ _ _ => rfl

theorem readValue_eq (place : Place) (le : LEnv) (state : LS) :
    (lowerExpr (.read place) le state).1 =
      (Goose.Lower.emitDef (.load (lowerPlace place le state).1) le (lowerPlace place le state).2).1 := rfl

theorem readCurrent_eq (place : Place) (le : LEnv) (state : LS) :
    (lowerExpr (.read place) le state).2.cur =
      (Goose.Lower.emitDef (.load (lowerPlace place le state).1) le (lowerPlace place le state).2).2.cur := by
  rw [lowerExpr_read_run]
  dsimp only
  rw [recordReadValueRootRecipe_frame]

theorem readValues_eq (place : Place) (le : LEnv) (state : LS) :
    (lowerExpr (.read place) le state).2.vals =
      (Goose.Lower.emitDef (.load (lowerPlace place le state).1) le (lowerPlace place le state).2).2.vals := by
  rw [lowerExpr_read_run]
  dsimp only
  rw [recordReadValueRootRecipe_frame]

theorem readBlocks_eq (place : Place) (le : LEnv) (state : LS) :
    (lowerExpr (.read place) le state).2.blocks =
      (Goose.Lower.emitDef (.load (lowerPlace place le state).1) le (lowerPlace place le state).2).2.blocks := by
  rw [lowerExpr_read_run]
  dsimp only
  rw [recordReadValueRootRecipe_frame]

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem localReadWithOrigins {env : PEnv} {variableId : VarId} {localVar : LocalVar}
    {before after : RState} {sourceRoots : List RootRef}
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (variableRow : env.impl.vars[variableId]? = some localVar)
    (source : rpExpr env (.read (.var variableId)) before = .ok (sourceRoots, after))
    (slotBound : variableId < le.slots.size)
    (chosen : List RootRef)
    (included : ls.cur.isSome = true → (if valRefLike vt (ls.vals.size + 1) then rootsAt slots variableId else []) ⊆ chosen)
    (refined : ls.cur.isSome = true → RootsRefine func chosen sourceRoots)
    (scalar : ls.cur.isSome = true → localVar.ty.isRefLike = false → chosen = [])
    (rows : ∀ value afterLoad,
      Goose.Lower.emitDef (.load (Goose.Lower.emitDef (.slotAddr variableId) le ls).1) le
        (Goose.Lower.emitDef (.slotAddr variableId) le ls).2 = (value, afterLoad) →
      ∀ tag, (Goose.Lower.recordReadValueRootRecipe value (.var variableId) le afterLoad).2.valueRootRecipes =
        afterLoad.valueRootRecipes.push (value, tag) →
      ∀ row ∈ func.roots.values.getD #[], row.1 = value →
        row.2 ⊆ chosen ∧ chosen ⊆ row.2) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerExpr (.read (.var variableId)) le ls).2 next ∧
      ((lowerExpr (.read (.var variableId)) le ls).2.cur.isSome = true →
        ReplayValue func next (lowerExpr (.read (.var variableId)) le ls).2
          (lowerExpr (.read (.var variableId)) le ls).1 sourceRoots (.data localVar.ty) ∧
        rootsAt next.vals (lowerExpr (.read (.var variableId)) le ls).1 =
          chosen) ∧
      (∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index) ∧
      ((lowerExpr (.read (.var variableId)) le ls).2.cur.isSome = true →
        ∃ placeRoots placeAfter, rpPlace env (.var variableId) before = .ok (placeRoots, placeAfter) ∧
          (lowerPlace (.var variableId) le ls).1 < (lowerExpr (.read (.var variableId)) le ls).2.vals.size ∧
          RootsRefine func (rootsAt next.vals (lowerPlace (.var variableId) le ls).1) placeRoots) ∧
      ((lowerExpr (.read (.var variableId)) le ls).2.cur.isSome = true →
        rootsAt next.vals (lowerPlace (.var variableId) le ls).1 = [.local variableId]) := by
  cases current : ls.cur with
  | none =>
    have stable := stopped_lowerExpr (.read (.var variableId))
    have generated : ReplayBuilder module results vt func target le scopeCount slots
        (lowerExpr (.read (.var variableId)) le ls).2 upper := ready.stopped stable current rfl
    have dead : (lowerExpr (.read (.var variableId)) le ls).2.cur = none :=
      (stable le ls _ _ rfl current).1
    exact ⟨upper, generated, by simp [dead], (fun _ _ => rfl), by simp [dead], by simp [dead]⟩
  | some block =>
    rw [rpExpr_read_variable] at source
    let address := Goose.Lower.emitDef (.slotAddr variableId) le ls
    obtain ⟨middle, middleReady, addressInfo, middleGrowth⟩ := ready.emitDef
      (.slotAddr variableId) [.local variableId] (by simp [Op.uses]) (by simp [Op.origin])
      slotBound (effectRefinement_empty func target) (RootsRefine.refl _ _)
    have addressCurrent : address.2.cur = some block := by
      dsimp only [address]
      rw [emitDef_run _ _ current]
      exact current
    have addressLive : address.2.cur.isSome = true := by simp [addressCurrent]
    have addressSize : address.2.vals.size = ls.vals.size + 1 := by
      dsimp only [address]
      rw [emitDef_run _ _ current]
      simp
    obtain ⟨addressBound, addressRoots, _⟩ := addressInfo addressLive
    have addressExact : rootsAt middle.vals address.1 = [.local variableId] := addressRoots
    have delta : EffectRefinement func
        (func.effectStep module vt middle {} (.def address.2.vals.size (.load address.1))) target := by
      change EffectRefinement func { reads := addTargets [] (rootsTargets (rootsAt middle.vals address.1)) } target
      rw [addressExact]
      exact effectRefinement_empty func target
    have loadIncluded : rootsOfDef results vt func middle address.2.vals.size (.load address.1) ⊆ chosen := by
      rw [rootsOfDef_load_slot addressExact, middleReady.slotsEq, addressSize]
      exact included (by simp [current])
    obtain ⟨next, nextReady, resultInfo, nextGrowth⟩ := middleReady.emitDefSeeded
      (.load address.1) sourceRoots chosen (by simpa [Op.uses] using addressBound)
      (by simp [Op.origin]) (by simp [Op.SymbolRefsValid]) delta loadIncluded (refined (by simp [current]))
    let loaded := Goose.Lower.emitDef (.load address.1) le address.2
    have loadedCurrent : loaded.2.cur = some block := by
      dsimp only [loaded]
      rw [emitDef_run _ _ addressCurrent]
      exact addressCurrent
    have loadedLive : loaded.2.cur.isSome = true := by simp [loadedCurrent]
    have recorded := nextReady.recordReadValueRootRecipeWhen loaded.1 (.var variableId)
      (fun tag written row member same => by
        rw [(resultInfo loadedLive).2.1]
        exact rows loaded.1 loaded.2 rfl tag written row member same)
    have frame := recordReadValueRootRecipe_frame loaded.1 (.var variableId) le loaded.2
    have recordedCur : (Goose.Lower.recordReadValueRootRecipe loaded.1 (.var variableId) le loaded.2).2.cur = loaded.2.cur :=
      by
        have result := congrArg LS.cur frame
        exact result
    have recordedVals : (Goose.Lower.recordReadValueRootRecipe loaded.1 (.var variableId) le loaded.2).2.vals = loaded.2.vals :=
      by
        have result := congrArg LS.vals frame
        exact result
    have whole : lowerExpr (.read (.var variableId)) le ls =
        (loaded.1, (Goose.Lower.recordReadValueRootRecipe loaded.1 (.var variableId) le loaded.2).2) := by
      simp only [lowerExpr, lowerPlace, bind_run, pure_run]
      rfl
    rw [whole]
    refine ⟨next, recorded, ?_, ?_, ?_, ?_⟩
    · intro live
      have loadedLive : loaded.2.cur.isSome = true := by simpa only [recordedCur] using live
      obtain ⟨bound, exactRoots, resultRefined⟩ := resultInfo loadedLive
      exact ⟨⟨by simpa only [recordedVals] using bound, resultRefined,
        fun nonref => exactRoots.trans (scalar (by simp [current]) nonref)⟩, exactRoots⟩
    · intro index bound
      have middleSize : upper.vals.size ≤ middle.vals.size := by
        calc
          upper.vals.size = ls.vals.size := ready.roots.valueSize
          _ ≤ address.2.vals.size := by rw [addressSize]; omega
          _ = middle.vals.size := middleReady.roots.valueSize.symm
      exact (nextGrowth index (Nat.lt_of_lt_of_le bound middleSize)).trans (middleGrowth index bound)
    · intro _
      refine ⟨[.local variableId], before, rfl, ?_, ?_⟩
      · rw [recordedVals]
        change address.1 < (Goose.Lower.emitDef (.load address.1) le address.2).2.vals.size
        rw [emitDef_run _ _ addressCurrent]
        simpa only [Array.size_push] using Nat.lt_succ_of_lt addressBound
      · have retainedAddress := nextGrowth address.1 (by rw [middleReady.roots.valueSize]; exact addressBound)
        change RootsRefine func (rootsAt next.vals address.1) [.local variableId]
        rw [retainedAddress, addressExact]
        exact RootsRefine.refl _ _

    · intro _
      have retainedAddress := nextGrowth address.1 (by rw [middleReady.roots.valueSize]; exact addressBound)
      change rootsAt next.vals address.1 = [.local variableId]
      exact retainedAddress.trans addressExact

#print axioms localReadWithOrigins

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
