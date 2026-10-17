import Goose.Lower.Validation.SummaryPreservationReplayLiveEmit
import Goose.Lower.Validation.SummaryPreservationRefinedReads

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem localRead {env : PEnv} {variableId : VarId} {localVar : LocalVar}
    {before after : RState} {sourceRoots : List RootRef}
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (checked : checkAnnotationShape env.mod env.impl env.ctx = .ok ())
    (variableRow : env.impl.vars[variableId]? = some localVar)
    (source : rpExpr env (.read (.var variableId)) before = .ok (sourceRoots, after))
    (slotBound : variableId < le.slots.size)
    (slotRoots : RootsRefine func (rootsAt slots variableId) (env.ann variableId |>.getD []))
    (scalarType : ls.cur.isSome = true → localVar.ty.isRefLike = false →
      valRefLike vt (ls.vals.size + 1) = false) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerExpr (.read (.var variableId)) le ls).2 next ∧
      ((lowerExpr (.read (.var variableId)) le ls).2.cur.isSome = true →
        ReplayValue func next (lowerExpr (.read (.var variableId)) le ls).2
          (lowerExpr (.read (.var variableId)) le ls).1 sourceRoots (.data localVar.ty) ∧
        rootsAt next.vals (lowerExpr (.read (.var variableId)) le ls).1 =
          if valRefLike vt (lowerExpr (.read (.var variableId)) le ls).1 then rootsAt slots variableId else []) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  cases current : ls.cur with
  | none =>
    have stable := stopped_lowerExpr (.read (.var variableId))
    have generated : ReplayBuilder module results vt func target le scopeCount slots
        (lowerExpr (.read (.var variableId)) le ls).2 upper := ready.stopped stable current rfl
    have dead : (lowerExpr (.read (.var variableId)) le ls).2.cur = none :=
      (stable le ls _ _ rfl current).1
    exact ⟨upper, generated, by simp [dead], fun _ _ => rfl⟩
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
    have middleSlots : RootsRefine func (rootsAt middle.slots variableId) (env.ann variableId |>.getD []) := by
      rw [middleReady.slotsEq]
      exact slotRoots
    have loaded : RootsRefine func
        (rootsOfDef results vt func middle address.2.vals.size (.load address.1)) sourceRoots :=
      readRoots_variable_load_refines checked variableRow source addressExact middleSlots
    have delta : EffectRefinement func
        (func.effectStep module vt middle {} (.def address.2.vals.size (.load address.1))) target := by
      change EffectRefinement func { reads := addTargets [] (rootsTargets (rootsAt middle.vals address.1)) } target
      rw [addressExact]
      exact effectRefinement_empty func target
    obtain ⟨next, nextReady, resultInfo, nextGrowth⟩ := middleReady.emitDef (.load address.1) sourceRoots
      (by simpa [Op.uses] using addressBound) (by simp [Op.origin]) (by simp [Op.SymbolRefsValid]) delta loaded
    have whole : lowerExpr (.read (.var variableId)) le ls = Goose.Lower.emitDef (.load address.1) le address.2 := by
      simp only [lowerExpr, lowerPlace, bind_run]
      rfl
    rw [whole]
    refine ⟨next, nextReady, ?_, ?_⟩
    · intro live
      obtain ⟨bound, exactRoots, refined⟩ := resultInfo live
      refine ⟨⟨bound, refined, ?_⟩, ?_⟩
      · intro nonref
        rw [exactRoots, rootsOfDef_load_slot addressExact]
        have scalar : valRefLike vt address.2.vals.size = false := by
          have tag := scalarType (by simp [current]) nonref
          rw [addressSize]
          exact tag
        change (if valRefLike vt address.2.vals.size then rootsAt middle.slots variableId else []) = []
        simp only [scalar, Bool.false_eq_true, ite_false]
      · have returnedValue : (Goose.Lower.emitDef (.load address.1) le address.2).1 = address.2.vals.size := by
          rw [emitDef_run _ _ addressCurrent]
        rw [exactRoots, rootsOfDef_load_slot addressExact, middleReady.slotsEq]
        change (if valRefLike vt address.2.vals.size then rootsAt slots variableId else []) = _
        rw [returnedValue]
    · intro index bound
      have middleSize : upper.vals.size ≤ middle.vals.size := by
        calc
          upper.vals.size = ls.vals.size := ready.roots.valueSize
          _ ≤ address.2.vals.size := by rw [addressSize]; omega
          _ = middle.vals.size := middleReady.roots.valueSize.symm
      exact (nextGrowth index (Nat.lt_of_lt_of_le bound middleSize)).trans (middleGrowth index bound)

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
