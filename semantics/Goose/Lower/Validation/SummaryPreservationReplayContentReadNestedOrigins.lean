import Goose.Lower.Validation.SummaryPreservationReplayAcceptedReadOrigins
import Goose.Lower.Validation.SummaryPreservationContentSource
import Goose.Lower.Validation.SummaryPreservationContentReads
import Goose.Lower.Validation.SummaryPreservationReadSource

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

theorem contentRead_observed {env : PEnv} {variableId : VarId}
    {before after : RState} {roots : List RootRef}
    (reference : env.isRefSliceVar variableId = true)
    (source : rpExpr env (.read (.deref (.read (.var variableId)))) before = .ok (roots, after)) :
    ∃ contents, env.cont variableId = some contents := by
  simp only [rpExpr] at source
  obtain ⟨placeRoots, placeState, _, tail⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, readState, _, reading⟩ := (st_bind_ok _ _ _ _).mp tail
  cases found : env.cont variableId with
  | none =>
    simp only [readRoots, reference, ite_true, found, rejP] at reading
    change Except.error _ = Except.ok _ at reading
    cases reading
  | some contents => exact ⟨contents, rfl⟩

theorem contentReadWithNestedOrigins {env : PEnv} {context : ContextId} {index : Nat} {param : Param} {localVar : LocalVar}
    {before after : RState} {sourceRoots : List RootRef} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {target : Core.Eff} {siteRoot : DemandNode} {scopeCount : Nat} {ls : LS} {upper : Prov}
    {mutability : Mutability} {element : Ty}
    (accepted : Core.validate env.mod = .ok ())
    (contextRow : env.mod.contexts[context]? = some env.ctx)
    (implementationRow : env.mod.impls[env.ctx.impl]? = some env.impl)
    (parameter : env.impl.params[index]? = some param)
    (variableRow : env.impl.vars[param.var]? = some localVar)
    (reference : localVar.ty.isRefSlice = true)
    (ready : ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
      (typedContextSlotUpper env.mod env.ctx env.impl) ls upper)
    (source : rpExpr env (.read (.deref (.read (.var param.var)))) before = .ok (sourceRoots, after))
    (wholeEffect : EffectRefinement (lowerContextAt env.mod env.ctx env.impl) after.eff target)
    (addressType : ls.cur.isSome = true → vt[(lowerExpr (.read (.var param.var))
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).1]? = some (some (.data localVar.ty)))
    (sliceType : ls.cur.isSome = true → vt[(lowerExpr (.read (.var param.var))
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2.vals.size]? =
        some (some (.data (.slice mutability element))))
    (metadata : SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot
      (lowerContextAt env.mod env.ctx env.impl)
      (lowerExpr (.read (.deref (.read (.var param.var))))
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2) :
    ∃ next, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
        (typedContextSlotUpper env.mod env.ctx env.impl)
        (lowerExpr (.read (.deref (.read (.var param.var))))
          (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2 next ∧
      ((lowerExpr (.read (.deref (.read (.var param.var))))
          (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2.cur.isSome = true →
        ReplayValue (lowerContextAt env.mod env.ctx env.impl) next
          (lowerExpr (.read (.deref (.read (.var param.var))))
            (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2
          (lowerExpr (.read (.deref (.read (.var param.var))))
            (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).1
          sourceRoots (.data (.slice mutability element))) ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      ((lowerExpr (.read (.deref (.read (.var param.var))))
          (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2.cur.isSome = true →
        ∃ placeRoots placeAfter, rpPlace env (.deref (.read (.var param.var))) before = .ok (placeRoots, placeAfter) ∧
          (lowerPlace (.deref (.read (.var param.var))) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).1 <
            (lowerExpr (.read (.deref (.read (.var param.var))))
              (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2.vals.size ∧
          RootsRefine (lowerContextAt env.mod env.ctx env.impl)
            (rootsAt next.vals (lowerPlace (.deref (.read (.var param.var)))
              (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).1) placeRoots) ∧
      ((lowerExpr (.read (.deref (.read (.var param.var))))
          (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2.cur.isSome = true →
        ∃ innerPlaceRoots innerPlaceAfter innerAfter,
          rpPlace env (.var param.var) before = .ok (innerPlaceRoots, innerPlaceAfter) ∧
          rpExpr env (.read (.var param.var)) before = .ok ([.param index], innerAfter) ∧
          (lowerPlace (.var param.var) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).1 <
            (lowerExpr (.read (.deref (.read (.var param.var))))
              (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2.vals.size ∧
          RootsRefine (lowerContextAt env.mod env.ctx env.impl)
            (rootsAt next.vals (lowerPlace (.var param.var)
              (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).1) innerPlaceRoots ∧
          RootsRefine (lowerContextAt env.mod env.ctx env.impl)
            (rootsAt next.vals (lowerExpr (.read (.var param.var))
              (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).1) [.param index]) ∧
      ((lowerExpr (.read (.deref (.read (.var param.var))))
          (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2.cur.isSome = true →
        env.isRefSliceVar param.var = true ∧
        rootsAt next.vals (lowerPlace (.deref (.read (.var param.var)))
          (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).1 = [.param param.var] ∧
        rootsAt next.vals (lowerPlace (.var param.var)
          (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).1 = [.local param.var]) := by
  let le := lowerEnv env.mod env.impl.vars env.impl.results.toList
  let func := lowerContextAt env.mod env.ctx env.impl
  let loaded := lowerExpr (.read (.var param.var)) le ls
  cases current : ls.cur with
  | none =>
    have stable := stopped_lowerExpr (.read (.deref (.read (.var param.var))))
    have generated : ReplayBuilder (lower env.mod) results vt func target le scopeCount
        (typedContextSlotUpper env.mod env.ctx env.impl)
        (lowerExpr (.read (.deref (.read (.var param.var)))) le ls).2 upper := ready.stopped stable current rfl
    have dead : (lowerExpr (.read (.deref (.read (.var param.var))))
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2.cur = none :=
      (stable le ls _ _ rfl current).1
    exact ⟨upper, generated, by simp only [dead, Option.isSome_none, Bool.false_eq_true, false_implies], (fun _ _ => rfl), (by simp [dead]), (by simp [dead]), by simp [dead]⟩
  | some block =>
    have live : ls.cur.isSome = true := by simp [current]
    have refLike : localVar.ty.isRefLike = true := by
      cases type : localVar.ty <;> simp_all [Ty.isRefLike, Ty.isRefSlice]
    obtain ⟨readAfter, placeReplay⟩ := rpExpr_content_place_contract accepted contextRow implementationRow
      parameter variableRow reference source
    have observed : (env.cont param.var).isSome = true := by
      obtain ⟨contents, found⟩ := contentRead_observed
        (by simp [PEnv.isRefSliceVar, variableRow, reference]) source
      simp [found]
    have innerMetadata : SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot func loaded.2 := by
      apply metadata.restrict
      have advancement := advB_emitDef (.load loaded.1) le loaded.2 _ _
        (rfl : Goose.Lower.emitDef (.load loaded.1) le loaded.2 =
          lowerExpr (.read (.deref (.read (.var param.var)))) le ls)
      obtain ⟨suffix, same⟩ := advancement.recipePrefix
      intro recipe member
      apply Array.mem_toList_iff.mp
      change recipe ∈ (Goose.Lower.emitDef (.load loaded.1) le loaded.2).2.valueRootRecipes.toList
      exact same.symm ▸ List.mem_append_left _ (Array.mem_toList_iff.mpr member)
    obtain ⟨middle, middleReady, loadedInfo, middleGrowth, innerOrigins, innerPhysical⟩ := ready.acceptedLocalReadWithOrigins
      accepted contextRow implementationRow variableRow placeReplay
      (by intro _ nonref; rw [refLike] at nonref; cases nonref) innerMetadata
    let slot := lowerPlace (.var param.var) le ls
    have slotCurrent : slot.2.cur = some block := by
      dsimp [slot, lowerPlace]
      rw [emitDef_run _ _ current]
      exact current
    have loadedCurrent : loaded.2.cur = some block := by
      rw [ReplayBuilder.readCurrent_eq]
      change (Goose.Lower.emitDef (.load slot.1) le slot.2).2.cur = some block
      rw [emitDef_run _ _ slotCurrent]
      exact slotCurrent
    have loadedLive : loaded.2.cur.isSome = true := by simp [loadedCurrent]
    obtain ⟨loadedValue, raw⟩ := loadedInfo loadedLive
    have recognized : valRefLike vt loaded.1 = true := by
      have tag : vt[loaded.1]? = some (some (.data localVar.ty)) := addressType live
      simp only [valRefLike, tag, VTy.refLike, refLike]
    have identity := ((validate_modOk env.mod accepted).impl env.ctx.impl env.impl implementationRow).params
      index param parameter |>.1
    have rawRoots : rootsAt middle.vals loaded.1 = [.param index] := by
      change rootsAt middle.vals loaded.1 = (if localVar.ty.isRefSlice then
        lowerValueRootCeiling env #[] (.refSliceVar param.var) else
        if valRefLike vt (ls.vals.size + 1) then
          rootsAt (typedContextSlotUpper env.mod env.ctx env.impl) param.var else []) at raw
      rw [if_pos reference, refSliceReadRootCeiling_observed accepted contextRow implementationRow
        variableRow reference observed] at raw
      simpa only [identity] using raw
    have rawPlace : rpPlace env (.deref (.read (.var param.var))) before =
        .ok ([.param index], readAfter) := placeReplay
    have sourceContract := rpExpr_read_contract rawPlace source
    have computed := readRoots_refSlice_parameter_refines (res := results) (vt := vt) (provenance := middle)
      (result := loaded.2.vals.size) parameter variableRow reference sourceContract.1 rawRoots (sliceType live)
    have nodeEffect : EffectRefinement func
        { readAfter.eff with reads := addTargets readAfter.eff.reads (rootsTargets [.param index]) } target := by
      simpa only [sourceContract.2] using wholeEffect
    have delta : EffectRefinement func (func.effectStep (lower env.mod) vt middle {}
        (.def loaded.2.vals.size (.load loaded.1))) target := by
      apply (effectStep_load_refines (lowerContextAt_parameterRoots_closed accepted contextRow implementationRow)
        (effectRefinement_empty func readAfter.eff) ?_).trans nodeEffect
      rw [rawRoots]
      exact RootsRefine.refl _ _
    obtain ⟨next, nextReady, nextValue, nextGrowth⟩ := middleReady.emitTypedDef (.load loaded.1) sourceRoots
      (.data (.slice mutability element)) (by simpa [Op.uses] using loadedValue.bound)
      (by simp [Op.origin]) (by simp [Op.SymbolRefsValid]) delta computed (by simp [VTy.refLike, Ty.isRefLike])
    have whole : lowerExpr (.read (.deref (.read (.var param.var)))) le ls =
        Goose.Lower.emitDef (.load loaded.1) le loaded.2 := by
      simp only [lowerExpr, lowerPlace, bind_run]
      rfl
    rw [whole]
    refine ⟨next, nextReady, nextValue, ?_, ?_, ?_, ?_⟩
    · intro old bound
      have growth : upper.vals.size ≤ middle.vals.size := by
        rw [ready.roots.valueSize, middleReady.roots.valueSize]
        exact (advB_lowerExpr (.read (.var param.var)) le ls loaded.1 loaded.2 rfl).vals
      exact (nextGrowth old (Nat.lt_of_lt_of_le bound growth)).trans (middleGrowth old bound)
    · intro _
      refine ⟨[.param index], readAfter, rawPlace, ?_, ?_⟩
      · change loaded.1 < (Goose.Lower.emitDef (.load loaded.1) le loaded.2).2.vals.size
        rw [emitDef_run _ _ loadedCurrent]
        simpa only [Array.size_push] using Nat.lt_succ_of_lt loadedValue.bound
      · have retainedAddress := nextGrowth loaded.1 (by rw [middleReady.roots.valueSize]; exact loadedValue.bound)
        change RootsRefine func (rootsAt next.vals loaded.1) [.param index]
        rw [retainedAddress, rawRoots]
        exact RootsRefine.refl _ _
    · intro _
      obtain ⟨innerPlaceRoots, innerPlaceAfter, innerPlaceReplay, innerAddressBound, innerAddressRefined⟩ :=
        innerOrigins loadedLive
      refine ⟨innerPlaceRoots, innerPlaceAfter, readAfter, innerPlaceReplay, placeReplay, ?_, ?_, ?_⟩
      · change slot.1 < (Goose.Lower.emitDef (.load loaded.1) le loaded.2).2.vals.size
        rw [emitDef_run _ _ loadedCurrent]
        simpa only [Array.size_push] using Nat.lt_succ_of_lt innerAddressBound
      · have retainedAddress := nextGrowth slot.1 (by rw [middleReady.roots.valueSize]; exact innerAddressBound)
        change RootsRefine func (rootsAt next.vals slot.1) innerPlaceRoots
        rw [retainedAddress]
        exact innerAddressRefined
      · have retainedValue := nextGrowth loaded.1 (by rw [middleReady.roots.valueSize]; exact loadedValue.bound)
        rw [retainedValue]
        exact loadedValue.refined

    · intro _
      refine ⟨by simp only [PEnv.isRefSliceVar, variableRow, reference], ?_, ?_⟩
      · have retainedAddress := nextGrowth loaded.1 (by rw [middleReady.roots.valueSize]; exact loadedValue.bound)
        change rootsAt next.vals loaded.1 = [.param param.var]
        rw [retainedAddress, rawRoots, identity]
      · have retainedAddress := nextGrowth slot.1 (by rw [middleReady.roots.valueSize]; exact (innerOrigins loadedLive).choose_spec.choose_spec.2.1)
        change rootsAt next.vals slot.1 = [.local param.var]
        exact retainedAddress.trans (innerPhysical loadedLive)

#print axioms contentReadWithNestedOrigins

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
