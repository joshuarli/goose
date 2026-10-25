import Goose.Lower.Validation.SummaryPreservationAssignSource
import Goose.Lower.Validation.SummaryPreservationReplayMutationsEmit

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem effectStep_store_nonref_refines_closed {module : GIR.Module} {func : Func} {vt : Array (Option VTy)} {provenance : Prov}
    {address value : ValueId} {origin : OriginId} {sourceRoots : List RootRef} {source : Core.Eff}
    (closed : ParameterRootsClosed func)
    (roots : RootsRefine func
      (rootsAt provenance.vals address) sourceRoots)
    (owner : (ownerTy vt address).any Ty.isRefLike = false) :
    EffectRefinement func
      (func.effectStep module vt provenance {}
        (.eff (.store address value origin)))
      { source with writes := addTargets source.writes (rootsTargets sourceRoots) } := by
  have noRebind := effectStep_store_nonref_no_rebinds (module := module)
    (func := func) (provenance := provenance) (value := value) (origin := origin) owner
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Func.effectStep, Func.storageTargets]
  · intro target member
    change target ∈ func.storageTargets
      (addTargets [] (rootsTargets (rootsAt provenance.vals address))) at member
    rcases storageTargets_addTargets_origin member with empty | actual
    · simp [Func.storageTargets] at empty
    · exact storageTargets_mono (fun t h => addTargets_right _ _ t h) target
        (roots.targets closed target actual)
  · simp [Func.effectStep, Func.storageTargets]
  · simp [Func.effectStep, Func.storageTargets]
  · intro target member
    rw [noRebind] at member
    cases member
  · simp [Func.effectStep]
  · simp [Func.effectStep]
  · simp [Func.effectStep]


theorem effectStep_store_parameter_refines {module : GIR.Module} {func : Func}
    {vt : Array (Option VTy)} {provenance : Prov} {address value : ValueId}
    {origin : OriginId} {sourceRoots : List RootRef} {source : Core.Eff} {parameter : VarId}
    (closed : ParameterRootsClosed func)
    (roots : RootsRefine func (rootsAt provenance.vals address) sourceRoots)
    (identity : ∀ root ∈ rootsAt provenance.vals address, root ∈ [RootRef.param parameter]) :
    EffectRefinement func (func.effectStep module vt provenance {} (.eff (.store address value origin)))
      { source with
        writes := addTargets source.writes (rootsTargets sourceRoots)
        rebinds := addTargets source.rebinds [.param parameter] } := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Func.effectStep, Func.storageTargets]
  · intro target member
    change target ∈ func.storageTargets (addTargets [] (rootsTargets (rootsAt provenance.vals address))) at member
    rcases storageTargets_addTargets_origin member with empty | actual
    · simp [Func.storageTargets] at empty
    · exact storageTargets_mono (fun t h => addTargets_right _ _ t h) target
        (roots.targets closed target actual)
  · simp [Func.effectStep, Func.storageTargets]
  · simp [Func.effectStep, Func.storageTargets]
  · intro target member
    simp only [Func.effectStep] at member
    rcases mem_addTargets_iff.mp member with empty | actual
    · cases empty
    · obtain ⟨root, rootMember, mapped⟩ := List.mem_filterMap.mp actual
      have same : root = .param parameter := List.mem_singleton.mp (identity root rootMember)
      subst root
      cases row : func.params[parameter]? with
      | none => simp [row] at mapped
      | some type =>
        simp only [row] at mapped
        split at mapped
        · cases mapped
          exact addTargets_right _ _ _ (by simp)
        · cases mapped
  · simp [Func.effectStep]
  · simp [Func.effectStep]
  · simp [Func.effectStep]

namespace ReplayBuilder

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem assignNonref {env : PEnv} {place : Place} {expression : Expr} {origin : OriginId}
    {initialSource placeState before after : RState} {placeRoots valueRoots : List RootRef}
    {initial placeLS : LS} {address value : ValueId} (loop : Option LoopCtx)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (placeReplay : rpPlace env place initialSource = .ok (placeRoots, placeState))
    (valueReplay : rpExpr env expression placeState = .ok (valueRoots, before))
    (source : rpStmt env (.assign place expression origin) initialSource = .ok ((), after))
    (wholeEffect : EffectRefinement func after.eff target)
    (placeRun : lowerPlace place le initial = (address, placeLS))
    (valueRun : lowerExpr expression le placeLS = (value, ls))
    (closed : ParameterRootsClosed func) (originBound : origin < le.mod.origins.size)
    (input : ls.cur.isSome = true → address < ls.vals.size ∧ value < ls.vals.size ∧
      RootsRefine func (rootsAt upper.vals address) placeRoots ∧
      (ownerTy vt address).any Ty.isRefLike = false ∧ rootsAt upper.vals value = []) :
    ReplayBuilder module results vt func target le scopeCount slots
      (lowerStmt loop (.assign place expression origin) le initial).2 upper := by
  have sourceEffect := (rpStmt_assign_contract placeReplay valueReplay source).2
  have whole : lowerStmt loop (.assign place expression origin) le initial =
      Goose.Lower.emitEffect (.store address value (some origin)) le ls := by
    simp only [lowerStmt, bind_run, placeRun, valueRun]
  rw [whole]
  apply ready.emitEffect_live (.store address value (some origin))
  · intro live
    apply Inst.SymbolsWithin.eff
    · simpa [Effect.uses] using And.intro (input live).1 (input live).2.1
    · simpa [Effect.origin] using originBound
    · trivial
  · intro live slot slotMember root member
    rw [(input live).2.2.2.2] at member
    cases member
  · intro live
    have delta := effectStep_store_nonref_refines_closed (module := module) (vt := vt)
      (value := value) (origin := origin) (source := before.eff) closed
      (input live).2.2.1 (input live).2.2.2.1
    apply EffectRefinement.trans delta
    apply EffectRefinement.trans _ wholeEffect
    rw [sourceEffect]
    exact ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h,
      fun t h => addTargets_left _ _ t h, fun h => h, fun h => h, fun h => h⟩

theorem assignRefSlice {env : PEnv} {place : Place} {expression : Expr} {origin : OriginId}
    {initialSource placeState before after : RState} {placeRoots valueRoots : List RootRef}
    {initial placeLS : LS} {address value : ValueId} {parameter : VarId} (loop : Option LoopCtx)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (placeReplay : rpPlace env place initialSource = .ok (placeRoots, placeState))
    (valueReplay : rpExpr env expression placeState = .ok (valueRoots, before))
    (source : rpStmt env (.assign place expression origin) initialSource = .ok ((), after))
    (wholeEffect : EffectRefinement func after.eff target)
    (placeRun : lowerPlace place le initial = (address, placeLS))
    (valueRun : lowerExpr expression le placeLS = (value, ls))
    (closed : ParameterRootsClosed func) (originBound : origin < le.mod.origins.size)
    (deref : place.derefVar? = some parameter) (isReferenceSlice : env.isRefSliceVar parameter = true)
    (parameterBound : parameter < env.impl.params.size)
    (input : ls.cur.isSome = true → address < ls.vals.size ∧ value < ls.vals.size ∧
      RootsRefine func (rootsAt upper.vals address) placeRoots ∧
      ∀ root ∈ rootsAt upper.vals address, root ∈ [RootRef.param parameter]) :
    ReplayBuilder module results vt func target le scopeCount slots
      (lowerStmt loop (.assign place expression origin) le initial).2 upper := by
  have sourceEffect := (rpStmt_assign_contract placeReplay valueReplay source).2
  have rebinds : storeRebinds env place = [.param parameter] := by
    simp [storeRebinds, deref, isReferenceSlice, parameterBound]
  have whole : lowerStmt loop (.assign place expression origin) le initial =
      Goose.Lower.emitEffect (.store address value (some origin)) le ls := by
    simp only [lowerStmt, bind_run, placeRun, valueRun]
  rw [whole]
  apply ready.emitEffect_live (.store address value (some origin))
  · intro live
    apply Inst.SymbolsWithin.eff
    · simpa [Effect.uses] using And.intro (input live).1 (input live).2.1
    · simpa [Effect.origin] using originBound
    · trivial
  · intro live slot slotMember root member
    have impossible := (input live).2.2.2 (.local slot) slotMember
    simp at impossible
  · intro live
    have delta := effectStep_store_parameter_refines (module := module) (vt := vt)
      (value := value) (origin := origin) (source := before.eff) closed
      (input live).2.2.1 (input live).2.2.2
    rw [sourceEffect, rebinds] at wholeEffect
    exact delta.trans wholeEffect

end ReplayBuilder
end Goose.Lower.Validation.SummaryPreservation
