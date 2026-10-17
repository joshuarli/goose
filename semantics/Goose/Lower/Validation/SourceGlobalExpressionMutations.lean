import Goose.Lower.Validation.SourceGlobalReplayContracts
import Goose.Lower.Validation.SummaryPreservationReplayMutationsGrowth
import Goose.Lower.Validation.SummaryPreservationReplayMutationsOwners
import Goose.Lower.Validation.SourceSymbolRefs
import Goose.Core.Sound.AccessTyping

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

private theorem global_read_shrink_aborts_extension (func : Func) (source : Core.Eff) (roots : List RootRef) :
    EffectRefinement func source {source with
      reads := addTargets source.reads (rootsTargets roots)
      shrinks := addTargets source.shrinks (rootsTargets roots), aborts := true} := by
  refine ⟨?_, fun _ h => h, fun _ h => h, ?_, fun _ h => h, fun _ => rfl, fun h => h, fun h => h⟩
  all_goals exact storageTargets_mono (fun target member => addTargets_left _ _ target member)

private theorem growth_extension (func : Func) (source : Core.Eff) (owners reads : List RootRef)
    (profile : ArtifactProfile) (limited : Bool) :
    EffectRefinement func source (if profile == .shrink then {source with
      reads := addTargets source.reads (rootsTargets reads)
      grows := addTargets source.grows (rootsTargets owners)
      writes := addTargets source.writes (rootsTargets owners)
      aborts := source.aborts || limited} else {source with
      reads := addTargets source.reads (rootsTargets reads)
      grows := addTargets source.grows (rootsTargets owners)}) := by
  cases profile
  · refine ⟨?_, fun _ h => h, ?_, fun _ h => h, fun _ h => h, fun h => h, fun h => h, fun h => h⟩
    all_goals exact storageTargets_mono (fun target member => addTargets_left _ _ target member)
  · refine ⟨?_, ?_, ?_, fun _ h => h, fun _ h => h, ?_, fun h => h, fun h => h⟩
    · exact storageTargets_mono (fun target member => addTargets_left _ _ target member)
    · exact storageTargets_mono (fun target member => addTargets_left _ _ target member)
    · exact storageTargets_mono (fun target member => addTargets_left _ _ target member)
    · intro h
      simp [h]

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)} {target : Core.Eff} {scopeCount : Nat} {initial : LS} {upper : Prov}

theorem globalExpressionReplay_push {owner : Place} {expression : Expr} (origin : Option OriginId)
    (tables : SourceRootTables typingEnv env) (closed : ParameterRootsClosed func)
    (ownerChild : GlobalPlaceReplayAt typingEnv env results vt func returnTypes slots target scopeCount owner initial upper)
    (valueChild : ∀ provenance, GlobalExpressionReplayAt typingEnv env results vt func returnTypes slots target scopeCount expression
      (lowerPlace owner (lowerEnv env.mod env.impl.vars returnTypes) initial).2 provenance) :
    GlobalExpressionReplayAt typingEnv env results vt func returnTypes slots target scopeCount (.push owner expression origin) initial upper := by
  intro type start finish before after roots typed replay ceiling ready generated native
  obtain ⟨info, element, ownerStart, ownerFinish, childStart, childFinish, ownerTyped, _elementType, valueTyped, typeEq⟩ :=
    tyExpr_push_children typed
  subst type
  obtain ⟨ownerRoots, ownerState, ownerReplay, tail⟩ := (st_bind_ok _ _ _ _).mp replay
  obtain ⟨valueRoots, valueState, valueReplay, _tail⟩ := (st_bind_ok _ _ _ _).mp tail
  have sourceType := tyPlace_accessType tables.moduleEq.symm tables.variablesEq.symm ownerTyped
  obtain ⟨limited, limitedRun⟩ : ∃ limited, env.limitedOwner owner = .ok limited := by
    cases shape : info.ty <;> simp only [PEnv.limitedOwner, sourceType, shape] <;> first | exact ⟨false, rfl⟩ | exact ⟨true, rfl⟩
  have sourceReplay := replay
  rw [rpExpr_push_after_operands ownerReplay valueReplay limitedRun] at sourceReplay
  have sourceEffect := congrArg (fun result => result.2.eff) (Except.ok.inj sourceReplay).symm
  have valueCeiling : EffectRefinement func valueState.eff target := by
    apply (growth_extension _ _ ownerRoots [] env.mod.profile limited).trans
    cases profile : env.mod.profile <;>
      simp [profile] at sourceEffect ⊢ <;> rw [sourceEffect] at ceiling <;>
      simpa [rootsTargets, addTargets] using ceiling
  have ownerCeiling := effectRefinement_before_expression valueReplay valueCeiling
  let le := lowerEnv env.mod env.impl.vars returnTypes
  let address := lowerPlace owner le initial
  let value := lowerExpr expression le address.2
  have valueNative : NativeRows vt value.2 := native.of_prefix (types_emitDef (.push address.1 value.1 origin) le value.2 _ _ rfl)
  have ownerNative := valueNative.of_prefix (types_lowerExpr expression le address.2 _ _ rfl)
  obtain ⟨middle, ownerReady, ownerValue, ownerPrefix⟩ :=
    ownerChild info ownerStart ownerFinish before ownerState ownerRoots ownerTyped ownerReplay ownerCeiling ready generated ownerNative
  obtain ⟨valueUpper, valueReady, valueFacts, valuePrefix⟩ :=
    valueChild middle element childStart childFinish ownerState valueState valueRoots valueTyped valueReplay valueCeiling
      ownerReady (generated.lowerPlace owner rfl) valueNative
  obtain ⟨mutability, actualType⟩ : ∃ mutability, value.2.cur.isSome = true →
      vt[address.1]? = some (some (.data (.ref mutability info.ty))) := by
    by_cases live : value.2.cur.isSome = true
    · obtain ⟨mutability, row⟩ := ownerNative.place (value := address.1) (results := returnTypes) generated ownerTyped
        (by rw [← tables.moduleEq, ← tables.variablesEq]) ((dead_lowerExpr expression).live_before rfl live)
      exact ⟨mutability, fun _ => row⟩
    · exact ⟨.readOnly, fun active => (live active).elim⟩
  obtain ⟨next, completed, returned, retained⟩ := valueReady.push (element := element)
    ownerReplay valueReplay replay ceiling rfl rfl
    closed rfl
    (by intro candidate selected; subst origin; simpa only [le, lowerEnv, tables.moduleEq] using Core.tyExpr_push_success_origin_bound typed)
    sourceType actualType (by
      intro live
      have ownerLive := (dead_lowerExpr expression).live_before rfl live
      have oldBound := (ownerValue ownerLive).1
      refine ⟨Nat.lt_of_lt_of_le oldBound (advB_lowerExpr expression le address.2 _ _ rfl).vals,
        (valueFacts live).bound, ?_⟩
      rw [valuePrefix address.1 (by rw [ownerReady.roots.valueSize]; exact oldBound)]
      exact (ownerValue ownerLive).2)
  refine ⟨next, completed, returned, ?_⟩
  intro old bound
  have ownerGrowth : upper.vals.size ≤ middle.vals.size := by
    rw [ready.roots.valueSize, ownerReady.roots.valueSize]
    exact (advB_lowerPlace owner le initial _ _ rfl).vals
  have valueGrowth : middle.vals.size ≤ valueUpper.vals.size := by
    rw [ownerReady.roots.valueSize, valueReady.roots.valueSize]
    exact (advB_lowerExpr expression le address.2 _ _ rfl).vals
  exact (retained old (Nat.lt_of_lt_of_le bound (Nat.le_trans ownerGrowth valueGrowth))).trans
    ((valuePrefix old (Nat.lt_of_lt_of_le bound ownerGrowth)).trans (ownerPrefix old bound))

theorem globalExpressionReplay_pop {owner : Place} (origin : OriginId)
    (tables : SourceRootTables typingEnv env) (closed : ParameterRootsClosed func)
    (child : GlobalPlaceReplayAt typingEnv env results vt func returnTypes slots target scopeCount owner initial upper) :
    GlobalExpressionReplayAt typingEnv env results vt func returnTypes slots target scopeCount (.pop owner origin) initial upper := by
  intro type start finish before after roots typed replay ceiling ready generated native
  obtain ⟨info, ownerStart, ownerFinish, ownerTyped, _elementType⟩ := tyExpr_pop_owner typed
  obtain ⟨ownerRoots, ownerState, ownerReplay, _tail⟩ := (st_bind_ok _ _ _ _).mp replay
  have sourceReplay := replay
  rw [rpExpr_pop_after_owner ownerReplay] at sourceReplay
  have afterEffect : after.eff = {ownerState.eff with
      reads := addTargets ownerState.eff.reads (rootsTargets ownerRoots)
      shrinks := addTargets ownerState.eff.shrinks (rootsTargets ownerRoots)
      aborts := true} := congrArg (fun result => result.2.eff) (Except.ok.inj sourceReplay).symm
  have ownerCeiling : EffectRefinement func ownerState.eff target := by
    apply (global_read_shrink_aborts_extension _ _ ownerRoots).trans
    simpa only [afterEffect] using ceiling
  let le := lowerEnv env.mod env.impl.vars returnTypes
  let operand := lowerPlace owner le initial
  have ownerNative : NativeRows vt operand.2 := native.of_prefix (types_emitDef (.pop operand.1 (some origin)) le operand.2 _ _ rfl)
  obtain ⟨middle, ownerReady, ownerValue, ownerPrefix⟩ :=
    child info ownerStart ownerFinish before ownerState ownerRoots ownerTyped ownerReplay ownerCeiling ready generated ownerNative
  obtain ⟨next, completed, returned, retained⟩ := ownerReady.pop (type := type) ownerReplay replay ceiling rfl
    closed
    (by simpa only [le, lowerEnv, tables.moduleEq] using Core.tyExpr_pop_success_origin_bound typed) ownerValue
  refine ⟨next, completed, returned, ?_⟩
  intro old bound
  have growth : upper.vals.size ≤ middle.vals.size := by
    rw [ready.roots.valueSize, ownerReady.roots.valueSize]
    exact (advB_lowerPlace owner le initial _ _ rfl).vals
  exact (retained old (Nat.lt_of_lt_of_le bound growth)).trans (ownerPrefix old bound)

#print axioms globalExpressionReplay_push
#print axioms globalExpressionReplay_pop

end Goose.Lower.Validation.SummaryPreservation
