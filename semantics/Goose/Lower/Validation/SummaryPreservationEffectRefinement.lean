import Goose.Lower.Validation.SummaryPreservationRootRefinement
import Goose.Lower.Validation.SummaryPreservationEffectFold

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

structure EffectRefinement (func : Func) (actual source : Core.Eff) : Prop where
  reads : ∀ target ∈ func.storageTargets actual.reads, target ∈ func.storageTargets source.reads
  writes : ∀ target ∈ func.storageTargets actual.writes, target ∈ func.storageTargets source.writes
  grows : ∀ target ∈ func.storageTargets actual.grows, target ∈ func.storageTargets source.grows
  shrinks : ∀ target ∈ func.storageTargets actual.shrinks, target ∈ func.storageTargets source.shrinks
  rebinds : ∀ target ∈ actual.rebinds, target ∈ source.rebinds
  aborts : actual.aborts = true → source.aborts = true
  outputs : actual.outputs = true → source.outputs = true
  unknown : actual.unknown = true → source.unknown = true

theorem EffectRefinement.refl (func : Func) (effect : Core.Eff) :
    EffectRefinement func effect effect :=
  ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h,
    fun _ h => h, fun h => h, fun h => h, fun h => h⟩

theorem EffectRefinement.trans {func : Func} {actual middle source : Core.Eff}
    (left : EffectRefinement func actual middle) (right : EffectRefinement func middle source) :
    EffectRefinement func actual source :=
  ⟨fun t h => right.reads t (left.reads t h),
    fun t h => right.writes t (left.writes t h),
    fun t h => right.grows t (left.grows t h),
    fun t h => right.shrinks t (left.shrinks t h),
    fun t h => right.rebinds t (left.rebinds t h),
    fun h => right.aborts (left.aborts h), fun h => right.outputs (left.outputs h),
    fun h => right.unknown (left.unknown h)⟩

theorem EffectRefinement.source_mono {func : Func} {actual source later : Core.Eff}
    (prior : EffectRefinement func actual source) (effects : EffLe source later)
    (rebinds : RebindsLe source later) (flags : EffectFlagsLe source later) :
    EffectRefinement func actual later :=
  ⟨fun target member => storageTargets_mono effects.1 target (prior.reads target member),
    fun target member => storageTargets_mono effects.2.1 target (prior.writes target member),
    fun target member => storageTargets_mono effects.2.2.1 target (prior.grows target member),
    fun target member => storageTargets_mono effects.2.2.2.1 target (prior.shrinks target member),
    fun target member => rebinds target (prior.rebinds target member),
    fun h => flags.1 (prior.aborts h), fun h => flags.2 (prior.outputs h),
    fun h => effects.2.2.2.2 (prior.unknown h)⟩

theorem EffectRefinement.join {func : Func} {left right joined source : Core.Eff}
    (leftBound : EffectRefinement func left source)
    (rightBound : EffectRefinement func right source)
    (combined : EffectJoin left right joined) : EffectRefinement func joined source := by
  obtain ⟨reads, writes, grows, shrinks, rebinds, aborts, outputs, unknown⟩ := combined
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro target member
    exact (storageTargets_origin_of_join reads member).elim
      (leftBound.reads target) (rightBound.reads target)
  · intro target member
    exact (storageTargets_origin_of_join writes member).elim
      (leftBound.writes target) (rightBound.writes target)
  · intro target member
    exact (storageTargets_origin_of_join grows member).elim
      (leftBound.grows target) (rightBound.grows target)
  · intro target member
    exact (storageTargets_origin_of_join shrinks member).elim
      (leftBound.shrinks target) (rightBound.shrinks target)
  · intro target member
    exact (rebinds target |>.mp member).elim (leftBound.rebinds target) (rightBound.rebinds target)
  · intro found
    rw [aborts] at found
    simp only [Bool.or_eq_true] at found
    exact found.elim leftBound.aborts rightBound.aborts
  · intro found
    rw [outputs] at found
    simp only [Bool.or_eq_true] at found
    exact found.elim leftBound.outputs rightBound.outputs
  · intro found
    rw [unknown] at found
    simp only [Bool.or_eq_true] at found
    exact found.elim leftBound.unknown rightBound.unknown

theorem effectRefinement_empty (func : Func) (source : Core.Eff) :
    EffectRefinement func {} source := by
  constructor <;> intros <;> simp_all [Func.storageTargets]

theorem effectStep_refines_of_delta {module : GIR.Module} {vt : Array (Option VTy)}
    {func : Func} {provenance : Prov} {effect source : Core.Eff} {inst : Inst}
    (prior : EffectRefinement func effect source)
    (delta : EffectRefinement func (func.effectStep module vt provenance {} inst) source) :
    EffectRefinement func (func.effectStep module vt provenance effect inst) source :=
  prior.join delta (effectStep_join module vt func provenance effect inst)

theorem effects_refine_of_instruction_bounds {module : GIR.Module} {func : Func}
    {provenance : Prov} {source : Core.Eff}
    (closed : ∀ block ∈ func.blocks.toList, ∀ inst ∈ block.insts,
      EffectRefinement func (func.effectStep module (func.valueTypes module) provenance {} inst) source) :
    EffectRefinement func (func.effects module provenance) source := by
  rw [effects_fold_step]
  apply List.foldlRecOn (motive := fun effect => EffectRefinement func effect source)
    func.blocks.toList _ (effectRefinement_empty func source)
  intro accumulated prior block member
  apply List.foldlRecOn (motive := fun effect => EffectRefinement func effect source)
    block.insts _ prior
  intro accumulated prior inst instMember
  exact effectStep_refines_of_delta prior (closed block member inst instMember)

theorem effectRefinement_addReads {func : Func} {actual source : Core.Eff}
    {actualRoots sourceRoots : List RootRef} (closed : ParameterRootsClosed func)
    (prior : EffectRefinement func actual source)
    (roots : RootsRefine func actualRoots sourceRoots) :
    EffectRefinement func { actual with reads := addTargets actual.reads (rootsTargets actualRoots) }
      { source with reads := addTargets source.reads (rootsTargets sourceRoots) } := by
  refine ⟨?_, prior.writes, prior.grows, prior.shrinks, prior.rebinds,
    prior.aborts, prior.outputs, prior.unknown⟩
  intro target member
  rcases storageTargets_addTargets_origin member with priorMember | newMember
  · exact storageTargets_mono (fun t h => addTargets_left _ _ t h) target
      (prior.reads target priorMember)
  · exact storageTargets_mono (fun t h => addTargets_right _ _ t h) target
      (roots.targets closed target newMember)

end Goose.Lower.Validation.SummaryPreservation
