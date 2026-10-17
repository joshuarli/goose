import Goose.Lower.Validation.SummaryPreservationRefinedEffects

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem effectRefinement_addWrites {func : Func} {actual source : Core.Eff}
    {actualRoots sourceRoots : List RootRef} (closed : ParameterRootsClosed func)
    (prior : EffectRefinement func actual source)
    (roots : RootsRefine func actualRoots sourceRoots) :
    EffectRefinement func { actual with writes := addTargets actual.writes (rootsTargets actualRoots) }
      { source with writes := addTargets source.writes (rootsTargets sourceRoots) } := by
  refine ⟨prior.reads, ?_, prior.grows, prior.shrinks, prior.rebinds, prior.aborts, prior.outputs, prior.unknown⟩
  intro target member
  rcases storageTargets_addTargets_origin member with priorMember | newMember
  · exact storageTargets_mono (fun t h => addTargets_left _ _ t h) target
      (prior.writes target priorMember)
  · exact storageTargets_mono (fun t h => addTargets_right _ _ t h) target
      (roots.targets closed target newMember)

theorem effectRefinement_addGrows {func : Func} {actual source : Core.Eff}
    {actualRoots sourceRoots : List RootRef} (closed : ParameterRootsClosed func)
    (prior : EffectRefinement func actual source)
    (roots : RootsRefine func actualRoots sourceRoots) :
    EffectRefinement func { actual with grows := addTargets actual.grows (rootsTargets actualRoots) }
      { source with grows := addTargets source.grows (rootsTargets sourceRoots) } := by
  refine ⟨prior.reads, prior.writes, ?_, prior.shrinks, prior.rebinds, prior.aborts, prior.outputs, prior.unknown⟩
  intro target member
  rcases storageTargets_addTargets_origin member with priorMember | newMember
  · exact storageTargets_mono (fun t h => addTargets_left _ _ t h) target
      (prior.grows target priorMember)
  · exact storageTargets_mono (fun t h => addTargets_right _ _ t h) target
      (roots.targets closed target newMember)

theorem effectRefinement_addShrinks {func : Func} {actual source : Core.Eff}
    {actualRoots sourceRoots : List RootRef} (closed : ParameterRootsClosed func)
    (prior : EffectRefinement func actual source)
    (roots : RootsRefine func actualRoots sourceRoots) :
    EffectRefinement func { actual with shrinks := addTargets actual.shrinks (rootsTargets actualRoots) }
      { source with shrinks := addTargets source.shrinks (rootsTargets sourceRoots) } := by
  refine ⟨prior.reads, prior.writes, prior.grows, ?_, prior.rebinds, prior.aborts, prior.outputs, prior.unknown⟩
  intro target member
  rcases storageTargets_addTargets_origin member with priorMember | newMember
  · exact storageTargets_mono (fun t h => addTargets_left _ _ t h) target
      (prior.shrinks target priorMember)
  · exact storageTargets_mono (fun t h => addTargets_right _ _ t h) target
      (roots.targets closed target newMember)

theorem effectRefinement_addAborts {func : Func} {actual source : Core.Eff}
    (prior : EffectRefinement func actual source) (extra : Bool) :
    EffectRefinement func { actual with aborts := actual.aborts || extra }
      { source with aborts := source.aborts || extra } := by
  refine ⟨prior.reads, prior.writes, prior.grows, prior.shrinks, prior.rebinds,
    ?_, prior.outputs, prior.unknown⟩
  intro found
  simp only [Bool.or_eq_true] at found ⊢
  exact found.elim (fun h => Or.inl (prior.aborts h)) Or.inr


theorem effectStep_clear_refines {module : GIR.Module} {vt : Array (Option VTy)}
    {func : Func} {provenance : Prov} {actual source : Core.Eff} {address : ValueId}
    {origin : Option OriginId} {sourceRoots : List RootRef}
    (closed : ParameterRootsClosed func) (prior : EffectRefinement func actual source)
    (roots : RootsRefine func (rootsAt provenance.vals address) sourceRoots) :
    EffectRefinement func (func.effectStep module vt provenance actual (.eff (.clear address origin)))
      { source with
        reads := addTargets source.reads (rootsTargets sourceRoots)
        shrinks := addTargets source.shrinks (rootsTargets sourceRoots) } :=
  effectRefinement_addShrinks closed (effectRefinement_addReads closed prior roots) roots


theorem effectStep_pop_refines {module : GIR.Module} {vt : Array (Option VTy)}
    {func : Func} {provenance : Prov} {actual source : Core.Eff} {result address : ValueId}
    {origin : Option OriginId} {sourceRoots : List RootRef}
    (closed : ParameterRootsClosed func) (prior : EffectRefinement func actual source)
    (roots : RootsRefine func (rootsAt provenance.vals address) sourceRoots) :
    EffectRefinement func (func.effectStep module vt provenance actual (.def result (.pop address origin)))
      { source with
        reads := addTargets source.reads (rootsTargets sourceRoots)
        shrinks := addTargets source.shrinks (rootsTargets sourceRoots)
        aborts := true } :=
  effectRefinement_noteAborts
    (effectRefinement_addShrinks closed (effectRefinement_addReads closed prior roots) roots)


theorem effectStep_popN_refines {module : GIR.Module} {vt : Array (Option VTy)}
    {func : Func} {provenance : Prov} {actual source : Core.Eff} {address count : ValueId}
    {origin : Option OriginId} {sourceRoots : List RootRef}
    (closed : ParameterRootsClosed func) (prior : EffectRefinement func actual source)
    (roots : RootsRefine func (rootsAt provenance.vals address) sourceRoots) :
    EffectRefinement func (func.effectStep module vt provenance actual (.eff (.popN address count origin)))
      { source with
        reads := addTargets source.reads (rootsTargets sourceRoots)
        shrinks := addTargets source.shrinks (rootsTargets sourceRoots)
        aborts := true } :=
  effectRefinement_noteAborts
    (effectRefinement_addShrinks closed (effectRefinement_addReads closed prior roots) roots)


theorem effectStep_replace_refines {module : GIR.Module} {vt : Array (Option VTy)}
    {func : Func} {provenance : Prov} {actual source : Core.Eff} {address value : ValueId}
    {origin : Option OriginId} {sourceRoots : List RootRef}
    (closed : ParameterRootsClosed func) (prior : EffectRefinement func actual source)
    (roots : RootsRefine func (rootsAt provenance.vals address) sourceRoots) :
    EffectRefinement func (func.effectStep module vt provenance actual (.eff (.replace address value origin)))
      { source with
        reads := addTargets source.reads (rootsTargets sourceRoots)
        writes := addTargets source.writes (rootsTargets sourceRoots)
        grows := addTargets source.grows (rootsTargets sourceRoots)
        shrinks := addTargets source.shrinks (rootsTargets sourceRoots) } :=
  effectRefinement_addShrinks closed
    (effectRefinement_addGrows closed
      (effectRefinement_addWrites closed (effectRefinement_addReads closed prior roots) roots) roots) roots

end Goose.Lower.Validation.SummaryPreservation
