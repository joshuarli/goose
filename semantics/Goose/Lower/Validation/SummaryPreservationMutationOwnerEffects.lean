import Goose.Lower.Validation.SummaryPreservationMutationEffects

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem limitedOwner_matches_valueType {env : PEnv} {place : Place} {ty : Ty}
    {vt : Array (Option VTy)} {address : ValueId} {mu : Mutability}
    (sourceType : env.access.placeType? place = some ty)
    (actualType : vt[address]? = some (some (.data (.ref mu ty)))) :
    env.limitedOwner place = .ok (ownerIsLimited vt address) := by
  cases ty <;> simp [PEnv.limitedOwner, sourceType, ownerIsLimited, ownerTy, actualType] <;> rfl


theorem effectStep_push_refines {module : GIR.Module} {vt : Array (Option VTy)}
    {func : Func} {provenance : Prov} {actual source : Core.Eff} {result address value : ValueId}
    {origin : Option OriginId} {sourceRoots : List RootRef} {limited : Bool}
    (closed : ParameterRootsClosed func) (prior : EffectRefinement func actual source)
    (roots : RootsRefine func (rootsAt provenance.vals address) sourceRoots)
    (owner : ownerIsLimited vt address = limited) :
    EffectRefinement func (func.effectStep module vt provenance actual (.def result (.push address value origin)))
      (if module.profile == .shrink then
        { source with
          grows := addTargets source.grows (rootsTargets sourceRoots)
          writes := addTargets source.writes (rootsTargets sourceRoots)
          aborts := source.aborts || limited }
      else { source with grows := addTargets source.grows (rootsTargets sourceRoots) }) := by
  simp only [Func.effectStep, owner]
  split
  · exact effectRefinement_addAborts
      (effectRefinement_addWrites closed (effectRefinement_addGrows closed prior roots) roots) limited
  · exact effectRefinement_addGrows closed prior roots


theorem effectStep_append_refines {module : GIR.Module} {vt : Array (Option VTy)}
    {func : Func} {provenance : Prov} {actual source : Core.Eff} {address value : ValueId}
    {origin : Option OriginId} {sourceRoots sourceValueRoots : List RootRef} {limited : Bool}
    (closed : ParameterRootsClosed func) (prior : EffectRefinement func actual source)
    (roots : RootsRefine func (rootsAt provenance.vals address) sourceRoots)
    (values : RootsRefine func (rootsAt provenance.vals value) sourceValueRoots)
    (owner : ownerIsLimited vt address = limited) :
    EffectRefinement func (func.effectStep module vt provenance actual (.eff (.append address value origin)))
      (if module.profile == .shrink then
        { source with
          reads := addTargets source.reads (rootsTargets sourceValueRoots)
          grows := addTargets source.grows (rootsTargets sourceRoots)
          writes := addTargets source.writes (rootsTargets sourceRoots)
          aborts := source.aborts || limited }
      else { source with
        reads := addTargets source.reads (rootsTargets sourceValueRoots)
        grows := addTargets source.grows (rootsTargets sourceRoots) }) := by
  simp only [Func.effectStep, owner]
  split
  · exact effectRefinement_addAborts
      (effectRefinement_addWrites closed
        (effectRefinement_addGrows closed (effectRefinement_addReads closed prior values) roots) roots) limited
  · exact effectRefinement_addGrows closed (effectRefinement_addReads closed prior values) roots


theorem effectStep_resize_refines {module : GIR.Module} {vt : Array (Option VTy)}
    {func : Func} {provenance : Prov} {actual source : Core.Eff} {address size : ValueId}
    {fill : Option ValueId} {origin : Option OriginId} {sourceRoots : List RootRef}
    (closed : ParameterRootsClosed func) (prior : EffectRefinement func actual source)
    (roots : RootsRefine func (rootsAt provenance.vals address) sourceRoots) :
    EffectRefinement func (func.effectStep module vt provenance actual (.eff (.resize address size fill origin)))
      (match fill with
      | none => { source with
          reads := addTargets source.reads (rootsTargets sourceRoots)
          shrinks := addTargets source.shrinks (rootsTargets sourceRoots)
          aborts := true }
      | some _ => { source with
          reads := addTargets source.reads (rootsTargets sourceRoots)
          writes := addTargets source.writes (rootsTargets sourceRoots)
          grows := addTargets source.grows (rootsTargets sourceRoots)
          shrinks := addTargets source.shrinks (rootsTargets sourceRoots)
          aborts := true }) := by
  cases fill with
  | none =>
    exact effectRefinement_noteAborts
      (effectRefinement_addShrinks closed (effectRefinement_addReads closed prior roots) roots)
  | some value =>
    exact effectRefinement_addGrows closed
      (effectRefinement_addWrites closed
        (effectRefinement_noteAborts
          (effectRefinement_addShrinks closed (effectRefinement_addReads closed prior roots) roots)) roots) roots

end Goose.Lower.Validation.SummaryPreservation
