import Goose.Lower.Validation.SummaryPreservationEffectRefinement

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem effectStep_load_refines {module : GIR.Module} {func : Func}
    {vt : Array (Option VTy)} {provenance : Prov} {actual source : Core.Eff}
    {result address : ValueId} {sourceRoots : List RootRef}
    (closed : ParameterRootsClosed func)
    (prior : EffectRefinement func actual source)
    (roots : RootsRefine func (rootsAt provenance.vals address) sourceRoots) :
    EffectRefinement func (func.effectStep module vt provenance actual (.def result (.load address)))
      { source with reads := addTargets source.reads (rootsTargets sourceRoots) } :=
  effectRefinement_addReads closed prior roots

theorem effectStep_snapshot_refines {module : GIR.Module} {func : Func}
    {vt : Array (Option VTy)} {provenance : Prov} {actual source : Core.Eff}
    {result address : ValueId} {kind : SnapshotMode} {sourceRoots : List RootRef}
    (closed : ParameterRootsClosed func)
    (prior : EffectRefinement func actual source)
    (roots : RootsRefine func (rootsAt provenance.vals address) sourceRoots) :
    EffectRefinement func (func.effectStep module vt provenance actual (.def result (.snapshot kind address)))
      { source with reads := addTargets source.reads (rootsTargets sourceRoots) } :=
  effectRefinement_addReads closed prior roots

theorem effectStep_arrayLen_refines {module : GIR.Module} {func : Func}
    {vt : Array (Option VTy)} {provenance : Prov} {actual source : Core.Eff}
    {result address : ValueId} {sourceRoots : List RootRef}
    (closed : ParameterRootsClosed func)
    (prior : EffectRefinement func actual source)
    (roots : RootsRefine func (rootsAt provenance.vals address) sourceRoots) :
    EffectRefinement func (func.effectStep module vt provenance actual (.def result (.arrayLen address)))
      { source with reads := addTargets source.reads (rootsTargets sourceRoots) } :=
  effectRefinement_addReads closed prior roots

theorem effectStep_load_refines_from_source {module : GIR.Module} {func : Func}
    {vt : Array (Option VTy)} {provenance : Prov} {actual : Core.Eff}
    {before after : RState} {result address : ValueId} {sourceRoots : List RootRef}
    (closed : ParameterRootsClosed func)
    (prior : EffectRefinement func actual before.eff)
    (roots : RootsRefine func (rootsAt provenance.vals address) sourceRoots)
    (sourceStep : addReads sourceRoots before = .ok ((), after)) :
    EffectRefinement func (func.effectStep module vt provenance actual (.def result (.load address)))
      after.eff := by
  unfold addReads addRoots at sourceStep
  have pair := (st_modify_ok _ _ _).mp sourceStep
  have state := congrArg Prod.snd pair
  dsimp only at state
  rw [state]
  exact effectStep_load_refines closed prior roots

theorem effectRefinement_noteAborts {func : Func} {actual source : Core.Eff}
    (prior : EffectRefinement func actual source) :
    EffectRefinement func { actual with aborts := true } { source with aborts := true } :=
  ⟨prior.reads, prior.writes, prior.grows, prior.shrinks, prior.rebinds,
    fun _ => rfl, prior.outputs, prior.unknown⟩

theorem effectRefinement_noteOutputs {func : Func} {actual source : Core.Eff}
    (prior : EffectRefinement func actual source) :
    EffectRefinement func { actual with outputs := true } { source with outputs := true } :=
  ⟨prior.reads, prior.writes, prior.grows, prior.shrinks, prior.rebinds,
    prior.aborts, fun _ => rfl, prior.unknown⟩

theorem effectStep_neg_refines {module : GIR.Module} {func : Func}
    {vt : Array (Option VTy)} {provenance : Prov} {actual source : Core.Eff}
    {result value : ValueId} {ty : IntTy} {origin : Option OriginId}
    (prior : EffectRefinement func actual source) :
    EffectRefinement func (func.effectStep module vt provenance actual (.def result (.un .neg ty value origin)))
      { source with aborts := true } := effectRefinement_noteAborts prior

theorem effectStep_bin_refines {module : GIR.Module} {func : Func}
    {vt : Array (Option VTy)} {provenance : Prov} {actual source : Core.Eff}
    {result left right : ValueId} {op : BinOp} {ty : IntTy} {origin : Option OriginId}
    (prior : EffectRefinement func actual source) :
    EffectRefinement func (func.effectStep module vt provenance actual
      (.def result (.bin op ty left right origin)))
      (if op.mayAbort then { source with aborts := true } else source) := by
  change EffectRefinement func (if op.mayAbort then { actual with aborts := true } else actual) _
  split
  · exact effectRefinement_noteAborts prior
  · exact prior

theorem effectStep_print_refines {module : GIR.Module} {func : Func}
    {vt : Array (Option VTy)} {provenance : Prov} {actual source : Core.Eff}
    {args : List PrintPart} {origin : Option OriginId}
    (prior : EffectRefinement func actual source) :
    EffectRefinement func (func.effectStep module vt provenance actual (.eff (.print args origin)))
      { source with outputs := true } := effectRefinement_noteOutputs prior


end Goose.Lower.Validation.SummaryPreservation
