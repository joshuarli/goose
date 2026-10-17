import Goose.Lower.Validation.SummaryPreservationFlags
import Goose.Lower.Validation.SummaryPreservationRootBounds
import Goose.Lower.Validation.SummaryPreservationReplay

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

structure EffectReplay (func : Func) (actual source : Core.Eff) : Prop where
  reads : ∀ target ∈ func.storageTargets actual.reads, target ∈ source.reads
  writes : ∀ target ∈ func.storageTargets actual.writes, target ∈ source.writes
  grows : ∀ target ∈ func.storageTargets actual.grows, target ∈ source.grows
  shrinks : ∀ target ∈ func.storageTargets actual.shrinks, target ∈ source.shrinks
  rebinds : ∀ target ∈ actual.rebinds, target ∈ source.rebinds
  aborts : actual.aborts = true → source.aborts = true
  outputs : actual.outputs = true → source.outputs = true
  unknown : actual.unknown = true → source.unknown = true

theorem EffectReplay.source_mono {func : Func} {actual source later : Core.Eff}
    (prior : EffectReplay func actual source) (effects : EffLe source later)
    (rebinds : RebindsLe source later) (flags : EffectFlagsLe source later) :
    EffectReplay func actual later :=
  ⟨fun target member => effects.1 target (prior.reads target member),
    fun target member => effects.2.1 target (prior.writes target member),
    fun target member => effects.2.2.1 target (prior.grows target member),
    fun target member => effects.2.2.2.1 target (prior.shrinks target member),
    fun target member => rebinds target (prior.rebinds target member),
    fun h => flags.1 (prior.aborts h), fun h => flags.2 (prior.outputs h),
    fun h => effects.2.2.2.2 (prior.unknown h)⟩

theorem addTargets_origin {left right : List Target} {target : Target}
    (member : target ∈ addTargets left right) : target ∈ left ∨ target ∈ right := by
  unfold addTargets at member
  induction right generalizing left with
  | nil => exact Or.inl member
  | cons head rest ih =>
    simp only [List.foldl_cons] at member
    rcases ih member with prior | tail
    · split at prior
      · exact Or.inl prior
      · rcases List.mem_append.mp prior with prior | last
        · exact Or.inl prior
        · exact Or.inr (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp last)))
    · exact Or.inr (List.mem_cons_of_mem _ tail)

theorem mem_addTargets_iff {left right : List Target} {target : Target} :
    target ∈ addTargets left right ↔ target ∈ left ∨ target ∈ right :=
  ⟨addTargets_origin, fun member => member.elim
    (addTargets_left left right target) (addTargets_right left right target)⟩

theorem storageTargets_addTargets_origin {func : Func} {left right : List Target}
    {target : Target} (member : target ∈ func.storageTargets (addTargets left right)) :
    target ∈ func.storageTargets left ∨ target ∈ func.storageTargets right := by
  obtain ⟨source, sourceMember, targetMember⟩ := List.mem_flatMap.mp member
  exact (addTargets_origin sourceMember).elim
    (fun member => Or.inl (List.mem_flatMap.mpr ⟨source, member, targetMember⟩))
    (fun member => Or.inr (List.mem_flatMap.mpr ⟨source, member, targetMember⟩))

theorem effectReplay_addReads {func : Func} {actual source : Core.Eff}
    {actualRoots sourceRoots : List RootRef} (prior : EffectReplay func actual source)
    (roots : RootsRepresent func actualRoots sourceRoots) :
    EffectReplay func { actual with reads := addTargets actual.reads (rootsTargets actualRoots) }
      { source with reads := addTargets source.reads (rootsTargets sourceRoots) } := by
  refine ⟨?_, prior.writes, prior.grows, prior.shrinks, prior.rebinds,
    prior.aborts, prior.outputs, prior.unknown⟩
  intro target member
  rcases storageTargets_addTargets_origin member with priorMember | newMember
  · exact addTargets_left _ _ target (prior.reads target priorMember)
  · exact addTargets_right _ _ target (rootsRepresent_targets roots target newMember)

theorem effectStep_load_replay {module : GIR.Module} {func : Func}
    {vt : Array (Option VTy)} {provenance : Prov} {actual source : Core.Eff}
    {result address : ValueId} {sourceRoots : List RootRef}
    (prior : EffectReplay func actual source)
    (roots : RootsRepresent func (rootsAt provenance.vals address) sourceRoots) :
    EffectReplay func (func.effectStep module vt provenance actual (.def result (.load address)))
      { source with reads := addTargets source.reads (rootsTargets sourceRoots) } :=
  effectReplay_addReads prior roots

theorem effectStep_snapshot_replay {module : GIR.Module} {func : Func}
    {vt : Array (Option VTy)} {provenance : Prov} {actual source : Core.Eff}
    {result address : ValueId} {kind : SnapshotMode} {sourceRoots : List RootRef}
    (prior : EffectReplay func actual source)
    (roots : RootsRepresent func (rootsAt provenance.vals address) sourceRoots) :
    EffectReplay func (func.effectStep module vt provenance actual (.def result (.snapshot kind address)))
      { source with reads := addTargets source.reads (rootsTargets sourceRoots) } :=
  effectReplay_addReads prior roots

theorem effectStep_arrayLen_replay {module : GIR.Module} {func : Func}
    {vt : Array (Option VTy)} {provenance : Prov} {actual source : Core.Eff}
    {result address : ValueId} {sourceRoots : List RootRef}
    (prior : EffectReplay func actual source)
    (roots : RootsRepresent func (rootsAt provenance.vals address) sourceRoots) :
    EffectReplay func (func.effectStep module vt provenance actual (.def result (.arrayLen address)))
      { source with reads := addTargets source.reads (rootsTargets sourceRoots) } :=
  effectReplay_addReads prior roots

theorem effectStep_load_from_source {module : GIR.Module} {func : Func}
    {vt : Array (Option VTy)} {provenance : Prov} {actual : Core.Eff}
    {before after : RState} {result address : ValueId} {sourceRoots : List RootRef}
    (prior : EffectReplay func actual before.eff)
    (roots : RootsRepresent func (rootsAt provenance.vals address) sourceRoots)
    (sourceStep : addReads sourceRoots before = .ok ((), after)) :
    EffectReplay func (func.effectStep module vt provenance actual (.def result (.load address)))
      after.eff := by
  unfold addReads addRoots at sourceStep
  have pair := (st_modify_ok _ _ _).mp sourceStep
  have state := congrArg Prod.snd pair
  dsimp only at state
  rw [state]
  exact effectStep_load_replay prior roots

theorem effectReplay_noteAborts {func : Func} {actual source : Core.Eff}
    (prior : EffectReplay func actual source) :
    EffectReplay func { actual with aborts := true } { source with aborts := true } :=
  ⟨prior.reads, prior.writes, prior.grows, prior.shrinks, prior.rebinds,
    fun _ => rfl, prior.outputs, prior.unknown⟩

theorem effectReplay_noteOutputs {func : Func} {actual source : Core.Eff}
    (prior : EffectReplay func actual source) :
    EffectReplay func { actual with outputs := true } { source with outputs := true } :=
  ⟨prior.reads, prior.writes, prior.grows, prior.shrinks, prior.rebinds,
    prior.aborts, fun _ => rfl, prior.unknown⟩

theorem effectStep_neg_replay {module : GIR.Module} {func : Func}
    {vt : Array (Option VTy)} {provenance : Prov} {actual source : Core.Eff}
    {result value : ValueId} {ty : IntTy} {origin : Option OriginId}
    (prior : EffectReplay func actual source) :
    EffectReplay func (func.effectStep module vt provenance actual (.def result (.un .neg ty value origin)))
      { source with aborts := true } := effectReplay_noteAborts prior

theorem effectStep_bin_replay {module : GIR.Module} {func : Func}
    {vt : Array (Option VTy)} {provenance : Prov} {actual source : Core.Eff}
    {result left right : ValueId} {op : BinOp} {ty : IntTy} {origin : Option OriginId}
    (prior : EffectReplay func actual source) :
    EffectReplay func (func.effectStep module vt provenance actual
      (.def result (.bin op ty left right origin)))
      (if op.mayAbort then { source with aborts := true } else source) := by
  change EffectReplay func (if op.mayAbort then { actual with aborts := true } else actual) _
  split
  · exact effectReplay_noteAborts prior
  · exact prior

theorem effectStep_print_replay {module : GIR.Module} {func : Func}
    {vt : Array (Option VTy)} {provenance : Prov} {actual source : Core.Eff}
    {args : List PrintPart} {origin : Option OriginId}
    (prior : EffectReplay func actual source) :
    EffectReplay func (func.effectStep module vt provenance actual (.eff (.print args origin)))
      { source with outputs := true } := effectReplay_noteOutputs prior

theorem effects_fold_step (module : GIR.Module) (func : Func) (provenance : Prov) :
    func.effects module provenance = func.blocks.toList.foldl
      (fun effect block => block.insts.foldl
        (func.effectStep module (func.valueTypes module) provenance) effect) {} := by
  simp only [Func.effects, Array.foldl_toList]

end Goose.Lower.Validation.SummaryPreservation
