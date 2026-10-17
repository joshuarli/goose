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

theorem effects_fold_step (module : GIR.Module) (func : Func) (provenance : Prov) :
    func.effects module provenance = func.blocks.toList.foldl
      (fun effect block => block.insts.foldl
        (func.effectStep module (func.valueTypes module) provenance) effect) {} := by
  simp only [Func.effects, Array.foldl_toList]

end Goose.Lower.Validation.SummaryPreservation
