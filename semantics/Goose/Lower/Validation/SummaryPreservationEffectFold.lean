import Goose.Lower.Validation.SummaryPreservationEffectStep

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

def EffectJoin (left right joined : Core.Eff) : Prop :=
  (∀ target, target ∈ joined.reads ↔ target ∈ left.reads ∨ target ∈ right.reads) ∧
  (∀ target, target ∈ joined.writes ↔ target ∈ left.writes ∨ target ∈ right.writes) ∧
  (∀ target, target ∈ joined.grows ↔ target ∈ left.grows ∨ target ∈ right.grows) ∧
  (∀ target, target ∈ joined.shrinks ↔ target ∈ left.shrinks ∨ target ∈ right.shrinks) ∧
  (∀ target, target ∈ joined.rebinds ↔ target ∈ left.rebinds ∨ target ∈ right.rebinds) ∧
  joined.aborts = (left.aborts || right.aborts) ∧
  joined.outputs = (left.outputs || right.outputs) ∧
  joined.unknown = (left.unknown || right.unknown)

set_option maxHeartbeats 800000 in
theorem effectStep_join (module : GIR.Module) (vt : Array (Option VTy)) (func : Func)
    (provenance : Prov) (effect : Core.Eff) (inst : Inst) :
    EffectJoin effect (func.effectStep module vt provenance {} inst)
      (func.effectStep module vt provenance effect inst) := by
  cases inst with
  | «def» result op =>
    cases op <;> simp [Func.effectStep, EffectJoin, mem_addTargets_iff]
    all_goals repeat' first | (solve | simp_all [mem_addTargets_iff]) | split
  | eff op =>
    cases op <;> simp [Func.effectStep, EffectJoin, mem_addTargets_iff]
    all_goals repeat' first | (solve | simp_all [mem_addTargets_iff]) | split
  | term term =>
    cases term <;> simp [Func.effectStep, EffectJoin, mem_addTargets_iff]
    all_goals repeat' first | (solve | simp_all [mem_addTargets_iff]) | split

theorem storageTargets_origin_of_join {func : Func} {left right joined : List Target}
    {target : Target} (join : ∀ item, item ∈ joined ↔ item ∈ left ∨ item ∈ right)
    (member : target ∈ func.storageTargets joined) :
    target ∈ func.storageTargets left ∨ target ∈ func.storageTargets right := by
  obtain ⟨source, sourceMember, targetMember⟩ := List.mem_flatMap.mp member
  exact (join source |>.mp sourceMember).elim
    (fun member => Or.inl (List.mem_flatMap.mpr ⟨source, member, targetMember⟩))
    (fun member => Or.inr (List.mem_flatMap.mpr ⟨source, member, targetMember⟩))

theorem EffectReplay.join {func : Func} {left right joined source : Core.Eff}
    (leftBound : EffectReplay func left source) (rightBound : EffectReplay func right source)
    (combined : EffectJoin left right joined) : EffectReplay func joined source := by
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

theorem effectReplay_empty (func : Func) (source : Core.Eff) : EffectReplay func {} source := by
  constructor <;> intros <;> simp_all [Func.storageTargets]

theorem effectStep_replay_of_delta {module : GIR.Module} {vt : Array (Option VTy)}
    {func : Func} {provenance : Prov} {effect source : Core.Eff} {inst : Inst}
    (prior : EffectReplay func effect source)
    (delta : EffectReplay func (func.effectStep module vt provenance {} inst) source) :
    EffectReplay func (func.effectStep module vt provenance effect inst) source :=
  prior.join delta (effectStep_join module vt func provenance effect inst)

theorem effects_replay_of_instruction_bounds {module : GIR.Module} {func : Func}
    {provenance : Prov} {source : Core.Eff}
    (closed : ∀ block ∈ func.blocks.toList, ∀ inst ∈ block.insts,
      EffectReplay func (func.effectStep module (func.valueTypes module) provenance {} inst) source) :
    EffectReplay func (func.effects module provenance) source := by
  rw [effects_fold_step]
  apply List.foldlRecOn (motive := fun effect => EffectReplay func effect source)
    func.blocks.toList _ (effectReplay_empty func source)
  intro accumulated prior block member
  apply List.foldlRecOn (motive := fun effect => EffectReplay func effect source)
    block.insts _ prior
  intro accumulated prior inst instMember
  exact effectStep_replay_of_delta prior (closed block member inst instMember)

end Goose.Lower.Validation.SummaryPreservation
