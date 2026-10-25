import Goose.Lower.Validation.SummaryPreservationEffectRefinement
import Goose.Lower.Validation.SummaryPreservationCallEffects

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

def EffectTargetsBelow (left right : Core.Eff) : Prop :=
  EffLe left right ∧ RebindsLe left right ∧ EffectFlagsLe left right

theorem EffectTargetsBelow.refines {func : Func} {left right : Core.Eff}
    (below : EffectTargetsBelow left right) : EffectRefinement func left right :=
  ⟨storageTargets_mono below.1.1, storageTargets_mono below.1.2.1,
    storageTargets_mono below.1.2.2.1, storageTargets_mono below.1.2.2.2.1,
    below.2.1, below.2.2.1, below.2.2.2, below.1.2.2.2.2⟩

theorem rootsTargets_mono {left right : List RootRef}
    (below : ∀ root ∈ left, root ∈ right) :
    ∀ target ∈ rootsTargets left, target ∈ rootsTargets right := by
  intro target member
  obtain ⟨root, rootMember, mapped⟩ := List.mem_filterMap.mp member
  exact List.mem_filterMap.mpr ⟨root, below root rootMember, mapped⟩

theorem expandedArgumentRoots_mono {func : Func} {before after : Prov}
    (below : ProvenanceBelow before after) (value : ValueId) :
    ∀ root ∈ ((rootsAt before.vals value).flatMap func.expandParameterRoot).foldl
      (fun acc item => unionRoots acc [item]) [],
      root ∈ ((rootsAt after.vals value).flatMap func.expandParameterRoot).foldl
        (fun acc item => unionRoots acc [item]) [] := by
  intro root member
  simp only [mem_union_singletons_fold, List.not_mem_nil, false_or] at member ⊢
  obtain ⟨source, sourceMember, rootMember⟩ := List.mem_flatMap.mp member
  exact List.mem_flatMap.mpr ⟨source, below.vals _ _ sourceMember, rootMember⟩

theorem mapSummaryTargets_mono {left right : List (List RootRef)}
    (below : ∀ (index : Nat) root, root ∈ left[index]?.getD [] → root ∈ right[index]?.getD [])
    (targets : List Target) :
    ∀ target ∈ mapSummaryTargets left targets, target ∈ mapSummaryTargets right targets := by
  induction targets with
  | nil => simp [mapSummaryTargets]
  | cons head rest ih =>
    intro target member
    cases head with
    | global global =>
      rcases List.mem_cons.mp member with same | tail
      · exact List.mem_cons.mpr (Or.inl same)
      · exact List.mem_cons_of_mem _ (ih target tail)
    | param index =>
      rcases List.mem_append.mp member with argument | tail
      · exact List.mem_append.mpr (Or.inl (rootsTargets_mono (below index) target argument))
      · exact List.mem_append.mpr (Or.inr (ih target tail))

theorem mappedCallTargets_mono {func : Func} {before after : Prov}
    (below : ProvenanceBelow before after) (arguments : List ValueId) (targets : List Target) :
    ∀ target ∈ mapSummaryTargets (arguments.map fun value =>
      ((rootsAt before.vals value).flatMap func.expandParameterRoot).foldl
        (fun acc root => unionRoots acc [root]) []) targets,
      target ∈ mapSummaryTargets (arguments.map fun value =>
      ((rootsAt after.vals value).flatMap func.expandParameterRoot).foldl
        (fun acc root => unionRoots acc [root]) []) targets := by
  apply mapSummaryTargets_mono
  intro index root member
  cases lookup : arguments[index]? with
  | none => simp [List.getElem?_map, lookup] at member
  | some value =>
    simp only [List.getElem?_map, lookup, Option.map_some, Option.getD_some] at member ⊢
    exact expandedArgumentRoots_mono below value root member

theorem filterMap_mono {α β : Type} {left right : List α} (mapping : α → Option β)
    (below : ∀ item ∈ left, item ∈ right) :
    ∀ item ∈ left.filterMap mapping, item ∈ right.filterMap mapping := by
  intro item member
  obtain ⟨source, sourceMember, mapped⟩ := List.mem_filterMap.mp member
  exact List.mem_filterMap.mpr ⟨source, below source sourceMember, mapped⟩

theorem addTargets_mono {left left' right right' : List Target}
    (leftBound : ∀ target ∈ left, target ∈ left')
    (rightBound : ∀ target ∈ right, target ∈ right') :
    ∀ target ∈ addTargets left right, target ∈ addTargets left' right' := by
  intro target member
  exact (mem_addTargets_iff.mp member).elim
    (fun h => addTargets_left _ _ target (leftBound target h))
    (fun h => addTargets_right _ _ target (rightBound target h))

set_option maxHeartbeats 1000000 in
theorem effectStep_delta_targets_mono {module : GIR.Module} {vt : Array (Option VTy)}
    {func : Func} {before after : Prov} (below : ProvenanceBelow before after) (inst : Inst) :
    EffectTargetsBelow (func.effectStep module vt before {} inst)
      (func.effectStep module vt after {} inst) := by
  have targets (value : ValueId) := rootsTargets_mono (below.vals value)
  cases inst with
  | «def» result op =>
    cases op with
    | call callee args origin =>
      cases lookup : module.funcs[callee]? with
      | none => simp [Func.effectStep, lookup, EffectTargetsBelow, EffLe, RebindsLe, EffectFlagsLe]
      | some calleeFunc =>
        cases summary : calleeFunc.summary with
        | unknown => simp [Func.effectStep, lookup, summary, EffectTargetsBelow, EffLe, RebindsLe, EffectFlagsLe]
        | known sm =>
          simp only [Func.effectStep, lookup, summary]
          simp only [EffectTargetsBelow, EffLe, RebindsLe, EffectFlagsLe]
          refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
          all_goals first
            | (intro target member
               simp only [mem_addTargets_iff, List.not_mem_nil, false_or] at member ⊢
               rcases member with argument | annotation
               · exact Or.inl (mappedCallTargets_mono (func := func) below args _ target argument)
               · exact Or.inr annotation)
            | simp
    | _ =>
      all_goals simp [Func.effectStep, EffectTargetsBelow, EffLe, RebindsLe,
        EffectFlagsLe, mem_addTargets_iff, targetsOf]
      all_goals repeat' first | (solve | simp_all [mem_addTargets_iff]) | split
      all_goals exact targets _
  | eff op =>
    cases op <;> simp [Func.effectStep, EffectTargetsBelow, EffLe, RebindsLe,
      EffectFlagsLe, mem_addTargets_iff, targetsOf]
    all_goals repeat' first | (solve | simp_all [mem_addTargets_iff]) | split
    all_goals constructor
    all_goals first
      | exact targets _
      | (intro target root member mapped; exact ⟨root, below.vals _ _ member, mapped⟩)
  | term term =>
    cases term <;> simp [Func.effectStep, EffectTargetsBelow, EffLe, RebindsLe,
      EffectFlagsLe, mem_addTargets_iff]

theorem effects_refine_of_upper {module : GIR.Module} {func : Func}
    {actual upper : Prov} {source : Core.Eff}
    (below : ProvenanceBelow actual upper)
    (closed : ∀ block ∈ func.blocks.toList, ∀ inst ∈ block.insts,
      EffectRefinement func (func.effectStep module (func.valueTypes module) upper {} inst) source) :
    EffectRefinement func (func.effects module actual) source := by
  apply effects_refine_of_instruction_bounds
  intro block blockMember inst instMember
  exact (effectStep_delta_targets_mono below inst).refines.trans
    (closed block blockMember inst instMember)

end Goose.Lower.Validation.SummaryPreservation
