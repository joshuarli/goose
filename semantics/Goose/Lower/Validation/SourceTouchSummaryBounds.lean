import Goose.Lower.Validation.SummaryPreservationModuleEffects
import Goose.Lower.Validation.SummaryPreservationEffectFold
import Goose.GIR.Sound
import Goose.GIR.ReplacementContentFlowProofsSliceDependencyAtoms

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

def effectTouchTargets (effect : Core.Eff) : List Target :=
  effect.reads ++ effect.writes ++ effect.grows ++ effect.shrinks

def summaryTouchTargets (summary : Summary) : List Target :=
  summary.reads ++ summary.writes ++ summary.grows ++ summary.shrinks

def summaryTouchRoots (_module : GIR.Module) (func : Func) : Option (List RootRef) :=
  match func.summary with
  | .unknown => none
  | .known summary => some ((func.storageTargets (summaryTouchTargets summary)).map fun
      | .param index => .param index
      | .global index => .global index)

theorem effectTouchTargets_step_join (module : GIR.Module) (vt : Array (Option VTy))
    (func : Func) (provenance : Prov) (prior : Core.Eff) (inst : Inst) (target : Target) :
    target ∈ effectTouchTargets (func.effectStep module vt provenance prior inst) ↔
      target ∈ effectTouchTargets prior ∨
      target ∈ effectTouchTargets (func.effectStep module vt provenance {} inst) := by
  obtain ⟨reads, writes, grows, shrinks, _⟩ := effectStep_join module vt func provenance prior inst
  simp only [effectTouchTargets, List.mem_append, reads, writes, grows, shrinks]
  simp only [or_assoc, or_left_comm]

private theorem fold_preserves {α β : Type} (step : α → β → α) (predicate : α → Prop)
    (monotone : ∀ state item, predicate state → predicate (step state item))
    (items : List β) {initial : α} (prior : predicate initial) :
    predicate (items.foldl step initial) := by
  induction items generalizing initial with
  | nil => exact prior
  | cons item rest ih => exact ih (monotone initial item prior)

private theorem fold_contains {α β : Type} (step : α → β → α) (predicate : α → Prop)
    (monotone : ∀ state item, predicate state → predicate (step state item))
    (items : List β) {item : β} (member : item ∈ items)
    (introduced : ∀ state, predicate (step state item)) (initial : α) :
    predicate (items.foldl step initial) := by
  induction items generalizing initial with
  | nil => simp at member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with same | member
    · subst first
      exact fold_preserves step predicate monotone rest (introduced initial)
    · exact ih member (step initial first)

theorem instruction_touch_targets_within_effects {module : GIR.Module} {func : Func}
    {provenance : Prov} {block : GIR.Block} {inst : Inst} {target : Target}
    (blockMember : block ∈ func.blocks.toList) (instMember : inst ∈ block.insts)
    (member : target ∈ effectTouchTargets
      (func.effectStep module (func.valueTypes module) provenance {} inst)) :
    target ∈ effectTouchTargets (func.effects module provenance) := by
  rw [effects_fold_step]
  let predicate := fun effect => target ∈ effectTouchTargets effect
  have monotone : ∀ effect instruction, predicate effect →
      predicate (func.effectStep module (func.valueTypes module) provenance effect instruction) := by
    intro effect instruction prior
    exact (effectTouchTargets_step_join module _ func provenance effect instruction target).mpr
      (Or.inl prior)
  apply fold_contains _ predicate (fun effect block prior =>
    fold_preserves _ predicate monotone block.insts prior) _ blockMember
  intro effect
  exact fold_contains _ predicate monotone block.insts instMember
    (fun prior => (effectTouchTargets_step_join module _ func provenance prior inst target).mpr
      (Or.inr member)) effect

theorem accepted_instruction_touch_storage_bound {module : Core.Module} {index : Nat}
    {func : Func} {summary : Summary} {block : GIR.Block} {inst : Inst} {target : Target}
    (accepted : Core.validate module = .ok ())
    (functionRow : (lower module).funcs[index]? = some func)
    (known : func.summary = .known summary)
    (blockMember : block ∈ func.blocks.toList) (instMember : inst ∈ block.insts)
    (member : target ∈ func.storageTargets (effectTouchTargets
      (func.effectStep (lower module) (func.valueTypes (lower module))
        (func.provenance (resultRoots (lower module) (lower module).implTypes)
          ((lower module).implTypes[index]?.getD #[]) (lower module).rootCount) {} inst))) :
    target ∈ func.storageTargets (summaryTouchTargets summary) := by
  have closed := GIR.within_of_closed (accepted_module_function_summaryClosed accepted functionRow)
  simp only [EffectsWithin, known] at closed
  obtain ⟨_, reads, writes, grows, shrinks, _⟩ := closed
  obtain ⟨source, sourceMember, expanded⟩ := List.mem_flatMap.mp member
  have all := instruction_touch_targets_within_effects blockMember instMember sourceMember
  simp only [effectTouchTargets, List.mem_append] at all
  have lift (targets : List Target)
      (subset : ∀ item ∈ targets, item ∈ summaryTouchTargets summary)
      (bounded : target ∈ func.storageTargets targets) :
      target ∈ func.storageTargets (summaryTouchTargets summary) := by
    obtain ⟨item, itemMember, rootMember⟩ := List.mem_flatMap.mp bounded
    exact List.mem_flatMap.mpr ⟨item, subset item itemMember, rootMember⟩
  rcases all with ((read | write) | grow) | shrink
  · exact lift summary.reads (fun item h => by simp [summaryTouchTargets, h])
      (reads target (List.mem_flatMap.mpr ⟨source, read, expanded⟩))
  · exact lift summary.writes (fun item h => by simp [summaryTouchTargets, h])
      (writes target (List.mem_flatMap.mpr ⟨source, write, expanded⟩))
  · exact lift summary.grows (fun item h => by simp [summaryTouchTargets, h])
      (grows target (List.mem_flatMap.mpr ⟨source, grow, expanded⟩))
  · exact lift summary.shrinks (fun item h => by simp [summaryTouchTargets, h])
      (shrinks target (List.mem_flatMap.mpr ⟨source, shrink, expanded⟩))

def directTouchOperands : Inst → List ValueId
  | .def _ (.load owner) | .def _ (.arrayLen owner) | .def _ (.snapshot _ owner)
  | .def _ (.push owner _ _) | .def _ (.pop owner _) => [owner]
  | .eff (.store owner _ _) | .eff (.popN owner _ _) | .eff (.resize owner _ _ _)
  | .eff (.clear owner _) | .eff (.replace owner _ _) => [owner]
  | .eff (.append owner source _) => [owner, source]
  | _ => []

set_option maxHeartbeats 400000 in
theorem directTouchOperands_effectStep {module : GIR.Module} {func : Func}
    {vt : Array (Option VTy)} {provenance : Prov} {inst : Inst} {owner : ValueId}
    {target : Target} (operand : owner ∈ directTouchOperands inst)
    (member : target ∈ targetsOf (rootsAt provenance.vals owner)) :
    target ∈ effectTouchTargets (func.effectStep module vt provenance {} inst) := by
  cases inst with
  | «def» result op =>
    cases op <;> simp only [directTouchOperands, List.mem_singleton, List.not_mem_nil] at operand
    all_goals try contradiction
    all_goals subst owner
    all_goals simp [Func.effectStep, effectTouchTargets, mem_addTargets_iff, member]
    all_goals split <;> simp_all [mem_addTargets_iff]
  | eff op =>
    cases op <;> simp only [directTouchOperands, List.not_mem_nil,
      List.mem_cons, or_false] at operand
    all_goals try contradiction
    all_goals first | subst owner | rcases operand with rfl | rfl
    all_goals simp [Func.effectStep, effectTouchTargets, mem_addTargets_iff, member]
    all_goals split <;> simp_all [mem_addTargets_iff]
  | term term => simp [directTouchOperands] at operand

theorem accepted_direct_touch_storage_bound {module : Core.Module} {index : Nat}
    {func : Func} {summary : Summary} {block : GIR.Block} {inst : Inst} {owner : ValueId}
    {target : Target} (accepted : Core.validate module = .ok ())
    (functionRow : (lower module).funcs[index]? = some func)
    (known : func.summary = .known summary)
    (blockMember : block ∈ func.blocks.toList) (instMember : inst ∈ block.insts)
    (operand : owner ∈ directTouchOperands inst)
    (member : target ∈ func.storageTargets (targetsOf (rootsAt
      (func.provenance (resultRoots (lower module) (lower module).implTypes)
        ((lower module).implTypes[index]?.getD #[]) (lower module).rootCount).vals owner))) :
    target ∈ func.storageTargets (summaryTouchTargets summary) := by
  apply accepted_instruction_touch_storage_bound accepted functionRow known blockMember instMember
  obtain ⟨source, sourceMember, expanded⟩ := List.mem_flatMap.mp member
  exact List.mem_flatMap.mpr ⟨source, directTouchOperands_effectStep operand sourceMember, expanded⟩

def callMappedTouchTargets (caller callee : Func) (provenance : Prov)
    (args : List ValueId) (targets : List Target) : List Target :=
  let argRoots := args.map fun value =>
    ((rootsAt provenance.vals value).flatMap caller.expandParameterRoot).foldl
      (fun acc root => unionRoots acc [root]) []
  let annotated := targets.flatMap fun
    | .param index =>
      match callee.params[index]? with
      | some type => if type.isRefLike then
          ((callee.roots.params.find? (·.1 == index)).map (·.2)).getD [] |>.filterMap fun
            | .global global => some (.global global)
            | _ => none
        else []
      | none => []
    | .global _ => []
  addTargets (mapSummaryTargets argRoots targets) annotated

theorem callMappedTouchTargets_effectStep {module : GIR.Module} {caller callee : Func}
    {summary : Summary} {vt : Array (Option VTy)} {provenance : Prov}
    {function : FnId} {args : List ValueId} {result : ValueId} {origin : Option OriginId}
    {target : Target}
    (calleeRow : module.funcs[function]? = some callee) (known : callee.summary = .known summary)
    (member : target ∈
      callMappedTouchTargets caller callee provenance args summary.reads ++
      callMappedTouchTargets caller callee provenance args summary.writes ++
      callMappedTouchTargets caller callee provenance args summary.grows ++
      callMappedTouchTargets caller callee provenance args summary.shrinks) :
    target ∈ effectTouchTargets
      (caller.effectStep module vt provenance {} (.def result (.call function args origin))) := by
  simp only [Func.effectStep, calleeRow, known]
  change target ∈ effectTouchTargets {
    reads := addTargets [] (callMappedTouchTargets caller callee provenance args summary.reads)
    writes := addTargets [] (callMappedTouchTargets caller callee provenance args summary.writes)
    grows := addTargets [] (callMappedTouchTargets caller callee provenance args summary.grows)
    shrinks := addTargets [] (callMappedTouchTargets caller callee provenance args summary.shrinks)
    aborts := false || summary.aborts
    outputs := false || summary.outputs }
  simpa [effectTouchTargets, mem_addTargets_iff] using member

theorem accepted_call_touch_storage_bound {module : Core.Module} {index : Nat}
    {caller callee : Func} {summary calleeSummary : Summary} {block : GIR.Block}
    {function : FnId} {args : List ValueId} {result : ValueId} {origin : Option OriginId}
    {target : Target} (accepted : Core.validate module = .ok ())
    (functionRow : (lower module).funcs[index]? = some caller)
    (known : caller.summary = .known summary)
    (blockMember : block ∈ caller.blocks.toList)
    (instMember : Inst.def result (.call function args origin) ∈ block.insts)
    (calleeRow : (lower module).funcs[function]? = some callee)
    (calleeKnown : callee.summary = .known calleeSummary)
    (member : target ∈ caller.storageTargets (
      let provenance := caller.provenance (resultRoots (lower module) (lower module).implTypes)
        ((lower module).implTypes[index]?.getD #[]) (lower module).rootCount
      callMappedTouchTargets caller callee provenance args calleeSummary.reads ++
      callMappedTouchTargets caller callee provenance args calleeSummary.writes ++
      callMappedTouchTargets caller callee provenance args calleeSummary.grows ++
      callMappedTouchTargets caller callee provenance args calleeSummary.shrinks)) :
    target ∈ caller.storageTargets (summaryTouchTargets summary) := by
  apply accepted_instruction_touch_storage_bound accepted functionRow known blockMember instMember
  obtain ⟨source, sourceMember, expanded⟩ := List.mem_flatMap.mp member
  exact List.mem_flatMap.mpr
    ⟨source, callMappedTouchTargets_effectStep calleeRow calleeKnown sourceMember, expanded⟩

open Goose.GIR.ReplacementContentFlow.Model

def summaryTouchPolicy (module : GIR.Module) (func : Func) (atom : Atom) : Prop :=
  match summaryTouchRoots module func with
  | none => True
  | some upper => ∃ actual, ownerDependencies module func (.known [atom]) = some actual ∧
      ∀ root ∈ actual, (∃ slot, root = .local slot) ∨ root ∈ upper

theorem expanded_root_touch_bound {func : Func} {source : List RootRef} {summary : Summary}
    {root : RootRef}
    (bounded : ∀ target ∈ func.storageTargets (rootsTargets source),
      target ∈ func.storageTargets (summaryTouchTargets summary))
    (member : root ∈ source.flatMap func.expandParameterRoot) :
    (∃ slot, root = .local slot) ∨
      root ∈ ((func.storageTargets (summaryTouchTargets summary)).map fun
        | .param index => RootRef.param index
        | .global index => RootRef.global index) := by
  cases root with
  | «local» slot => exact Or.inl ⟨slot, rfl⟩
  | param index =>
    apply Or.inr
    apply List.mem_map.mpr
    refine ⟨Target.param index, bounded _ ?_, rfl⟩
    rw [storageTargets_rootsTargets]
    exact List.mem_filterMap.mpr ⟨.param index, member, rfl⟩
  | global index =>
    apply Or.inr
    apply List.mem_map.mpr
    refine ⟨Target.global index, bounded _ ?_, rfl⟩
    rw [storageTargets_rootsTargets]
    exact List.mem_filterMap.mpr ⟨.global index, member, rfl⟩

theorem symbolicRoots_summaryTouchPolicy {module : GIR.Module} {func : Func}
    {roots : Roots} {source : List RootRef}
    (closed : ParameterRootsClosed func) (refined : SymbolicRootsRefine func roots source)
    (bounded : ∀ summary, func.summary = .known summary →
      ∀ target ∈ func.storageTargets (rootsTargets source),
        target ∈ func.storageTargets (summaryTouchTargets summary)) :
    roots.AtomsWithin (summaryTouchPolicy module func) := by
  cases summaryAt : func.summary with
  | unknown =>
    cases roots with
    | pending => trivial
    | unknown =>
      obtain ⟨actual, known, _⟩ := refined.actual closed (by simp)
      simp [normalize] at known
    | known atoms =>
      intro atom member
      simp [summaryTouchPolicy, summaryTouchRoots, summaryAt]
  | known summary =>
    cases roots with
    | pending => trivial
    | unknown =>
      obtain ⟨actual, known, _⟩ := refined.actual closed (by simp)
      simp [normalize] at known
    | known atoms =>
      obtain ⟨actual, normalized, within⟩ := refined.actual closed (by simp)
      obtain ⟨dependencies, dependenciesAt, dependenciesWithin⟩ := ownerDependencies_known normalized
      have admitted := ownerDependencies_atomsWithin dependenciesAt
      intro atom member
      obtain ⟨single, singleAt, singleWithin⟩ := admitted atom member
      simp only [summaryTouchPolicy, summaryTouchRoots, summaryAt]
      refine ⟨single, singleAt, ?_⟩
      intro root rootMember
      exact expanded_root_touch_bound (bounded summary summaryAt)
        (within (dependenciesWithin (singleWithin rootMember)))

theorem accepted_direct_touch_policy {module : Core.Module} {index : Nat}
    {func : Func} {block : GIR.Block} {inst : Inst} {owner : ValueId} {roots : Roots}
    (accepted : Core.validate module = .ok ())
    (functionRow : (lower module).funcs[index]? = some func)
    (blockMember : block ∈ func.blocks.toList) (instMember : inst ∈ block.insts)
    (operand : owner ∈ directTouchOperands inst)
    (closed : ParameterRootsClosed func)
    (refined : SymbolicRootsRefine func roots (rootsAt
      (func.provenance (resultRoots (lower module) (lower module).implTypes)
        ((lower module).implTypes[index]?.getD #[]) (lower module).rootCount).vals owner)) :
    roots.AtomsWithin (summaryTouchPolicy (lower module) func) := by
  apply symbolicRoots_summaryTouchPolicy closed refined
  intro summary known target member
  exact accepted_direct_touch_storage_bound accepted functionRow known blockMember instMember
    operand member

theorem instruction_unknown_within_effects {module : GIR.Module} {func : Func}
    {provenance : Prov} {block : GIR.Block} {inst : Inst}
    (blockMember : block ∈ func.blocks.toList) (instMember : inst ∈ block.insts)
    (unknown : (func.effectStep module (func.valueTypes module) provenance {} inst).unknown = true) :
    (func.effects module provenance).unknown = true := by
  rw [effects_fold_step]
  let predicate := fun effect : Core.Eff => effect.unknown = true
  have combined (prior : Core.Eff) (instruction : Inst) :=
    (effectStep_join module (func.valueTypes module) func provenance prior instruction).2.2.2.2.2.2.2
  have monotone : ∀ effect instruction, predicate effect →
      predicate (func.effectStep module (func.valueTypes module) provenance effect instruction) := by
    intro effect instruction prior
    change _ = true
    rw [combined]
    simp [predicate] at prior
    simp [prior]
  apply fold_contains _ predicate (fun effect block prior =>
    fold_preserves _ predicate monotone block.insts prior) _ blockMember
  intro effect
  apply fold_contains _ predicate monotone block.insts instMember _ effect
  intro prior
  change _ = true
  rw [combined]
  simp [unknown]

theorem accepted_known_caller_known_callee {module : Core.Module} {index : Nat}
    {caller callee : Func} {summary : Summary} {block : GIR.Block}
    {function : FnId} {args : List ValueId} {result : ValueId} {origin : Option OriginId}
    (accepted : Core.validate module = .ok ())
    (functionRow : (lower module).funcs[index]? = some caller)
    (known : caller.summary = .known summary)
    (blockMember : block ∈ caller.blocks.toList)
    (instMember : Inst.def result (.call function args origin) ∈ block.insts)
    (calleeRow : (lower module).funcs[function]? = some callee) :
    ∃ calleeSummary, callee.summary = .known calleeSummary := by
  cases calleeKnown : callee.summary with
  | known calleeSummary => exact ⟨calleeSummary, rfl⟩
  | unknown =>
    have closed := GIR.within_of_closed (accepted_module_function_summaryClosed accepted functionRow)
    simp only [EffectsWithin, known] at closed
    have found := instruction_unknown_within_effects (module := lower module) (provenance :=
      caller.provenance (resultRoots (lower module) (lower module).implTypes)
        ((lower module).implTypes[index]?.getD #[]) (lower module).rootCount)
      blockMember instMember (by simp [Func.effectStep, calleeRow, calleeKnown])
    rw [closed.1] at found
    contradiction

#print axioms instruction_unknown_within_effects
#print axioms accepted_known_caller_known_callee
#print axioms expanded_root_touch_bound
#print axioms symbolicRoots_summaryTouchPolicy
#print axioms accepted_direct_touch_policy
#print axioms callMappedTouchTargets_effectStep
#print axioms accepted_call_touch_storage_bound
#print axioms directTouchOperands_effectStep
#print axioms accepted_direct_touch_storage_bound
#print axioms instruction_touch_targets_within_effects
#print axioms accepted_instruction_touch_storage_bound

end Goose.Lower.Validation.SummaryPreservation
