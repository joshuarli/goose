import Goose.GIR.ReplacementContentFlowProofsIncomingValues
import Goose.GIR.ReplacementContentFlowProofsForwarding

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem edgeIncomingValues_mem {func : Func} {value target : Nat} {args : List ValueId}
    {block : Block} {pair : (ValueId × VTy) × ValueId}
    (targetAt : func.blocks[target]? = some block) (member : pair ∈ block.params.zip args)
    (same : pair.1.1 = value) : pair.2 ∈ edgeIncomingValues func value target args := by
  simp only [edgeIncomingValues,targetAt]
  apply List.mem_filterMap.mpr
  exact ⟨pair,member,by simp [same]⟩

theorem allIncomingValues_mem {func : Func} {value : ValueId} {block : Block} {term : Term}
    {target : BlockId} {args : List ValueId} {source : ValueId}
    (blockMember : block ∈ func.blocks.toList) (member : Inst.term term ∈ block.insts)
    (edgeMember : (target,args) ∈ termEdges term)
    (input : source ∈ edgeIncomingValues func value target args) : source ∈ allIncomingValues func value := by
  exact List.mem_flatMap.mpr ⟨block,blockMember,List.mem_flatMap.mpr
    ⟨.term term,member,List.mem_flatMap.mpr ⟨(target,args),edgeMember,input⟩⟩⟩

theorem unique_parameter_not_definition {func : Func} {targetBlock block : Block}
    {value target : ValueId} {op : Op}
    (unique : (func.blocks.toList.flatMap Block.defs).Nodup)
    (targetMember : targetBlock ∈ func.blocks.toList) (parameter : value ∈ targetBlock.params.map Prod.fst)
    (blockMember : block ∈ func.blocks.toList) (defined : Inst.def target op ∈ block.insts) : value ≠ target := by
  intro same
  subst target
  rw [← definitionEntries_ids_func] at unique
  have equal := entry_eq_of_nodup_ids unique
    (parameterEntry_mem (by simpa using targetMember) parameter)
    (definitionEntry_mem (by simpa using blockMember) defined) rfl
  cases equal

theorem nonentry_parameter_not_entry {func : Func} {target value : Nat} {block entry : Block}
    (unique : (func.blocks.toList.flatMap Block.defs).Nodup)
    (targetAt : func.blocks[target]? = some block) (parameter : value ∈ block.params.map Prod.fst)
    (nonentry : target ≠ 0) (entryAt : func.blocks[0]? = some entry) :
    value ∉ entry.params.map Prod.fst := by
  intro entryParameter
  rw [← definitionLocations_ids_func] at unique
  have equal := entry_eq_of_nodup_ids unique
    (parameterLocation_mem targetAt parameter) (parameterLocation_mem entryAt entryParameter) rfl
  exact nonentry (congrArg (fun pair => pair.2.1) equal)

theorem start_nonentry_parameter_pending {func : Func} {types : Array (Option VTy)}
    {target value : Nat} {block : Block}
    (unique : (func.blocks.toList.flatMap Block.defs).Nodup) (bounded : value < func.numValues)
    (targetAt : func.blocks[target]? = some block) (parameter : value ∈ block.params.map Prod.fst)
    (nonentry : target ≠ 0) : flowAt (start func types).values value = .pending := by
  cases entryAt : func.blocks[0]? with
  | none => simp [start,entryAt,flowAt,bounded]
  | some entry =>
      rw [start_values_fold types entryAt]
      have notParameter := nonentry_parameter_not_entry unique targetAt parameter nonentry entryAt
      change ((entry.params.zipIdx.foldl _ (Array.replicate func.numValues Roots.pending))[value]?.getD .unknown) = .pending
      rw [array_foldl_set_unchanged]
      · simp [bounded]
      · intro pair member same
        have actual : pair.1 ∈ entry.params := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp member)
        exact notParameter (List.mem_map.mpr ⟨pair.1,actual,same⟩)

theorem edge_phi_value {func : Func} {state final : State} {value : ValueId}
    {predicate : Atom → Prop} {target : BlockId} {args : List ValueId}
    (before : (flowAt state.values value).AtomsWithin predicate)
    (below : (edge func state target args).Extends final)
    (inputs : ∀ source ∈ edgeIncomingValues func value target args,
      (flowAt final.values source).AtomsWithin predicate) :
    (flowAt (edge func state target args).values value).AtomsWithin predicate := by
  cases targetAt : func.blocks[target]? with
  | none => simpa [edge,targetAt] using before
  | some block =>
      simp only [edge,targetAt] at below ⊢
      apply state_foldl_below (block.params.zip args) _
        (fun current pair => current.extends_values _ _)
        (fun current => (flowAt current.values value).AtomsWithin predicate) ?_ state below before
      intro current pair member beforeBelow afterBelow valid
      rw [flowAt_addFlow]
      split
      · rename_i same
        simpa only [same.1,flowAt] using valid.join ((beforeBelow.values.values pair.2).atomsWithin
          (inputs pair.2 (edgeIncomingValues_mem targetAt member same.1.symm)))
      · exact valid

theorem step_phi_value {module : Module} {states : Array State} {func : Func}
    {types : Array (Option VTy)} {state final : State} {value : ValueId}
    {block targetBlock : Block} {inst : Inst} {predicate : Atom → Prop}
    (unique : (func.blocks.toList.flatMap Block.defs).Nodup)
    (targetMember : targetBlock ∈ func.blocks.toList) (parameter : value ∈ targetBlock.params.map Prod.fst)
    (before : (flowAt state.values value).AtomsWithin predicate)
    (below : (step module states func types state inst).Extends final)
    (inputs : ∀ source ∈ allIncomingValues func value, (flowAt final.values source).AtomsWithin predicate)
    (blockMember : block ∈ func.blocks.toList) (member : inst ∈ block.insts) :
    (flowAt (step module states func types state inst).values value).AtomsWithin predicate := by
  cases inst with
  | «def» defined op =>
      have different := unique_parameter_not_definition unique targetMember parameter blockMember member
      rw [step_def_values,flowAt_addFlow]
      simp only [different,false_and,ite_false]
      exact before
  | eff effect =>
      cases effect <;> try exact before
      case store address source origin =>
        simp only [step,Id.run_pure]
        split
        · rw [write_values,touchValues_values]
          exact before
        · exact before
  | term term =>
      cases term with
      | br target args =>
          simp only [step,Id.run_pure] at below ⊢
          apply edge_phi_value (by simpa only [touchValues_values] using before) below
          intro source input
          exact inputs source (allIncomingValues_mem blockMember member (by simp [termEdges]) input)
      | condbr condition left leftArgs right rightArgs =>
          simp only [step,Id.run_pure] at below ⊢
          have first := edge_phi_value (value := value) (predicate := predicate)
            (by simpa only [touchValues_values] using before)
            ((edge_extends func _ right rightArgs).trans below)
            (fun source input => inputs source (allIncomingValues_mem blockMember member (by simp [termEdges]) input))
          exact edge_phi_value first below
            (fun source input => inputs source (allIncomingValues_mem blockMember member (by simp [termEdges]) input))
      | ret values origin =>
          cases values with
          | nil => exact before
          | cons first rest => cases rest <;> exact before
      | _ => exact before

theorem round_phi_value {module : Module} {states : Array State} {func : Func}
    {types : Array (Option VTy)} {state final : State} {value : ValueId}
    {targetBlock : Block} {predicate : Atom → Prop}
    (unique : (func.blocks.toList.flatMap Block.defs).Nodup)
    (targetMember : targetBlock ∈ func.blocks.toList) (parameter : value ∈ targetBlock.params.map Prod.fst)
    (before : (flowAt state.values value).AtomsWithin predicate)
    (below : (round module states func types state).Extends final)
    (inputs : ∀ source ∈ allIncomingValues func value, (flowAt final.values source).AtomsWithin predicate) :
    (flowAt (round module states func types state).values value).AtomsWithin predicate := by
  simp only [round,← Array.foldl_toList] at below ⊢
  apply state_foldl_below func.blocks.toList _
    (fun current block => state_foldl_extends block.insts _ (step_extends module states func types) current)
    (fun current => (flowAt current.values value).AtomsWithin predicate) ?_ state below before
  intro current block blockMember beforeBelow afterBelow valid
  apply state_foldl_below block.insts _ (step_extends module states func types)
    (fun current => (flowAt current.values value).AtomsWithin predicate) ?_ current afterBelow valid
  intro current inst member beforeBelow afterBelow valid
  exact step_phi_value unique targetMember parameter valid afterBelow inputs blockMember member

theorem FunctionReachable.phi_value {module : Module} {states : Array State} {func : Func}
    {types : Array (Option VTy)} {current final : State} {target value : Nat}
    {targetBlock : Block} {predicate : Atom → Prop}
    (reachable : FunctionReachable module states func types (start func types) current)
    (suffix : FunctionReachable module states func types current final)
    (unique : (func.blocks.toList.flatMap Block.defs).Nodup) (bounded : value < func.numValues)
    (targetAt : func.blocks[target]? = some targetBlock)
    (parameter : value ∈ targetBlock.params.map Prod.fst) (nonentry : target ≠ 0)
    (inputs : ∀ source ∈ allIncomingValues func value, (flowAt final.values source).AtomsWithin predicate) :
    (flowAt current.values value).AtomsWithin predicate := by
  induction reachable with
  | refl =>
      rw [start_nonentry_parameter_pending unique bounded targetAt parameter nonentry]
      trivial
  | @next current reachable ih =>
      have earlier := ih ((FunctionReachable.next (.refl current)).trans suffix)
      exact round_phi_value unique (List.mem_of_getElem? (by simpa using targetAt)) parameter earlier suffix.extends inputs

end Goose.GIR.ReplacementContentFlow.Model
