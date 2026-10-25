import Goose.GIR.ReplacementContentFlowProofsSliceDefinitionOrigins

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem step_unique_forward_value {module : Module} {states : Array State} {func : Func}
    {types : Array (Option VTy)} {state final : State} {value source : ValueId} {op : Op}
    {block targetBlock : Block} {inst : Inst} {predicate : Atom → Prop}
    (unique : (func.blocks.toList.flatMap Block.defs).Nodup)
    (targetMember : targetBlock ∈ func.blocks.toList) (defined : Inst.def value op ∈ targetBlock.insts)
    (ordinary : ∀ fn args origin, op ≠ .call fn args origin)
    (forward : ∀ current, result func types current value op = flowAt current.values source)
    (before : (flowAt state.values value).AtomsWithin predicate)
    (growth : state.Extends final) (input : (flowAt final.values source).AtomsWithin predicate)
    (blockMember : block ∈ func.blocks.toList) (member : inst ∈ block.insts) :
    (flowAt (step module states func types state inst).values value).AtomsWithin predicate := by
  have separate := unique_definition_not_parameter unique targetMember defined
  cases inst with
  | «def» target actual =>
      by_cases same : value = target
      · subst target
        have opEqual := unique_definition_op unique targetMember defined blockMember member
        subst actual
        rw [step_noncall_values ordinary,flowAt_addFlow]
        split
        · rw [forward state]
          exact before.join ((growth.values.values source).atomsWithin input)
        · exact before
      · rw [step_def_values,flowAt_addFlow]
        simp only [same,false_and,ite_false]
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
      | br target args => simpa only [step,Id.run_pure,edge_nonparameter_value separate,touchValues_values] using before
      | condbr condition left leftArgs right rightArgs =>
          simpa only [step,Id.run_pure,edge_nonparameter_value separate,touchValues_values] using before
      | ret values origin =>
          cases values with
          | nil => exact before
          | cons first rest => cases rest <;> exact before
      | _ => exact before

theorem round_unique_forward_value {module : Module} {states : Array State} {func : Func}
    {types : Array (Option VTy)} {state final : State} {value source : ValueId} {op : Op}
    {targetBlock : Block} {predicate : Atom → Prop}
    (unique : (func.blocks.toList.flatMap Block.defs).Nodup)
    (targetMember : targetBlock ∈ func.blocks.toList) (defined : Inst.def value op ∈ targetBlock.insts)
    (ordinary : ∀ fn args origin, op ≠ .call fn args origin)
    (forward : ∀ current, result func types current value op = flowAt current.values source)
    (before : (flowAt state.values value).AtomsWithin predicate)
    (below : (round module states func types state).Extends final)
    (input : (flowAt final.values source).AtomsWithin predicate) :
    (flowAt (round module states func types state).values value).AtomsWithin predicate := by
  simp only [round,← Array.foldl_toList] at below ⊢
  apply state_foldl_below func.blocks.toList _
    (fun current block => state_foldl_extends block.insts _ (step_extends module states func types) current)
    (fun current => (flowAt current.values value).AtomsWithin predicate) ?_ state below before
  intro current block blockMember beforeBelow afterBelow valid
  apply state_foldl_below block.insts _ (step_extends module states func types)
    (fun current => (flowAt current.values value).AtomsWithin predicate) ?_ current afterBelow valid
  intro current inst member beforeBelow afterBelow valid
  exact step_unique_forward_value unique targetMember defined ordinary forward valid beforeBelow input blockMember member

theorem FunctionReachable.forward_value {module : Module} {states : Array State} {func : Func}
    {types : Array (Option VTy)} {current final : State} {value source : ValueId} {op : Op}
    {targetBlock : Block} {predicate : Atom → Prop}
    (reachable : FunctionReachable module states func types (start func types) current)
    (suffix : FunctionReachable module states func types current final)
    (unique : (func.blocks.toList.flatMap Block.defs).Nodup) (bounded : value < func.numValues)
    (targetMember : targetBlock ∈ func.blocks.toList) (defined : Inst.def value op ∈ targetBlock.insts)
    (ordinary : ∀ fn args origin, op ≠ .call fn args origin)
    (forward : ∀ state, result func types state value op = flowAt state.values source)
    (input : (flowAt final.values source).AtomsWithin predicate) :
    (flowAt current.values value).AtomsWithin predicate := by
  induction reachable with
  | refl =>
      rw [start_nonparameter_pending bounded (unique_definition_not_parameter unique targetMember defined)]
      trivial
  | @next current reachable ih =>
      have earlier := ih ((FunctionReachable.next (.refl current)).trans suffix)
      exact round_unique_forward_value unique targetMember defined ordinary forward earlier suffix.extends input

#print axioms FunctionReachable.forward_value

end Goose.GIR.ReplacementContentFlow.Model
