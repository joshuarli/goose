import Goose.GIR.ReplacementContentFlowProofsSliceDefinitions

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem start_nonparameter_pending {func : Func} {types : Array (Option VTy)} {value : ValueId}
    (bounded : value < func.numValues)
    (separate : ∀ block ∈ func.blocks.toList, value ∉ block.params.map Prod.fst) :
    flowAt (start func types).values value = .pending := by
  cases entryAt : func.blocks[0]? with
  | none => simp [start,entryAt,flowAt,bounded]
  | some entry =>
      rw [start_values_fold types entryAt]
      have notParameter := separate entry (List.mem_of_getElem? (by simpa using entryAt))
      change ((entry.params.zipIdx.foldl _ (Array.replicate func.numValues Roots.pending))[value]?.getD .unknown) = .pending
      rw [array_foldl_set_unchanged]
      · simp [bounded]
      · intro pair member same
        have parameter : pair.1 ∈ entry.params := (List.mem_zipIdx_iff_getElem?.mp member) |> List.mem_of_getElem?
        exact notParameter (List.mem_map.mpr ⟨pair.1,parameter,same⟩)

theorem edge_nonparameter_value {func : Func} {state : State} {value : ValueId}
    (separate : ∀ block ∈ func.blocks.toList, value ∉ block.params.map Prod.fst)
    (target : BlockId) (args : List ValueId) :
    flowAt (edge func state target args).values value = flowAt state.values value := by
  cases targetAt : func.blocks[target]? with
  | none => simp [edge,targetAt]
  | some block =>
      simp only [edge,targetAt]
      have notParameter := separate block (List.mem_of_getElem? (by simpa using targetAt))
      have preserved : ∀ current : State,
          flowAt ((block.params.zip args).foldl (fun state pair =>
            { state with values := addFlow state.values pair.1.1 (flowAt state.values pair.2) }) current).values value =
            flowAt current.values value := by
        intro current
        apply List.foldlRecOn (motive := fun after : State => flowAt after.values value = flowAt current.values value)
          (block.params.zip args) _ rfl
        intro after valid pair member
        have parameter := (List.of_mem_zip member).1
        have different : value ≠ pair.1.1 := by
          intro same
          exact notParameter (List.mem_map.mpr ⟨pair.1,parameter,same.symm⟩)
        simpa only [flowAt_addFlow,different,false_and,ite_false] using valid
      exact preserved state

theorem step_unique_call_value {module : Module} {states : Array State} {func : Func}
    {types : Array (Option VTy)} {state final effects : State}
    {value fn : ValueId} {args : List ValueId} {origin : Option OriginId} {callee : Func}
    {block targetBlock : Block} {inst : Inst} {predicate : Atom → Prop}
    (unique : (func.blocks.toList.flatMap Block.defs).Nodup)
    (targetMember : targetBlock ∈ func.blocks.toList) (called : Inst.def value (.call fn args origin) ∈ targetBlock.insts)
    (calleeAt : module.funcs[fn]? = some callee) (effectsAt : states[fn]? = some effects)
    (before : (flowAt state.values value).AtomsWithin predicate)
    (growth : state.Extends final)
    (produced : ∀ current : State, current.Extends final →
      (substitute func current args effects.returned).AtomsWithin predicate)
    (blockMember : block ∈ func.blocks.toList) (member : inst ∈ block.insts) :
    (flowAt (step module states func types state inst).values value).AtomsWithin predicate := by
  have separate := unique_definition_not_parameter unique targetMember called
  cases inst with
  | «def» defined op =>
      rw [step_def_values,flowAt_addFlow]
      by_cases same : value = defined
      · subst defined
        have opEqual := unique_definition_op unique targetMember called blockMember member
        subst op
        split
        · apply before.join
          dsimp only
          split
          · rw [callState_result _ _ _ _ _ _ _ _ calleeAt effectsAt,substitute_touchValues]
            exact produced state growth
          · simp [Roots.AtomsWithin]
        · exact before
      · simp only [same,false_and,ite_false]
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

#print axioms start_nonparameter_pending
#print axioms step_unique_call_value

end Goose.GIR.ReplacementContentFlow.Model
