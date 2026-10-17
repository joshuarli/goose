import Goose.GIR.ReplacementContentFlowProofsForwarding
import Goose.GIR.ReplacementContentFlowProofsSteps

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem round_unique_call_value {module : Module} {states : Array State} {func : Func}
    {types : Array (Option VTy)} {state final effects : State} {calleeFunc : Func} {value callee : ValueId} {args : List ValueId} {origin : Option OriginId}
    {targetBlock : Block} {predicate : Atom → Prop}
    (unique : (func.blocks.toList.flatMap Block.defs).Nodup)
    (targetMember : targetBlock ∈ func.blocks.toList) (defined : Inst.def value (.call callee args origin) ∈ targetBlock.insts)
    (calleeAt : module.funcs[callee]? = some calleeFunc)
    (effectsAt : states[callee]? = some effects)
    (before : (flowAt state.values value).AtomsWithin predicate)
    (below : (round module states func types state).Extends final)
    (input : ∀ before : State, before.Extends final →
      (substitute func before args effects.returned).AtomsWithin predicate) :
    (flowAt (round module states func types state).values value).AtomsWithin predicate := by
  simp only [round,← Array.foldl_toList] at below ⊢
  apply state_foldl_below func.blocks.toList _
    (fun current block => state_foldl_extends block.insts _ (step_extends module states func types) current)
    (fun current => (flowAt current.values value).AtomsWithin predicate) ?_ state below before
  intro current block blockMember beforeBelow afterBelow valid
  apply state_foldl_below block.insts _ (step_extends module states func types)
    (fun current => (flowAt current.values value).AtomsWithin predicate) ?_ current afterBelow valid
  intro current inst member beforeBelow afterBelow valid
  exact step_unique_call_value unique targetMember defined calleeAt effectsAt valid beforeBelow input blockMember member

theorem FunctionReachable.call_value {module : Module} {states : Array State} {func : Func}
    {types : Array (Option VTy)} {current final effects : State} {calleeFunc : Func} {value callee : ValueId} {args : List ValueId} {origin : Option OriginId}
    {targetBlock : Block} {predicate : Atom → Prop}
    (reachable : FunctionReachable module states func types (start func types) current)
    (suffix : FunctionReachable module states func types current final)
    (unique : (func.blocks.toList.flatMap Block.defs).Nodup) (bounded : value < func.numValues)
    (targetMember : targetBlock ∈ func.blocks.toList) (defined : Inst.def value (.call callee args origin) ∈ targetBlock.insts)
    (calleeAt : module.funcs[callee]? = some calleeFunc)
    (effectsAt : states[callee]? = some effects)
    (input : ∀ before : State, before.Extends final →
      (substitute func before args effects.returned).AtomsWithin predicate) :
    (flowAt current.values value).AtomsWithin predicate := by
  induction reachable with
  | refl =>
      rw [start_nonparameter_pending bounded (unique_definition_not_parameter unique targetMember defined)]
      trivial
  | @next current reachable ih =>
      have earlier := ih ((FunctionReachable.next (.refl current)).trans suffix)
      exact round_unique_call_value unique targetMember defined calleeAt effectsAt earlier suffix.extends input

#print axioms FunctionReachable.call_value

end Goose.GIR.ReplacementContentFlow.Model
