import Goose.GIR.ReplacementContentFlowProofsScopedContentMemory

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem step_scoped_content_values {module : Module} {states : Array State} {func : Func}
    {types : Array (Option VTy)} {state final : State} {selected : ValueId → Prop} {leaves : List ValueId}
    {block : Block} {inst : Inst} {predicate : Atom → Prop}
    (before : state.ScopedValuesWithin selected predicate)
    (below : (step module states func types state inst).Extends final)
    (definitions : ∀ block ∈ func.blocks.toList, ∀ value op, Inst.def value op ∈ block.insts →
      selected value → value ∈ leaves ∨
      (∃ function arguments origin, op = .call function arguments origin) ∨ ∃ source, selected source ∧
        (∀ fn args origin, op ≠ .call fn args origin) ∧
        ∀ current, result func types current value op = flowAt current.values source)
    (incoming : ∀ value, selected value → value ∉ leaves →
      ∀ source ∈ allIncomingValues func value, selected source)
    (calls : ∀ value function arguments origin,
      inst = Inst.def value (.call function arguments origin) → selected value → value ∉ leaves →
      ((callState module states func state function arguments).1).AtomsWithin predicate)
    (observed : ∀ value ∈ leaves, (flowAt final.values value).AtomsWithin predicate)
    (blockMember : block ∈ func.blocks.toList) (member : inst ∈ block.insts) :
    (step module states func types state inst).ScopedValuesWithin selected predicate := by
  cases inst with
  | «def» defined op =>
      intro value chosen
      by_cases same : value = defined
      · subst defined
        by_cases leaf : value ∈ leaves
        · exact (below.values.values value).atomsWithin (observed value leaf)
        rcases definitions block blockMember value op member chosen with leaf | call | forward
        · exact (below.values.values value).atomsWithin (observed value leaf)
        · obtain ⟨function, arguments, origin, same⟩ := call
          subst op
          have produced := calls value function arguments origin rfl chosen leaf
          simp only [step_def_values]
          rw [flowAt_addFlow]
          split
          · apply (before value chosen).join
            split
            · rw [callState_result_touchValues]
              exact produced
            · simp [Roots.AtomsWithin]
          · exact before value chosen
        · obtain ⟨source,sourceChosen,ordinary,forward⟩ := forward
          rw [step_noncall_values ordinary,flowAt_addFlow]
          split
          · rw [forward state]
            exact (before value chosen).join (before source sourceChosen)
          · exact before value chosen
      · rw [step_def_values,flowAt_addFlow]
        simpa only [same,false_and,ite_false] using before value chosen
  | eff effect =>
      cases effect <;> try exact before
      case store address source origin =>
        simp only [step,Id.run_pure]
        split
        · simpa only [State.ScopedValuesWithin,write_values,touchValues_values] using before
        · exact before
  | term term =>
      cases term with
      | br target args =>
          simp only [step,Id.run_pure] at below ⊢
          exact edge_scoped_values (by simpa only [State.ScopedValuesWithin,touchValues_values] using before) below
            (fun value chosen notLeaf source input => incoming value chosen notLeaf source
              (allIncomingValues_mem blockMember member (by simp [termEdges]) input)) observed
      | condbr condition left leftArgs right rightArgs =>
          simp only [step,Id.run_pure] at below ⊢
          have first := edge_scoped_values (target := left) (args := leftArgs)
            (by simpa only [State.ScopedValuesWithin,touchValues_values] using before)
            ((edge_extends func _ right rightArgs).trans below)
            (fun value chosen notLeaf source input => incoming value chosen notLeaf source
              (allIncomingValues_mem blockMember member (by simp [termEdges]) input)) observed
          exact edge_scoped_values first below
            (fun value chosen notLeaf source input => incoming value chosen notLeaf source
              (allIncomingValues_mem blockMember member (by simp [termEdges]) input)) observed
      | ret values origin =>
          cases values with
          | nil => exact before
          | cons first rest => cases rest <;> exact before
      | _ => exact before

theorem step_scoped_content_memory {module : Module} {states : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {slots contents : Nat → Prop}
    {inst : Inst} {predicate : Atom → Prop}
    (before : state.ScopedMemoryWithin slots contents predicate)
    (calls : ∀ value function arguments origin,
      inst = Inst.def value (.call function arguments origin) →
      ((callState module states func state function arguments).2).ScopedMemoryWithin slots contents predicate)
    (initializations : ∀ slot value origin, inst = .eff (.slotInit slot value origin) →
      slots slot → (flowAt state.values value).AtomsWithin predicate)
    (stores : ∀ address value origin, inst = .eff (.store address value origin) →
      valRefLike types value = true →
      (write func (touchValues types state [address]) (flowAt state.values address)
        (flowAt state.values value)).ScopedMemoryWithin
        slots contents predicate) :
    (step module states func types state inst).ScopedMemoryWithin slots contents predicate := by
  cases inst with
  | «def» value op =>
    cases op with
    | call function arguments origin =>
      have bounded := calls value function arguments origin rfl
      exact ⟨bounded.slots, bounded.contents⟩
    | _ => exact ⟨before.slots, before.contents⟩
  | eff effect =>
    cases effect with
    | slotInit slot value origin =>
      have bounded := before.addSlot (initializations slot value origin rfl)
      exact ⟨bounded.slots, bounded.contents⟩
    | store address value origin =>
      simp only [step, Id.run_pure]
      split
      · rename_i reference
        have bounded := stores address value origin rfl reference
        simpa only [accessOperands, touchValues_values] using bounded
      · exact ⟨before.slots, before.contents⟩
    | _ => exact ⟨before.slots, before.contents⟩
  | term terminator =>
    cases terminator with
    | br target arguments =>
      exact (before.touchValues).edge
    | condbr condition left leftArgs right rightArgs =>
      exact ((before.touchValues).edge).edge
    | ret values origin =>
      cases values with
      | nil => exact ⟨before.slots, before.contents⟩
      | cons value rest => cases rest <;> exact ⟨before.slots, before.contents⟩
    | _ => exact ⟨before.slots, before.contents⟩

theorem step_scoped_content {module : Module} {states : Array State} {func : Func}
    {types : Array (Option VTy)} {state final : State} {selected slots contents : Nat → Prop}
    {leaves : List ValueId} {block : Block} {inst : Inst} {predicate : Atom → Prop}
    (before : state.ScopedContentWithin selected slots contents predicate)
    (below : (step module states func types state inst).Extends final)
    (definitions : ∀ block ∈ func.blocks.toList, ∀ value op, Inst.def value op ∈ block.insts →
      selected value → value ∈ leaves ∨
      (∃ function arguments origin, op = .call function arguments origin) ∨ ∃ source, selected source ∧
        (∀ fn args origin, op ≠ .call fn args origin) ∧
        ∀ current, result func types current value op = flowAt current.values source)
    (incoming : ∀ value, selected value → value ∉ leaves →
      ∀ source ∈ allIncomingValues func value, selected source)
    (calls : ∀ value function arguments origin,
      inst = Inst.def value (.call function arguments origin) →
      (selected value → value ∉ leaves → ((callState module states func state function arguments).1).AtomsWithin predicate) ∧
      ((callState module states func state function arguments).2).ScopedMemoryWithin slots contents predicate)
    (initializations : ∀ slot value origin, inst = .eff (.slotInit slot value origin) →
      slots slot → (flowAt state.values value).AtomsWithin predicate)
    (stores : ∀ address value origin, inst = .eff (.store address value origin) →
      valRefLike types value = true →
      (write func (touchValues types state [address]) (flowAt state.values address)
        (flowAt state.values value)).ScopedMemoryWithin
        slots contents predicate)
    (observed : ∀ value ∈ leaves, (flowAt final.values value).AtomsWithin predicate)
    (blockMember : block ∈ func.blocks.toList) (member : inst ∈ block.insts) :
    (step module states func types state inst).ScopedContentWithin selected slots contents predicate := by
  constructor
  · exact step_scoped_content_values before.values below definitions incoming
      (fun value function arguments origin same => (calls value function arguments origin same).1)
      observed blockMember member
  · exact step_scoped_content_memory before.memory
      (fun value function arguments origin same => (calls value function arguments origin same).2)
      initializations stores

#print axioms step_scoped_content_memory
#print axioms step_scoped_content

end Goose.GIR.ReplacementContentFlow.Model
