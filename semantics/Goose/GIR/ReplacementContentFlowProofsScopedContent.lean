import Goose.GIR.ReplacementContentFlowProofsScopedContentSteps

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem round_scoped_content {module : Module} {states : Array State} {func : Func}
    {types : Array (Option VTy)} {state final : State} {selected slots contents : Nat → Prop} {leaves : List ValueId}
    {predicate : Atom → Prop}
    (before : state.ScopedContentWithin selected slots contents predicate)
    (below : (round module states func types state).Extends final)
    (definitions : ∀ block ∈ func.blocks.toList, ∀ value op, Inst.def value op ∈ block.insts →
      selected value → value ∈ leaves ∨
      (∃ function arguments origin, op = .call function arguments origin) ∨ ∃ source, selected source ∧
        (∀ fn args origin, op ≠ .call fn args origin) ∧
        ∀ current, result func types current value op = flowAt current.values source)
    (incoming : ∀ value, selected value → value ∉ leaves →
      ∀ source ∈ allIncomingValues func value, selected source)
    (calls : ∀ block ∈ func.blocks.toList, ∀ value function arguments origin,
      Inst.def value (.call function arguments origin) ∈ block.insts →
      ∀ current, current.ScopedContentWithin selected slots contents predicate → current.Extends final →
        (selected value → value ∉ leaves → ((callState module states func current function arguments).1).AtomsWithin predicate) ∧
        ((callState module states func current function arguments).2).ScopedMemoryWithin slots contents predicate)
    (initializations : ∀ block ∈ func.blocks.toList, ∀ slot value origin,
      Inst.eff (.slotInit slot value origin) ∈ block.insts → ∀ (current : State),
      current.ScopedContentWithin selected slots contents predicate → current.Extends final →
      slots slot → (flowAt current.values value).AtomsWithin predicate)
    (stores : ∀ block ∈ func.blocks.toList, ∀ address value origin,
      Inst.eff (.store address value origin) ∈ block.insts → ∀ (current : State),
      current.ScopedContentWithin selected slots contents predicate → current.Extends final →
      valRefLike types value = true →
      (write func (touchValues types current [address]) (flowAt current.values address)
        (flowAt current.values value)).ScopedMemoryWithin slots contents predicate)
    (observed : ∀ value ∈ leaves, (flowAt final.values value).AtomsWithin predicate) :
    (round module states func types state).ScopedContentWithin selected slots contents predicate := by
  simp only [round,← Array.foldl_toList] at below ⊢
  apply state_foldl_below func.blocks.toList _
    (fun current block => state_foldl_extends block.insts _ (step_extends module states func types) current)
    (fun current => current.ScopedContentWithin selected slots contents predicate) ?_ state below before
  intro current block blockMember beforeBelow afterBelow valid
  apply state_foldl_below block.insts _ (step_extends module states func types)
    (fun current => current.ScopedContentWithin selected slots contents predicate) ?_ current afterBelow valid
  intro current inst member beforeBelow afterBelow valid
  apply step_scoped_content valid afterBelow definitions incoming
  · intro value function arguments origin same
    subst inst
    exact calls block blockMember value function arguments origin member current valid beforeBelow
  · intro slot value origin same
    subst inst
    exact initializations block blockMember slot value origin member current valid beforeBelow
  · intro address value origin same
    subst inst
    exact stores block blockMember address value origin member current valid beforeBelow
  · exact observed
  · exact blockMember
  · exact member

theorem FunctionReachable.scoped_content {module : Module} {states : Array State} {func : Func}
    {types : Array (Option VTy)} {current final : State} {selected slots contents : Nat → Prop} {leaves : List ValueId}
    {predicate : Atom → Prop}
    (reachable : FunctionReachable module states func types (start func types) current)
    (suffix : FunctionReachable module states func types current final)
    (initial : (start func types).ScopedMemoryWithin slots contents predicate)
    (bounded : ∀ value, selected value → value < func.numValues)
    (separate : ∀ entry, func.blocks[0]? = some entry →
      ∀ value, selected value → value ∉ leaves → value ∉ entry.params.map Prod.fst)
    (definitions : ∀ block ∈ func.blocks.toList, ∀ value op, Inst.def value op ∈ block.insts →
      selected value → value ∈ leaves ∨
      (∃ function arguments origin, op = .call function arguments origin) ∨ ∃ source, selected source ∧
        (∀ fn args origin, op ≠ .call fn args origin) ∧
        ∀ state, result func types state value op = flowAt state.values source)
    (incoming : ∀ value, selected value → value ∉ leaves →
      ∀ source ∈ allIncomingValues func value, selected source)
    (calls : ∀ block ∈ func.blocks.toList, ∀ value function arguments origin,
      Inst.def value (.call function arguments origin) ∈ block.insts →
      ∀ current, current.ScopedContentWithin selected slots contents predicate → current.Extends final →
        (selected value → value ∉ leaves → ((callState module states func current function arguments).1).AtomsWithin predicate) ∧
        ((callState module states func current function arguments).2).ScopedMemoryWithin slots contents predicate)
    (initializations : ∀ block ∈ func.blocks.toList, ∀ slot value origin,
      Inst.eff (.slotInit slot value origin) ∈ block.insts → ∀ (current : State),
      current.ScopedContentWithin selected slots contents predicate → current.Extends final →
      slots slot → (flowAt current.values value).AtomsWithin predicate)
    (stores : ∀ block ∈ func.blocks.toList, ∀ address value origin,
      Inst.eff (.store address value origin) ∈ block.insts → ∀ (current : State),
      current.ScopedContentWithin selected slots contents predicate → current.Extends final →
      valRefLike types value = true →
      (write func (touchValues types current [address]) (flowAt current.values address)
        (flowAt current.values value)).ScopedMemoryWithin slots contents predicate)
    (observed : ∀ value ∈ leaves, (flowAt final.values value).AtomsWithin predicate) :
    current.ScopedContentWithin selected slots contents predicate := by
  induction reachable with
  | refl =>
      refine ⟨?_, initial⟩
      intro value chosen
      by_cases leaf : value ∈ leaves
      · exact (suffix.extends.values.values value).atomsWithin (observed value leaf)
      · rw [start_entry_separate_pending (bounded value chosen)
          (fun entry row => separate entry row value chosen leaf)]
        trivial
  | @next current reachable ih =>
      have earlier := ih ((FunctionReachable.next (.refl current)).trans suffix)
      exact round_scoped_content earlier suffix.extends definitions incoming calls initializations stores observed

#print axioms FunctionReachable.scoped_content

end Goose.GIR.ReplacementContentFlow.Model
