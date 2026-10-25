import Goose.GIR.ReplacementContentFlowProofsPhi

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

def State.ScopedValuesWithin (state : State) (selected : ValueId → Prop) (predicate : Atom → Prop) : Prop :=
  ∀ value, selected value → (flowAt state.values value).AtomsWithin predicate

theorem start_entry_separate_pending {func : Func} {types : Array (Option VTy)} {value : ValueId}
    (bounded : value < func.numValues)
    (separate : ∀ entry, func.blocks[0]? = some entry → value ∉ entry.params.map Prod.fst) :
    flowAt (start func types).values value = .pending := by
  cases entryAt : func.blocks[0]? with
  | none => simp [start,entryAt,flowAt,bounded]
  | some entry =>
      rw [start_values_fold types entryAt]
      change ((entry.params.zipIdx.foldl _ (Array.replicate func.numValues Roots.pending))[value]?.getD .unknown) = .pending
      rw [array_foldl_set_unchanged]
      · simp [bounded]
      · intro pair member same
        have actual : pair.1 ∈ entry.params := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp member)
        exact separate entry entryAt (List.mem_map.mpr ⟨pair.1,actual,same⟩)

theorem edge_scoped_values {func : Func} {state final : State} {selected : ValueId → Prop}
    {predicate : Atom → Prop} {target : BlockId} {args : List ValueId} {leaves : List ValueId}
    (before : state.ScopedValuesWithin selected predicate)
    (below : (edge func state target args).Extends final)
    (closed : ∀ value, selected value → value ∉ leaves →
      ∀ source ∈ edgeIncomingValues func value target args, selected source)
    (observed : ∀ value ∈ leaves, (flowAt final.values value).AtomsWithin predicate) :
    (edge func state target args).ScopedValuesWithin selected predicate := by
  cases targetAt : func.blocks[target]? with
  | none => simpa only [edge,targetAt,State.ScopedValuesWithin] using before
  | some block =>
      simp only [edge,targetAt] at below ⊢
      apply state_foldl_below (block.params.zip args) _
        (fun current pair => current.extends_values _ _)
        (fun current => current.ScopedValuesWithin selected predicate) ?_ state below before
      intro current pair member beforeBelow afterBelow valid value chosen
      by_cases leaf : value ∈ leaves
      · exact (afterBelow.values.values value).atomsWithin (observed value leaf)
      · rw [flowAt_addFlow]
        split
        · rename_i same
          have sourceChosen := closed value chosen leaf pair.2
            (edgeIncomingValues_mem targetAt member same.1.symm)
          simpa only [same.1,flowAt] using (valid value chosen).join (valid pair.2 sourceChosen)
        · exact valid value chosen

theorem step_scoped_values {module : Module} {states : Array State} {func : Func}
    {types : Array (Option VTy)} {state final : State} {selected : ValueId → Prop} {leaves : List ValueId}
    {block : Block} {inst : Inst} {predicate : Atom → Prop}
    (before : state.ScopedValuesWithin selected predicate)
    (below : (step module states func types state inst).Extends final)
    (definitions : ∀ block ∈ func.blocks.toList, ∀ value op, Inst.def value op ∈ block.insts →
      selected value → value ∈ leaves ∨ ∃ source, selected source ∧
        (∀ fn args origin, op ≠ .call fn args origin) ∧
        ∀ current, result func types current value op = flowAt current.values source)
    (incoming : ∀ value, selected value → value ∉ leaves →
      ∀ source ∈ allIncomingValues func value, selected source)
    (observed : ∀ value ∈ leaves, (flowAt final.values value).AtomsWithin predicate)
    (blockMember : block ∈ func.blocks.toList) (member : inst ∈ block.insts) :
    (step module states func types state inst).ScopedValuesWithin selected predicate := by
  cases inst with
  | «def» defined op =>
      intro value chosen
      by_cases same : value = defined
      · subst defined
        rcases definitions block blockMember value op member chosen with leaf | forward
        · exact (below.values.values value).atomsWithin (observed value leaf)
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

theorem round_scoped_values {module : Module} {states : Array State} {func : Func}
    {types : Array (Option VTy)} {state final : State} {selected : ValueId → Prop} {leaves : List ValueId}
    {predicate : Atom → Prop}
    (before : state.ScopedValuesWithin selected predicate)
    (below : (round module states func types state).Extends final)
    (definitions : ∀ block ∈ func.blocks.toList, ∀ value op, Inst.def value op ∈ block.insts →
      selected value → value ∈ leaves ∨ ∃ source, selected source ∧
        (∀ fn args origin, op ≠ .call fn args origin) ∧
        ∀ current, result func types current value op = flowAt current.values source)
    (incoming : ∀ value, selected value → value ∉ leaves →
      ∀ source ∈ allIncomingValues func value, selected source)
    (observed : ∀ value ∈ leaves, (flowAt final.values value).AtomsWithin predicate) :
    (round module states func types state).ScopedValuesWithin selected predicate := by
  simp only [round,← Array.foldl_toList] at below ⊢
  apply state_foldl_below func.blocks.toList _
    (fun current block => state_foldl_extends block.insts _ (step_extends module states func types) current)
    (fun current => current.ScopedValuesWithin selected predicate) ?_ state below before
  intro current block blockMember beforeBelow afterBelow valid
  apply state_foldl_below block.insts _ (step_extends module states func types)
    (fun current => current.ScopedValuesWithin selected predicate) ?_ current afterBelow valid
  intro current inst member beforeBelow afterBelow valid
  exact step_scoped_values valid afterBelow definitions incoming observed blockMember member

theorem FunctionReachable.scoped_values {module : Module} {states : Array State} {func : Func}
    {types : Array (Option VTy)} {current final : State} {selected : ValueId → Prop} {leaves : List ValueId}
    {predicate : Atom → Prop}
    (reachable : FunctionReachable module states func types (start func types) current)
    (suffix : FunctionReachable module states func types current final)
    (bounded : ∀ value, selected value → value < func.numValues)
    (separate : ∀ entry, func.blocks[0]? = some entry →
      ∀ value, selected value → value ∉ leaves → value ∉ entry.params.map Prod.fst)
    (definitions : ∀ block ∈ func.blocks.toList, ∀ value op, Inst.def value op ∈ block.insts →
      selected value → value ∈ leaves ∨ ∃ source, selected source ∧
        (∀ fn args origin, op ≠ .call fn args origin) ∧
        ∀ state, result func types state value op = flowAt state.values source)
    (incoming : ∀ value, selected value → value ∉ leaves →
      ∀ source ∈ allIncomingValues func value, selected source)
    (observed : ∀ value ∈ leaves, (flowAt final.values value).AtomsWithin predicate) :
    current.ScopedValuesWithin selected predicate := by
  induction reachable with
  | refl =>
      intro value chosen
      by_cases leaf : value ∈ leaves
      · exact (suffix.extends.values.values value).atomsWithin (observed value leaf)
      · rw [start_entry_separate_pending (bounded value chosen)
          (fun entry row => separate entry row value chosen leaf)]
        trivial
  | @next current reachable ih =>
      have earlier := ih ((FunctionReachable.next (.refl current)).trans suffix)
      exact round_scoped_values earlier suffix.extends definitions incoming observed

end Goose.GIR.ReplacementContentFlow.Model
