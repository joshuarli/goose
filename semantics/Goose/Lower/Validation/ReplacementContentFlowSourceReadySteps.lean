import Goose.Lower.Validation.ReplacementContentFlowSourceReadyCore
import Goose.GIR.ReplacementContentFlowProofsSteps

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem bind_ready {roots : Roots} {map : Atom → Roots}
    (ready : roots ≠ .pending)
    (mapped : ∀ atoms, roots = .known atoms → ∀ atom ∈ atoms, map atom ≠ .pending) :
    roots.bind map ≠ .pending := by
  cases roots with
  | pending => exact False.elim (ready rfl)
  | unknown => simp [Roots.bind]
  | known atoms =>
    have all := mapped atoms rfl
    clear ready mapped
    have fold : ∀ initial : Roots, initial ≠ .pending →
        atoms.foldl (fun acc atom => match acc, map atom with
          | .unknown, _ | _, .unknown => .unknown
          | .pending, _ | _, .pending => .pending
          | left, right => left.join right) initial ≠ .pending := by
      induction atoms with
      | nil => intro initial available; exact available
      | cons atom rest ih =>
        intro initial available
        apply ih (fun selected member => all selected (by simp [member]))
        have first := all atom (by simp)
        cases initial <;> cases found : map atom <;> simp_all [Roots.join]
    exact fold (.known []) (by simp)

theorem fixed_slotInit_ready {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {slot : SlotId} {value : ValueId} {origin : Option OriginId}
    (fixed : step module callees func types state (.eff (.slotInit slot value origin)) = state)
    (bound : slot < state.slots.size) (ready : flowAt state.values value ≠ .pending) :
    flowAt state.slots slot ≠ .pending := by
  have equality := congrArg State.slots fixed
  change addFlow state.slots slot (flowAt state.values value) = state.slots at equality
  rw [← equality, flowAt_addFlow]
  simp only [bound, and_self, ite_true]
  exact Roots.join_ready_right _ _ ready

theorem round_slotInit_ready {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {slot : SlotId} {value : ValueId} {origin : Option OriginId}
    (fixed : round module callees func types state = state)
    {block : GIR.Block} (blockMember : block ∈ func.blocks.toList)
    (instructionMember : Inst.eff (.slotInit slot value origin) ∈ block.insts)
    (bound : slot < state.slots.size) (ready : flowAt state.values value ≠ .pending) :
    flowAt state.slots slot ≠ .pending :=
  fixed_slotInit_ready
    (round_fixed_step module callees func types state fixed block blockMember _ instructionMember) bound ready

theorem edge_parameter_ready {func : Func} {state : State} {target : BlockId} {args : List ValueId}
    {block : GIR.Block} (row : func.blocks[target]? = some block)
    {parameter : ValueId × VTy} {argument : ValueId}
    (member : (parameter, argument) ∈ block.params.zip args)
    (bound : parameter.1 < state.values.size) (ready : flowAt state.values argument ≠ .pending) :
    flowAt (edge func state target args).values parameter.1 ≠ .pending := by
  let update := fun (current : State) (binding : (ValueId × VTy) × ValueId) =>
    { current with values := addFlow current.values binding.1.1 (flowAt current.values binding.2) }
  have growth : ∀ (current : State) (binding : (ValueId × VTy) × ValueId), current.Extends (update current binding) :=
    fun current binding => State.extends_values _ _ _
  obtain ⟨earlier, suffix, split⟩ := List.append_of_mem member
  let middle := earlier.foldl update state
  have prefixGrowth : state.Extends middle := state_foldl_extends earlier update growth state
  have argumentReady := (prefixGrowth.values.values argument).ready ready
  have parameterBound : parameter.1 < middle.values.size := by
    rw [← prefixGrowth.values.size]
    exact bound
  let updated := update middle (parameter, argument)
  have producedReady : flowAt updated.values parameter.1 ≠ .pending := by
    change flowAt (addFlow middle.values parameter.1 (flowAt middle.values argument)) parameter.1 ≠ .pending
    rw [flowAt_addFlow]
    simp only [parameterBound, and_self, ite_true]
    exact Roots.join_ready_right _ _ argumentReady
  have suffixGrowth := state_foldl_extends suffix update growth updated
  have available := (suffixGrowth.values.values parameter.1).ready producedReady
  simpa only [edge, row, split, List.foldl_append, List.foldl_cons, update, middle, updated, flowAt] using available

theorem round_branch_parameter_ready {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {target : BlockId} {args : List ValueId}
    (fixed : round module callees func types state = state)
    {sourceBlock : GIR.Block} (sourceMember : sourceBlock ∈ func.blocks.toList)
    (instructionMember : Inst.term (.br target args) ∈ sourceBlock.insts)
    {targetBlock : GIR.Block} (targetRow : func.blocks[target]? = some targetBlock)
    {parameter : ValueId × VTy} {argument : ValueId}
    (member : (parameter, argument) ∈ targetBlock.params.zip args)
    (bound : parameter.1 < state.values.size) (ready : flowAt state.values argument ≠ .pending) :
    flowAt state.values parameter.1 ≠ .pending := by
  have saturated := round_fixed_step module callees func types state fixed sourceBlock sourceMember _ instructionMember
  change edge func state target args = state at saturated
  have available := edge_parameter_ready targetRow member bound ready
  rw [saturated] at available
  exact available

#print axioms edge_parameter_ready
#print axioms round_branch_parameter_ready

#print axioms bind_ready
#print axioms fixed_slotInit_ready
#print axioms round_slotInit_ready

end Goose.Lower.Validation.ReplacementContentFlowSource
