import Goose.GIR.ReplacementContentFlowProofsScopedEdges

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

def ScalarCells (types : Array (Option VTy)) (values : Array Roots) : Prop :=
  ∀ value, value < values.size → valRefLike types value = false →
    (flowAt values value).AtomsWithin (fun _ => False)

theorem ScalarCells.set {types : Array (Option VTy)} {values : Array Roots} {index : Nat} {roots : Roots}
    (before : ScalarCells types values)
    (added : valRefLike types index = false → roots.AtomsWithin (fun _ => False)) :
    ScalarCells types (values.set! index roots) := by
  intro value bounded scalar
  have priorBound : value < values.size := by simpa using bounded
  change ((values.set! index roots)[value]?.getD .unknown).AtomsWithin _
  simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases same : index = value
  · subst value
    simpa [priorBound] using added scalar
  · simpa [same, flowAt] using before value priorBound scalar

theorem ScalarCells.addFlow {types : Array (Option VTy)} {values : Array Roots} {index : Nat} {roots : Roots}
    (before : ScalarCells types values)
    (added : valRefLike types index = false → roots.AtomsWithin (fun _ => False)) :
    ScalarCells types (addFlow values index roots) := by
  intro value bounded scalar
  have priorBound : value < values.size := by simpa [ReplacementContentFlow.Model.addFlow] using bounded
  rw [flowAt_addFlow]
  split
  · rename_i updated
    have same := updated.1
    subst value
    exact (before index priorBound scalar).join (added scalar)
  · exact before value priorBound scalar

theorem start_scalar_values (func : Func) (types : Array (Option VTy)) :
    ScalarCells types (start func types).values := by
  cases found : func.blocks[0]? with
  | none =>
    intro value bounded scalar
    have bound : value < func.numValues := by simpa [start, found] using bounded
    simp [start, found, flowAt, bound, Roots.AtomsWithin]
  | some entry =>
    rw [start_values_fold types found]
    have base : ScalarCells types (Array.replicate func.numValues .pending) := by
      intro value bounded scalar
      have bound : value < func.numValues := by simpa using bounded
      simp [flowAt, bound, Roots.AtomsWithin]
    apply List.foldlRecOn (motive := ScalarCells types) entry.params.zipIdx _ base
    intro values before pair member
    apply before.set
    intro scalar
    simp [scalar, Roots.AtomsWithin]

theorem edge_scalar_values {func : Func} {types : Array (Option VTy)} {state : State}
    {target : BlockId} {args : List ValueId} {block : Block}
    (shape : state.Shape func) (before : ScalarCells types state.values)
    (targetAt : func.blocks[target]? = some block)
    (typed : ∀ parameter argument, (parameter, argument) ∈ block.params.zip args →
      types[parameter.1]? = types[argument]? ∧ argument < func.numValues) :
    ScalarCells types (edge func state target args).values := by
  simp only [edge, targetAt]
  have result : (block.params.zip args).foldl (fun state pair =>
      { state with values := addFlow state.values pair.1.1 (flowAt state.values pair.2) }) state |>
      fun after => after.Shape func ∧ ScalarCells types after.values := by
    apply List.foldlRecOn (motive := fun current : State => current.Shape func ∧ ScalarCells types current.values)
      (block.params.zip args) _ ⟨shape, before⟩
    intro current valid pair member
    refine ⟨(current.extends_values _ _).shape valid.1, valid.2.addFlow ?_⟩
    intro scalar
    have sourceScalar : valRefLike types pair.2 = false := by
      simpa only [valRefLike, ← (typed pair.1 pair.2 member).1] using scalar
    exact valid.2 pair.2 (valid.1.values ▸ (typed pair.1 pair.2 member).2) sourceScalar
  exact result.2

theorem step_scalar_values {module : Module} {states : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {inst : Inst}
    (shape : state.Shape func) (before : ScalarCells types state.values)
    (typed : InstructionTyping module func types inst) :
    ScalarCells types (step module states func types state inst).values := by
  cases typed with
  | definition value op type typed canonical =>
    rw [step_def_values]
    apply before.addFlow
    intro scalar
    cases op <;> simp [scalar, result, Roots.AtomsWithin]
  | branch target args block targetAt typed bounded =>
    simpa only [step, Id.run_pure, touchValues_values] using
      edge_scalar_values ((touchValues_extends types state _).shape shape) before targetAt typed
  | conditional condition left right leftArgs rightArgs leftBlock rightBlock leftAt rightAt leftTypes rightTypes leftBound rightBound =>
    have first := edge_scalar_values (target := left) (args := leftArgs) ((touchValues_extends types state (accessOperands (.term (.condbr condition left leftArgs right rightArgs)))).shape shape) before leftAt leftTypes
    simpa only [step, Id.run_pure] using edge_scalar_values
      ((edge_extends func _ left leftArgs).shape ((touchValues_extends types state (accessOperands (.term (.condbr condition left leftArgs right rightArgs)))).shape shape)) first rightAt rightTypes
  | slotInit => exact before
  | effect effect ordinary nonstore =>
    cases effect <;> try exact before
    exact False.elim (nonstore _ _ _ rfl)
  | store =>
    simp only [step, Id.run_pure]
    split
    · simpa only [write_values, touchValues_values] using before
    · exact before
  | returned => exact before
  | terminal term nonbranch nonconditional nonreturned =>
    cases term <;> try exact before
    · exact False.elim (nonbranch _ _ rfl)
    · exact False.elim (nonconditional _ _ _ _ _ rfl)
    · rename_i values origin
      cases values with
      | nil => exact before
      | cons first rest => cases rest <;> exact before

theorem FunctionReachable.scalar_values {module : Module} {states : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State}
    (reachable : FunctionReachable module states func types (start func types) state)
    (typing : ∀ block ∈ func.blocks.toList, ∀ inst ∈ block.insts, InstructionTyping module func types inst) :
    ScalarCells types state.values := by
  induction reachable with
  | refl => exact start_scalar_values func types
  | @next current reachable ih =>
    have shape := reachable.extends.shape (start_shape func types)
    have result : (round module states func types current).Shape func ∧
        ScalarCells types (round module states func types current).values := by
      simp only [round, ← Array.foldl_toList]
      apply List.foldlRecOn (motive := fun current : State => current.Shape func ∧ ScalarCells types current.values)
        func.blocks.toList _ ⟨shape, ih⟩
      intro before valid block member
      apply List.foldlRecOn (motive := fun current : State => current.Shape func ∧ ScalarCells types current.values)
        block.insts _ valid
      intro before valid inst instructionMember
      exact ⟨(step_extends module states func types before inst).shape valid.1,
        step_scalar_values valid.1 valid.2 (typing block member inst instructionMember)⟩
    exact result.2

#print axioms FunctionReachable.scalar_values

end Goose.GIR.ReplacementContentFlow.Model
