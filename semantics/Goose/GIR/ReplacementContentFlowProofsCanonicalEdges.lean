import Goose.GIR.ReplacementContentFlowProofsCanonicalOps

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem State.CanonicalWithin.edge {func : Func} {vt : Array (Option VTy)} {provenance : Prov}
    {state : State} {target : BlockId} {args : List ValueId} {block : Block}
    (before : state.CanonicalWithin func vt provenance) (targetAt : func.blocks[target]? = some block)
    (types : ∀ parameter argument, (parameter,argument) ∈ block.params.zip args →
      vt[parameter.1]? = vt[argument]? ∧ argument < func.numValues)
    (roots : ∀ parameter argument, (parameter,argument) ∈ block.params.zip args →
      rootsAt provenance.vals argument ⊆ rootsAt provenance.vals parameter.1) :
    (ReplacementContentFlow.Model.edge func state target args).CanonicalWithin func vt provenance := by
  simp only [ReplacementContentFlow.Model.edge,targetAt]
  apply List.foldlRecOn (motive := fun current : State => current.CanonicalWithin func vt provenance)
    (block.params.zip args) _ before
  intro current valid pair member
  obtain ⟨sameType,bounded⟩ := types pair.1 pair.2 member
  have bound : pair.2 < current.values.size := by rw [valid.shape.values]; exact bounded
  have ceiling := roots pair.1 pair.2 member
  apply valid.addValue ((valid.values pair.2 bound).source_mono ceiling)
  · intro mutability payload type reference
    rw [sameType] at type
    exact (valid.holderValues pair.2 bound mutability payload type reference).mono ceiling
  · intro mutability payload type owner
    rw [sameType] at type
    exact valid.ownerValues pair.2 bound mutability payload type owner

theorem State.CanonicalWithin.br {module : Module} {states : Array State}
    {func : Func} {vt : Array (Option VTy)} {provenance : Prov} {state : State}
    {target : BlockId} {args : List ValueId} {block : Block}
    (before : state.CanonicalWithin func vt provenance) (targetAt : func.blocks[target]? = some block)
    (types : ∀ parameter argument, (parameter,argument) ∈ block.params.zip args →
      vt[parameter.1]? = vt[argument]? ∧ argument < func.numValues)
    (roots : ∀ parameter argument, (parameter,argument) ∈ block.params.zip args →
      rootsAt provenance.vals argument ⊆ rootsAt provenance.vals parameter.1) :
    (step module states func vt state (.term (.br target args))).CanonicalWithin func vt provenance := by
  simpa only [step,accessOperands,ReplacementContentFlow.Model.touchValues,List.foldl_nil,Id.run_pure] using
    before.edge targetAt types roots

theorem State.CanonicalWithin.condbr {module : Module} {states : Array State}
    {func : Func} {vt : Array (Option VTy)} {provenance : Prov} {state : State} {condition : ValueId}
    {thenTarget elseTarget : BlockId} {thenArgs elseArgs : List ValueId} {thenBlock elseBlock : Block}
    (before : state.CanonicalWithin func vt provenance)
    (thenAt : func.blocks[thenTarget]? = some thenBlock) (elseAt : func.blocks[elseTarget]? = some elseBlock)
    (thenTypes : ∀ parameter argument, (parameter,argument) ∈ thenBlock.params.zip thenArgs →
      vt[parameter.1]? = vt[argument]? ∧ argument < func.numValues)
    (elseTypes : ∀ parameter argument, (parameter,argument) ∈ elseBlock.params.zip elseArgs →
      vt[parameter.1]? = vt[argument]? ∧ argument < func.numValues)
    (thenRoots : ∀ parameter argument, (parameter,argument) ∈ thenBlock.params.zip thenArgs →
      rootsAt provenance.vals argument ⊆ rootsAt provenance.vals parameter.1)
    (elseRoots : ∀ parameter argument, (parameter,argument) ∈ elseBlock.params.zip elseArgs →
      rootsAt provenance.vals argument ⊆ rootsAt provenance.vals parameter.1) :
    (step module states func vt state (.term (.condbr condition thenTarget thenArgs elseTarget elseArgs))).CanonicalWithin
      func vt provenance := by
  simpa only [step,accessOperands,ReplacementContentFlow.Model.touchValues,List.foldl_nil,Id.run_pure] using
    (before.edge thenAt thenTypes thenRoots).edge elseAt elseTypes elseRoots

theorem State.CanonicalWithin.br_closed {module : Module} {states : Array State}
    {results : Array (List RootRef)} {func : Func} {vt : Array (Option VTy)} {provenance : Prov}
    {state : State} {target : BlockId} {args : List ValueId} {block : Block}
    (before : state.CanonicalWithin func vt provenance) (targetAt : func.blocks[target]? = some block)
    (types : ∀ parameter argument, (parameter,argument) ∈ block.params.zip args →
      vt[parameter.1]? = vt[argument]? ∧ argument < func.numValues)
    (parameters : ∀ parameter ∈ block.params, parameter.1 < provenance.vals.size)
    (quiet : func.provStep results vt (provenance,false) (.term (.br target args)) = (provenance,false)) :
    (step module states func vt state (.term (.br target args))).CanonicalWithin func vt provenance := by
  apply before.br targetAt types
  intro parameter argument member
  exact provStep_br_roots targetAt quiet member (parameters parameter ((List.of_mem_zip member).1))

theorem State.CanonicalWithin.condbr_closed {module : Module} {states : Array State}
    {results : Array (List RootRef)} {func : Func} {vt : Array (Option VTy)} {provenance : Prov}
    {state : State} {condition thenTarget elseTarget : ValueId}
    {thenArgs elseArgs : List ValueId} {thenBlock elseBlock : Block}
    (before : state.CanonicalWithin func vt provenance)
    (thenAt : func.blocks[thenTarget]? = some thenBlock) (elseAt : func.blocks[elseTarget]? = some elseBlock)
    (thenTypes : ∀ parameter argument, (parameter,argument) ∈ thenBlock.params.zip thenArgs →
      vt[parameter.1]? = vt[argument]? ∧ argument < func.numValues)
    (elseTypes : ∀ parameter argument, (parameter,argument) ∈ elseBlock.params.zip elseArgs →
      vt[parameter.1]? = vt[argument]? ∧ argument < func.numValues)
    (thenParameters : ∀ parameter ∈ thenBlock.params, parameter.1 < provenance.vals.size)
    (elseParameters : ∀ parameter ∈ elseBlock.params, parameter.1 < provenance.vals.size)
    (quiet : func.provStep results vt (provenance,false)
      (.term (.condbr condition thenTarget thenArgs elseTarget elseArgs)) = (provenance,false)) :
    (step module states func vt state (.term (.condbr condition thenTarget thenArgs elseTarget elseArgs))).CanonicalWithin
      func vt provenance := by
  have roots := provStep_condbr_roots thenAt elseAt quiet
  exact before.condbr thenAt elseAt thenTypes elseTypes
    (fun parameter argument member => roots.1 parameter argument member
      (thenParameters parameter ((List.of_mem_zip member).1)))
    (fun parameter argument member => roots.2 parameter argument member
      (elseParameters parameter ((List.of_mem_zip member).1)))

#print axioms State.CanonicalWithin.edge
#print axioms State.CanonicalWithin.br
#print axioms State.CanonicalWithin.condbr

end Goose.GIR.ReplacementContentFlow.Model
