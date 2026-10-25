import Goose.Lower.Validation.ProvenanceConvergenceFinite

namespace Goose.Lower.Validation.ProvenanceConvergence

open Goose.Core Goose.GIR

theorem InstructionRootsClosed.store {results : Array (List RootRef)}
    {types : Array (Option VTy)} {func : Func} {provenance : Prov}
    (closed : InstructionRootsClosed results types func provenance)
    {block : GIR.Block} (blockMember : block ∈ func.blocks.toList)
    {owner value : ValueId} {origin : OriginId}
    (member : Inst.eff (.store owner value origin) ∈ block.insts)
    {slot : SlotId} (localRoot : RootRef.local slot ∈ rootsAt provenance.vals owner)
    (bounded : slot < provenance.slots.size) :
    rootsAt provenance.vals value ⊆ rootsAt provenance.slots slot := by
  let step : Prov × Bool → RootRef → Prov × Bool := fun acc root =>
    match root with
    | .local slot =>
      ({ acc.1 with slots := (GIR.addTo acc.1.slots slot (rootsAt acc.1.vals value)).1 },
        acc.2 || (GIR.addTo acc.1.slots slot (rootsAt acc.1.vals value)).2)
    | _ => acc
  have grows : ∀ state root, Growth state (step state root) := by
    intro state root
    cases root with
    | «local» slot => exact Growth.addSlots _ _ _
    | _ => exact Growth.refl state
  have same := closed block blockMember _ member
  change (rootsAt provenance.vals owner).foldl step (provenance, false) = (provenance, false) at same
  have stepSame := fold_step_quiet grows (by rw [same]) localRoot
  have slotsSame := congrArg (fun state : Prov × Bool => state.1.slots) stepSame
  change (GIR.addTo provenance.slots slot (rootsAt provenance.vals value)).1 = provenance.slots at slotsSame
  intro root produced
  have inserted := addTo_inserts bounded produced
  rw [slotsSame] at inserted
  exact inserted

theorem branchRootsClosed_of_step {results : Array (List RootRef)} {types : Array (Option VTy)}
    {func : Func} {provenance : Prov} {target : BlockId} {args : List ValueId}
    (fixed : func.provStep results types (provenance, false) (.term (.br target args)) = (provenance, false))
    {block : GIR.Block} (targetAt : func.blocks[target]? = some block)
    {param : ValueId × VTy} {argument : ValueId} (member : (param, argument) ∈ block.params.zip args)
    (bounded : param.1 < provenance.vals.size) :
    rootsAt provenance.vals argument ⊆ rootsAt provenance.vals param.1 := by
  let step : Prov × Bool → (ValueId × VTy) × ValueId → Prov × Bool := fun acc pair =>
    ({ acc.1 with vals := (GIR.addTo acc.1.vals pair.1.1 (rootsAt acc.1.vals pair.2)).1 },
      acc.2 || (GIR.addTo acc.1.vals pair.1.1 (rootsAt acc.1.vals pair.2)).2)
  have grows : ∀ state pair, Growth state (step state pair) := fun _ _ => Growth.addValues _ _ _
  simp only [Func.provStep, targetAt] at fixed
  change (block.params.zip args).foldl step (provenance, false) = (provenance, false) at fixed
  have stepSame := fold_step_quiet grows (by rw [fixed]) member
  have valsSame := congrArg (fun state : Prov × Bool => state.1.vals) stepSame
  change (GIR.addTo provenance.vals param.1 (rootsAt provenance.vals argument)).1 = provenance.vals at valsSame
  intro root produced
  have inserted := addTo_inserts bounded produced
  rw [valsSame] at inserted
  exact inserted

theorem InstructionRootsClosed.branch {results : Array (List RootRef)}
    {types : Array (Option VTy)} {func : Func} {provenance : Prov}
    (closed : InstructionRootsClosed results types func provenance)
    {source : GIR.Block} (sourceMember : source ∈ func.blocks.toList)
    {target : BlockId} {args : List ValueId} (instMember : Inst.term (.br target args) ∈ source.insts)
    {block : GIR.Block} (targetAt : func.blocks[target]? = some block)
    {param : ValueId × VTy} {argument : ValueId} (member : (param, argument) ∈ block.params.zip args)
    (bounded : param.1 < provenance.vals.size) :
    rootsAt provenance.vals argument ⊆ rootsAt provenance.vals param.1 :=
  branchRootsClosed_of_step (closed source sourceMember _ instMember) targetAt member bounded

theorem InstructionRootsClosed.conditionalSteps {results : Array (List RootRef)}
    {types : Array (Option VTy)} {func : Func} {provenance : Prov}
    (closed : InstructionRootsClosed results types func provenance)
    {source : GIR.Block} (sourceMember : source ∈ func.blocks.toList)
    {condition : ValueId} {left right : BlockId} {leftArgs rightArgs : List ValueId}
    (member : Inst.term (.condbr condition left leftArgs right rightArgs) ∈ source.insts) :
    func.provStep results types (provenance, false) (.term (.br left leftArgs)) = (provenance, false) ∧
    func.provStep results types (provenance, false) (.term (.br right rightArgs)) = (provenance, false) := by
  have same := closed source sourceMember _ member
  change func.provStep results types
    (func.provStep results types (provenance, false) (.term (.br left leftArgs)))
    (.term (.br right rightArgs)) = (provenance, false) at same
  have second := provStep_growth results types func
    (func.provStep results types (provenance, false) (.term (.br left leftArgs))) (.term (.br right rightArgs))
  have firstQuiet := second.flag_false (show _ = false from congrArg Prod.snd same)
  have firstSame := (provStep_growth results types func (provenance, false)
    (.term (.br left leftArgs))).quiet_eq firstQuiet
  exact ⟨firstSame, by simpa only [firstSame] using same⟩

end Goose.Lower.Validation.ProvenanceConvergence
