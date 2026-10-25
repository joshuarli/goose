import Goose.Lower.Validation.SourceTouchFootprintCallStep
import Goose.Lower.Validation.SourceTouchOperandsTyping

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR SummaryPreservation
open Goose.GIR.ReplacementContentFlow.Model

theorem accepted_touch_footprint_step {module : Core.Module} {index : Nat}
    {func : Func} {state : State} {states : Array State} {block : GIR.Block} {inst : Inst}
    (accepted : Core.validate module = .ok ())
    (functionAt : (lower module).funcs[index]? = some func)
    (before : state.TouchFootprint func (func.valueTypes (lower module)) (summaryTouchPolicy (lower module) func))
    (canonical : state.CanonicalWithin func (func.valueTypes (lower module))
      (func.provenance (resultRoots (lower module) (lower module).implTypes)
        (func.valueTypes (lower module)) (lower module).rootCount))
    (inputs : ModuleCanonicalWithin (lower module)
      ((lower module).funcs.map (·.valueTypes (lower module)))
      ((lower module).funcs.map fun func => func.provenance
        (resultRoots (lower module) (lower module).implTypes)
        (func.valueTypes (lower module)) (lower module).rootCount) states)
    (support : ModuleSupported (lower module) states)
    (touchRows : ModuleTouchRows (lower module) states)
    (footprints : ModuleTouchFootprints (lower module)
      ((lower module).funcs.map (·.valueTypes (lower module))) (summaryTouchPolicy (lower module)) states)
    (blockMember : block ∈ func.blocks.toList) (member : inst ∈ block.insts) :
    (step (lower module) states func (func.valueTypes (lower module)) state inst).TouchFootprint
      func (func.valueTypes (lower module)) (summaryTouchPolicy (lower module) func) := by
  have facts := (lower_canonical_facts_of_accepted accepted).functions index func functionAt
  simp only [Array.getElem?_map,functionAt,Option.map_some,Option.getD_some] at facts
  have native : (lower module).implTypes[index]?.getD #[] = func.valueTypes (lower module) := by
    rw [module_implTypes_eq_native]
    simp only [Array.getElem?_map,functionAt,Option.map_some,Option.getD_some]
  have checked := accepted_function_native_instruction accepted functionAt blockMember member
  have directBound : ∀ source ∈ directTouchOperands inst,
      (flowAt state.values source).AtomsWithin (TouchFootprintAtom func (summaryTouchPolicy (lower module) func)) := by
    intro source direct
    have sourceUses : source ∈ inst.uses := by
      cases inst with
      | «def» value op => cases op <;> simp_all [directTouchOperands,Inst.uses,Op.uses]
      | eff effect => cases effect <;> simp_all [directTouchOperands,Inst.uses,Effect.uses]
      | term term => simp [directTouchOperands] at direct
    have bounded : source < state.values.size := by
      rw [canonical.shape.values]
      exact facts.uses block blockMember inst member source sourceUses
    have refined := canonical.values source bounded
    have bounded := accepted_direct_touch_policy accepted functionAt blockMember member direct facts.roots.closed
      (by simpa only [native] using refined)
    exact bounded.mono (fun _ policy => Or.inl policy)
  apply before.step canonical facts
  · intro noncall source accessed reference
    have sourceType : ∃ type, (func.valueTypes (lower module))[source]? = some (some type) := by
      cases found : (func.valueTypes (lower module))[source]? with
      | none => simp [valRefLike,found] at reference
      | some row => cases row with
        | none => simp [valRefLike,found] at reference
        | some type => exact ⟨type,rfl⟩
    obtain ⟨type,typeAt⟩ := sourceType
    cases wholeOwner : wholeOwnerReference type with
    | false =>
        exact before.values source (by
          rw [canonical.shape.values]
          exact facts.uses block blockMember inst member source (accessOperands_uses inst accessed))
          type typeAt wholeOwner
    | true =>
        exact directBound source (SourceTouchOperandsTyping.noncall_wholeOwner_access_direct
          facts.valuesShape facts.globalStorage facts.fields checked noncall accessed typeAt wholeOwner)
  · intro value op same source backing
    subst inst
    have produced : ∃ type, op.resultTy { (lower module).tyEnv func with vals := func.valueTypes (lower module) } = .ok type := by
      have typed := facts.typing block blockMember _ member
      cases typed with
      | definition value op type typed canonical => exact ⟨type,typed⟩
    obtain ⟨type,produced⟩ := produced
    rcases SourceTouchOperandsTyping.backing_source_nonwhole_or_direct facts.valuesShape rfl produced backing with
      ⟨sourceType,sourceAt,interior⟩ | direct
    · exact before.values source (by
        rw [canonical.shape.values]
        apply facts.uses block blockMember _ member source
        cases backing <;> simp [Inst.uses,Op.uses]) sourceType sourceAt interior
    · exact directBound source direct
  · intro index payload kind mutability row interior
    apply Or.inl
    exact global_nonowner_summaryTouchPolicy (ReplacementContentFlowSource.accepted_storageClosed accepted) row interior
  · intro value fn args origin same
    subst inst
    exact accepted_call_touch_footprint_step accepted functionAt before canonical inputs support touchRows footprints
      blockMember member
  · exact blockMember
  · exact member

#print axioms accepted_touch_footprint_step

end Goose.Lower.Validation
