import Goose.Lower.Validation.SourceTouchFootprintStep

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR SummaryPreservation
open Goose.GIR.ReplacementContentFlow.Model

private theorem accepted_reachable_touch_footprints {module : Core.Module}
    (accepted : Core.validate module = .ok ())
    (preserved : ∀ (states : Array State) (index : Nat) (func : Func) (state : State)
      (block : GIR.Block) (inst : Inst), (lower module).funcs[index]? = some func →
      state.TouchFootprint func (func.valueTypes (lower module)) (summaryTouchPolicy (lower module) func) →
      state.CanonicalWithin func (func.valueTypes (lower module))
        (func.provenance (resultRoots (lower module) (lower module).implTypes)
          (func.valueTypes (lower module)) (lower module).rootCount) →
      ModuleCanonicalWithin (lower module)
        ((lower module).funcs.map (·.valueTypes (lower module)))
        ((lower module).funcs.map fun func => func.provenance
          (resultRoots (lower module) (lower module).implTypes)
          (func.valueTypes (lower module)) (lower module).rootCount) states →
      ModuleSupported (lower module) states → ModuleTouchRows (lower module) states →
      ModuleTouchFootprints (lower module) ((lower module).funcs.map (·.valueTypes (lower module)))
        (summaryTouchPolicy (lower module)) states →
      block ∈ func.blocks.toList → inst ∈ block.insts →
      (step (lower module) states func (func.valueTypes (lower module)) state inst).TouchFootprint
        func (func.valueTypes (lower module)) (summaryTouchPolicy (lower module) func))
    {states : Array State}
    (reachable : ModuleReachable (lower module) ((lower module).funcs.map (·.valueTypes (lower module)))
      (moduleStart (lower module) ((lower module).funcs.map (·.valueTypes (lower module)))) states) :
    ModuleTouchFootprints (lower module) ((lower module).funcs.map (·.valueTypes (lower module)))
      (summaryTouchPolicy (lower module)) states := by
  have moduleFacts := lower_canonical_facts_of_accepted accepted
  obtain ⟨annotations,entries,addresses⟩ := lower_canonical_factory_structure_of_accepted accepted
  have initialCanonical := moduleStart_canonicalWithin moduleFacts
  have initialFinite := moduleStart_finite (lower module)
    ((lower module).funcs.map (·.valueTypes (lower module))) annotations entries
  induction reachable with
  | refl => exact moduleStart_touchFootprints _ moduleFacts
  | @next current reachable ih =>
      obtain ⟨canonical,finite⟩ := reachable.canonicalWithin moduleFacts initialCanonical initialFinite addresses
      have rows := reachable.touchRows moduleFacts initialCanonical initialFinite addresses
        (moduleStart_touchRows _ _)
      intro index func state functionAt stateAt
      obtain ⟨prior,priorAt,priorCanonical⟩ := canonical.2 index func functionAt
      have same : state = round (lower module) current func
          (func.valueTypes (lower module)) prior := by
        simpa [moduleRound,functionAt,priorAt] using stateAt.symm
      subst state
      have priorFootprint := ih index func prior functionAt priorAt
      have facts := moduleFacts.functions index func functionAt
      simp only [Array.getElem?_map,functionAt,Option.map_some,Option.getD_some] at priorFootprint priorCanonical facts ⊢
      exact priorFootprint.round priorCanonical facts moduleFacts canonical finite.1
        (fun state block blockMember inst member before bounded =>
          preserved current index func state block inst functionAt before bounded canonical finite.1 rows ih blockMember member)

theorem accepted_module_touchFootprint {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {states : Array State}
    (closed : close (lower module) ((lower module).funcs.map (·.valueTypes (lower module))) = some states)
    {index : Nat} {func : Func} {state : State}
    (functionAt : (lower module).funcs[index]? = some func)
    (stateAt : states[index]? = some state) :
    state.TouchFootprint func (func.valueTypes (lower module))
      (summaryTouchPolicy (lower module) func) := by
  have footprints := accepted_reachable_touch_footprints accepted
    (fun states index func state block inst functionAt before canonical inputs support rows footprints blockMember member =>
      accepted_touch_footprint_step accepted functionAt before canonical inputs support rows footprints blockMember member)
    (close_reachable closed)
  simpa [Array.getElem?_map,functionAt] using footprints index func state functionAt stateAt

theorem accepted_public_touch_footprint {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {states : Array State}
    (closed : close (lower module) ((lower module).funcs.map (·.valueTypes (lower module))) = some states)
    {index : Nat} {func : Func} {state : State}
    (functionAt : (lower module).funcs[index]? = some func)
    (stateAt : states[index]? = some state) :
    ∃ atoms, publicTouches state.touched = .known atoms ∧
      ∀ atom ∈ atoms, match atom with
        | .global global => summaryTouchPolicy (lower module) func (.global global)
        | .param _ | .contents _ => True
        | .local _ => False := by
  have facts := lower_canonical_facts_of_accepted accepted
  obtain ⟨annotations,entries,addresses⟩ := lower_canonical_factory_structure_of_accepted accepted
  obtain ⟨actual,known⟩ := close_touched_known facts annotations entries addresses closed functionAt stateAt
  obtain ⟨raw,rawAt⟩ := normalize_known_shape known
  obtain ⟨atoms,publicAt⟩ := publicTouches_known raw
  rw [← rawAt] at publicAt
  refine ⟨atoms,publicAt,?_⟩
  have bounded := publicTouches_atomsWithin
    (accepted_module_touchFootprint accepted closed functionAt stateAt).touched
  rw [publicAt] at bounded
  intro atom member
  obtain ⟨policy,external⟩ := bounded atom member
  cases atom with
  | «local» slot => exact external slot rfl
  | param _ | contents _ => trivial
  | global global => simpa [TouchFootprintAtom] using policy

#print axioms accepted_module_touchFootprint
#print axioms accepted_public_touch_footprint

end Goose.Lower.Validation
