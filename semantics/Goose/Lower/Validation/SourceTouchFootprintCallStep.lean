import Goose.Lower.Validation.SourceTouchFootprintCalls
import Goose.Lower.Validation.SourceCanonicalFactsAssembly

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR SummaryPreservation
open Goose.GIR.ReplacementContentFlow.Model

theorem accepted_call_touch_footprint_step {module : Core.Module} {index : Nat}
    {func : Func} {state : State} {states : Array State} {block : GIR.Block}
    {fn value : ValueId} {args : List ValueId} {origin : Option OriginId}
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
    (blockMember : block ∈ func.blocks.toList)
    (called : Inst.def value (.call fn args origin) ∈ block.insts) :
    (step (lower module) states func (func.valueTypes (lower module)) state (.def value (.call fn args origin))).TouchFootprint
      func (func.valueTypes (lower module)) (summaryTouchPolicy (lower module) func) := by
  have moduleFacts := lower_canonical_facts_of_accepted accepted
  have facts := moduleFacts.functions index func functionAt
  simp only [Array.getElem?_map,functionAt,Option.map_some,Option.getD_some] at facts
  obtain ⟨site⟩ := facts.calls block blockMember value fn args origin called
  obtain ⟨effects,effectsAt,effectsCanonical⟩ := inputs.2 fn site.callee site.calleeAt
  have effectsFootprint := footprints fn site.callee effects site.calleeAt effectsAt
  simp only [Array.getElem?_map,site.calleeAt,Option.map_some,Option.getD_some] at effectsCanonical effectsFootprint
  have calleeRoots := (moduleFacts.functions fn site.callee site.calleeAt).roots
  apply before.call canonical facts site effectsAt effectsFootprint effectsCanonical calleeRoots
    (support fn site.callee effects site.calleeAt effectsAt)
    (touchRows fn site.callee effects site.calleeAt effectsAt) ?_ blockMember called
  intro roots bounded supported normalizable external
  exact accepted_call_touch_footprint_substitution accepted functionAt before canonical facts site calleeRoots
    bounded supported normalizable external blockMember called

#print axioms accepted_call_touch_footprint_step

end Goose.Lower.Validation
