import Goose.Lower.Validation.SourceTouchFootprintInputs
import Goose.Lower.Validation.SourceTouchCallPolicy

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR SummaryPreservation
open Goose.GIR.ReplacementContentFlow.Model

theorem accepted_call_touch_footprint_substitution {module : Core.Module} {index : Nat}
    {func : Func} {state : State} {block : GIR.Block} {fn value : ValueId}
    {args : List ValueId} {origin : Option OriginId} {roots : Roots}
    (accepted : Core.validate module = .ok ())
    (functionAt : (lower module).funcs[index]? = some func)
    (before : state.TouchFootprint func (func.valueTypes (lower module)) (summaryTouchPolicy (lower module) func))
    (canonical : state.CanonicalWithin func (func.valueTypes (lower module))
      (func.provenance (resultRoots (lower module) (lower module).implTypes)
        (func.valueTypes (lower module)) (lower module).rootCount))
    (facts : FunctionCanonicalFacts (lower module) func (func.valueTypes (lower module))
      (func.provenance (resultRoots (lower module) (lower module).implTypes)
        (func.valueTypes (lower module)) (lower module).rootCount)
      (resultRoots (lower module) (lower module).implTypes))
    (site : CallSiteFacts (lower module) func (func.valueTypes (lower module))
      (func.provenance (resultRoots (lower module) (lower module).implTypes)
        (func.valueTypes (lower module)) (lower module).rootCount) fn args)
    (calleeRoots : FunctionRootFacts site.callee)
    (bounded : roots.AtomsWithin (TouchFootprintAtom site.callee (summaryTouchPolicy (lower module) site.callee)))
    (supported : roots.Supported (atomUniverse (lower module) site.callee))
    (normalizable : roots.AtomsWithin (fun atom => (normalizeAtom site.callee atom).isSome = true))
    (external : roots.AtomsWithin (fun atom => ∀ slot, atom ≠ .local slot))
    (blockMember : block ∈ func.blocks.toList)
    (called : Inst.def value (.call fn args origin) ∈ block.insts) :
    (substitute func state args roots).AtomsWithin
      (TouchFootprintAtom func (summaryTouchPolicy (lower module) func)) := by
  have native : (lower module).implTypes[index]?.getD #[] = func.valueTypes (lower module) := by
    rw [module_implTypes_eq_native]
    simp only [Array.getElem?_map,functionAt,Option.map_some,Option.getD_some]
  apply before.substitute canonical facts site calleeRoots bounded supported normalizable external ?_ blockMember called
  intro atom policy support row apart
  cases atom with
  | «local» slot => exact False.elim (apart slot rfl)
  | contents parameter => exact before.call_contents canonical site facts.roots.parameters calleeRoots row
  | global global =>
      intro actual member
      have same : actual = .global global := by simpa using member
      subst actual
      apply Or.inl
      cases summaryAt : func.summary with
      | unknown => simp [summaryTouchPolicy,summaryTouchRoots,summaryAt]
      | known summary =>
          obtain ⟨calleeSummary,calleeKnown⟩ := accepted_known_caller_known_callee accepted functionAt
            summaryAt blockMember called site.calleeAt
          exact accepted_call_global_touch_policy accepted functionAt summaryAt blockMember called site.calleeAt
            calleeKnown facts.roots.closed calleeRoots.closed policy
  | param parameter =>
      obtain ⟨argument,argumentAt,argumentBound⟩ := site.arguments parameter
        ((atomUniverse_param (lower module) site.callee parameter).mp support)
      simp only [argumentAt,Option.map_some,Option.getD_some]
      have refined := canonical.values argument (by rw [canonical.shape.values]; exact argumentBound)
      cases summaryAt : func.summary with
      | unknown =>
          apply refined.normalizableAtoms.mono
          intro atom _
          apply Or.inl
          simp [summaryTouchPolicy,summaryTouchRoots,summaryAt]
      | known summary =>
          obtain ⟨calleeSummary,calleeKnown⟩ := accepted_known_caller_known_callee accepted functionAt
            summaryAt blockMember called site.calleeAt
          have mappedRefined : SymbolicRootsRefine func (flowAt state.values argument)
              (mapRawContentRoots
                (func.provenance (resultRoots (lower module) (lower module).implTypes)
                  ((lower module).implTypes[index]?.getD #[]) (lower module).rootCount) args [.param parameter]) := by
            rw [native]
            apply refined.source_mono
            intro root member
            simpa [mapRawContentRoots,argumentAt] using member
          have mapped := accepted_call_parameter_touch_policy accepted functionAt summaryAt blockMember called
            site.calleeAt calleeKnown facts.roots.closed calleeRoots.closed policy
            (by simpa only [native] using site.contracts) mappedRefined
          exact mapped.mono (fun _ policy => Or.inl policy)

#print axioms accepted_call_touch_footprint_substitution

end Goose.Lower.Validation
