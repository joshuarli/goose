import Goose.Lower.Validation.AdmittedSourceCallsTransport
import Goose.GIR.ReplacementContentFlowProofsCanonicalFacts
import Goose.GIR.ReplacementContentFlowProofsSliceSubstitution

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem normalized_symbolic_source_bound {func : Func} {roots : Roots} {source actual : List RootRef}
    (closed : ∀ index root, root ∈ func.parameterRoots index → root = .param index ∨ ∃ global, root = .global global)
    (refined : SymbolicRootsRefine func roots source)
    (known : normalize func roots = some actual) :
    actual ⊆ source.flatMap func.expandParameterRoot := by
  have ready : roots ≠ .pending := by
    intro same
    subst roots
    cases known
  obtain ⟨found, normalized, within⟩ := refined.actual closed ready
  have same : found = actual := Option.some.inj (normalized.symm.trans known)
  exact same ▸ within

theorem normalized_argument_source_bound {func : Func} {vt : Array (Option VTy)}
    {provenance upper : Prov} {state : State} {value : ValueId} {source actual : List RootRef}
    (canonical : state.CanonicalWithin func vt provenance)
    (closed : ∀ index root, root ∈ func.parameterRoots index → root = .param index ∨ ∃ global, root = .global global)
    (bounded : value < func.numValues)
    (below : rootsAt provenance.vals value ⊆ rootsAt upper.vals value)
    (refined : GIR.RootsRefine func (rootsAt upper.vals value) source)
    (known : normalize func (flowAt state.values value) = some actual) :
    actual ⊆ source.flatMap func.expandParameterRoot := by
  have stateBound : value < state.values.size := by rw [canonical.shape.values]; exact bounded
  exact normalized_symbolic_source_bound closed
    ((canonical.values value stateBound).refine closed (refined.actual_mono below)) known

theorem call_content_source_bound {module : GIR.Module} {func callee : Func}
    {vt : Array (Option VTy)} {provenance : Prov} {state : State} {results : Array (List RootRef)}
    {block : GIR.Block} {result calleeId index : Nat} {arguments : List ValueId} {origin : Option OriginId}
    {declared mapped : List RootRef} {sourceRoots : List (List RootRef)}
    (native : FunctionCanonicalFacts module func vt provenance results)
    (canonical : state.CanonicalWithin func vt provenance)
    (member : block ∈ func.blocks.toList)
    (called : Inst.def result (.call calleeId arguments origin) ∈ block.insts)
    (calleeAt : module.funcs[calleeId]? = some callee)
    (calleeRoots : FunctionRootFacts callee)
    (annotation : callee.roots.contents.find? (·.1 == index) = some (index, declared))
    (mapping : Core.mapResultRoots sourceRoots [] declared = .ok mapped)
    (argumentBounds : ∀ parameter value source, RootRef.param parameter ∈ declared →
      arguments[parameter]? = some value → sourceRoots[parameter]? = some source →
      GIR.RootsRefine func (rootsAt provenance.vals value) source)
    (available : CallObservationReady callee func state arguments) :
    ∃ value actual, arguments[index]? = some value ∧
      normalize func (content func state (flowAt state.values value)) = some actual ∧
      actual ⊆ mapped.flatMap func.expandParameterRoot := by
  obtain ⟨site⟩ := native.calls block member result calleeId arguments origin called
  have calleeEq : site.callee = callee := Option.some.inj (site.calleeAt.symm.trans calleeAt)
  have reference := calleeRoots.contentTypes index declared annotation
  have bounded : index < callee.params.length := by
    cases formal : callee.params[index]? with
    | none => simp [formal] at reference
    | some type => exact (List.getElem?_eq_some_iff.mp formal).1
  have bounds := canonical.callContentArguments calleeAt native.roots.closed native.roots.parameters
    calleeRoots.contentTypes (by simpa only [calleeEq] using site.references)
    (by simpa only [calleeEq] using site.observed) native.admitted member called
  obtain ⟨value, row, refined⟩ := bounds index declared bounded annotation
  obtain ⟨observed, actual, observedAt, known⟩ := available.contents index declared bounded annotation
  have same : observed = value := Option.some.inj (observedAt.symm.trans row)
  subst observed
  refine ⟨value, actual, row, known, ?_⟩
  have mappedBound := AdmittedSourceCalls.mapRawContentRoots_refines mapping argumentBounds
  exact normalized_symbolic_source_bound native.roots.closed
    (refined.refine native.roots.closed mappedBound) known

end Goose.Lower.Validation.ReplacementContentFlowSource
