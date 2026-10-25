import Goose.GIR.ReplacementContentFlowProofsSliceDependencyAtoms

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem callQuery_slice_argument_atoms {module : Module} {states : Array State} {func : Func}
    {types : Array (Option VTy)} {provenance : Prov} {results : Array (List RootRef)} {state : State}
    {fn value : ValueId} {args : List ValueId} {origin : Option OriginId} {actual : List RootRef}
    (facts : FunctionCanonicalFacts module func types provenance results)
    (site : CallSiteFacts module func types provenance fn args)
    (known : callQuery module func types states state fn args = some actual)
    {block : Block} (blockMember : block ∈ func.blocks.toList)
    (called : Inst.def value (.call fn args origin) ∈ block.insts) :
    ∀ (index : Nat) (mutability : Mutability) (element : Ty), site.callee.params[index]? = some (.slice mutability element) →
      ∀ argument, args[index]? = some argument →
        (flowAt state.values argument).AtomsWithin (OwnerDependencyAtom module func actual) := by
  intro index mutability element formal argument argumentAt
  have typed := facts.typing block blockMember _ called
  cases typed with
  | definition value op type typed canonical =>
      have signature : ({module.tyEnv func with vals := types} : TyEnv).sigs[fn]? =
          some (site.callee.params,site.callee.results) := by
        change (module.funcs.map (fun callee => (callee.params,callee.results)))[fn]? = some _
        simp [site.calleeAt]
      have reference := call_slice_argument_refLike signature typed formal argumentAt
      obtain ⟨roots,rootsAt,within⟩ := callQuery_argument_dependencies known (List.mem_of_getElem? argumentAt) reference
      exact (ownerDependencies_atomsWithin rootsAt).mono (fun _ bounded => bounded.mono within)

theorem call_slice_return_observed {module : Module} {states : Array State} {func : Func}
    {types calleeTypes : Array (Option VTy)} {provenance calleeProvenance : Prov}
    {results : Array (List RootRef)} {before final effects : State}
    {fn value : ValueId} {args : List ValueId} {origin : Option OriginId} {observed : List Atom}
    {mutability : Mutability} {element : Ty} {actual : List RootRef}
    (facts : FunctionCanonicalFacts module func types provenance results)
    (site : CallSiteFacts module func types provenance fn args) (effectsAt : states[fn]? = some effects)
    (calleeRoots : FunctionRootFacts site.callee)
    (calleeResult : site.callee.results = [.slice mutability element])
    (calleeCanonical : effects.CanonicalWithin site.callee calleeTypes calleeProvenance)
    (calleeOrigins : effects.SliceOrigins site.callee calleeTypes observed)
    (supported : effects.Supported (atomUniverse module site.callee))
    (touchRows : effects.touched.AtomsWithin (fun atom => (normalizeAtom site.callee atom).isSome = true))
    (touches : effects.touched = .known observed)
    (growth : before.Extends final) (available : CallObservationReady site.callee func final args)
    (known : callQuery module func types states final fn args = some actual)
    {block : Block} (blockMember : block ∈ func.blocks.toList)
    (called : Inst.def value (.call fn args origin) ∈ block.insts) :
    (substitute func before args effects.returned).AtomsWithin (OwnerDependencyAtom module func actual) := by
  have original := calleeOrigins.returned mutability element calleeResult
  have external := (calleeCanonical.returned _ calleeResult rfl).externalAtoms calleeRoots.resultExternal
  obtain ⟨touched,touchedAt,touchedWithin⟩ := callQuery_touch_dependencies known effectsAt
  have observedBound := (ownerDependencies_atomsWithin touchedAt).mono
    (fun _ bounded => bounded.mono touchedWithin)
  rw [touches] at observedBound touchRows
  have touchSupport := supported.touched
  rw [touches] at touchSupport
  exact substitute_slice_origins_final growth original external supported.returned touchRows touchSupport available
    observedBound (callQuery_slice_argument_atoms facts site known blockMember called)

#print axioms call_slice_return_observed

end Goose.GIR.ReplacementContentFlow.Model
