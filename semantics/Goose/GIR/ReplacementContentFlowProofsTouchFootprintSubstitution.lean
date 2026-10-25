import Goose.GIR.ReplacementContentFlowProofsTouchFootprintCalls

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem passable_wholeOwnerReference {actual formal : Ty}
    (passing : actual.passableTo formal = true)
    (interior : wholeOwnerReference (.data formal) = false) :
    wholeOwnerReference (.data actual) = false := by
  cases actual <;> try rfl
  rename_i mutability payload
  cases formal <;> simp_all [Ty.passableTo,wholeOwnerReference,Bool.and_eq_true,beq_iff_eq]

theorem State.TouchFootprint.call_parameter {module : Module} {func : Func}
    {types : Array (Option VTy)} {provenance : Prov} {results : Array (List RootRef)}
    {policy : Atom → Prop} {state : State} {fn value : ValueId} {args : List ValueId}
    {origin : Option OriginId} {block : Block} {index : Nat} {formal : Ty}
    (before : state.TouchFootprint func types policy)
    (shape : state.Shape func)
    (facts : FunctionCanonicalFacts module func types provenance results)
    (site : CallSiteFacts module func types provenance fn args)
    (formalAt : site.callee.params[index]? = some formal)
    (interior : wholeOwnerReference (.data formal) = false)
    (blockMember : block ∈ func.blocks.toList)
    (called : Inst.def value (.call fn args origin) ∈ block.insts) :
    ((args[index]?).map (flowAt state.values ·) |>.getD .unknown).AtomsWithin
      (TouchFootprintAtom func policy) := by
  obtain ⟨argument,argumentAt,bounded⟩ := site.arguments index (List.getElem?_eq_some_iff.mp formalAt).1
  have typed := facts.typing block blockMember _ called
  cases typed with
  | definition value op type typed canonical =>
      have signature : ({module.tyEnv func with vals := types} : TyEnv).sigs[fn]? =
          some (site.callee.params,site.callee.results) := by
        change (module.funcs.map (fun callee => (callee.params,callee.results)))[fn]? = some _
        simp [site.calleeAt]
      obtain ⟨actual,actualAt,passing⟩ := call_argument_passable signature typed formalAt argumentAt
      simp only [argumentAt,Option.map_some,Option.getD_some]
      exact before.values argument (by rw [shape.values]; exact bounded) (.data actual)
        (TyEnv.dataTy_known actualAt) (passable_wholeOwnerReference passing interior)

theorem State.TouchFootprint.call_contents {module : Module} {func : Func}
    {types : Array (Option VTy)} {provenance : Prov} {policy : Atom → Prop} {state : State}
    {fn : FnId} {args : List ValueId} {index : Nat}
    (before : state.TouchFootprint func types policy)
    (canonical : state.CanonicalWithin func types provenance)
    (site : CallSiteFacts module func types provenance fn args)
    (parameters : ∀ type ∈ func.params, type.paramOk = true)
    (calleeRoots : FunctionRootFacts site.callee)
    (normalizable : (normalizeAtom site.callee (.contents index)).isSome = true) :
    ((args[index]?).map (fun value => Model.content func state (flowAt state.values value)) |>.getD .unknown).AtomsWithin
      (TouchFootprintAtom func policy) := by
  cases annotation : site.callee.roots.contents.find? (·.1 == index) with
  | none => simp [normalizeAtom,annotation] at normalizable
  | some row =>
      have identity : row.1 = index := by
        simpa only [beq_iff_eq] using Array.find?_some annotation
      obtain ⟨selected,ceiling⟩ := row
      change selected = index at identity
      subst selected
      have reference := calleeRoots.contentTypes index ceiling annotation
      cases formal : site.callee.params[index]? with
      | none => simp [formal] at reference
      | some type =>
          have slice : type.isRefSlice = true := by simpa only [formal,Option.any_some] using reference
          obtain ⟨outer,inner,element,same,flat⟩ := isRefSlice_shape slice
          subst type
          obtain ⟨argument,actualMutability,argumentAt,typed,bounded⟩ := site.references index outer _ formal
          have physical := canonical.holderValues argument
            (by rw [canonical.shape.values]; exact bounded) actualMutability (.slice inner element) typed rfl
          simp only [argumentAt,Option.map_some,Option.getD_some]
          exact before.content canonical.shape parameters physical rfl rfl

theorem State.TouchFootprint.substitute {module : Module} {func : Func}
    {types : Array (Option VTy)} {provenance : Prov} {results : Array (List RootRef)}
    {policy calleePolicy : Atom → Prop} {state : State} {fn value : ValueId} {args : List ValueId}
    {origin : Option OriginId} {block : Block} {roots : Roots}
    (before : state.TouchFootprint func types policy)
    (canonical : state.CanonicalWithin func types provenance)
    (facts : FunctionCanonicalFacts module func types provenance results)
    (site : CallSiteFacts module func types provenance fn args)
    (calleeRoots : FunctionRootFacts site.callee)
    (bounded : roots.AtomsWithin (TouchFootprintAtom site.callee calleePolicy))
    (supported : roots.Supported (atomUniverse module site.callee))
    (normalizable : roots.AtomsWithin (fun atom => (normalizeAtom site.callee atom).isSome = true))
    (external : roots.AtomsWithin (fun atom => ∀ slot, atom ≠ .local slot))
    (policyMapped : ∀ atom, calleePolicy atom → atom ∈ atomUniverse module site.callee →
      (normalizeAtom site.callee atom).isSome = true → (∀ slot, atom ≠ .local slot) →
      (match atom with
        | .global global => Roots.known [.global global]
        | .param index => (args[index]?).map (flowAt state.values ·) |>.getD .unknown
        | .contents index => (args[index]?).map (fun argument => Model.content func state (flowAt state.values argument)) |>.getD .unknown
        | .local _ => .unknown).AtomsWithin (TouchFootprintAtom func policy))
    (blockMember : block ∈ func.blocks.toList)
    (called : Inst.def value (.call fn args origin) ∈ block.insts) :
    (Model.substitute func state args roots).AtomsWithin (TouchFootprintAtom func policy) := by
  have all : roots.AtomsWithin (fun atom => TouchFootprintAtom site.callee calleePolicy atom ∧
      atom ∈ atomUniverse module site.callee ∧ (normalizeAtom site.callee atom).isSome = true ∧
        ∀ slot, atom ≠ .local slot) := by
    cases roots with
    | pending => trivial
    | unknown => exact False.elim bounded
    | known atoms =>
        intro atom member
        exact ⟨bounded atom member,supported.2 member,normalizable atom member,external atom member⟩
  apply substitute_atomsWithin all
  intro atom ⟨allowed,support,row,apart⟩
  rcases allowed with admitted | ⟨slot,same⟩ | ⟨index,same⟩ | ⟨index,type,same,formal,interior⟩
  · exact policyMapped atom admitted support row apart
  · subst atom
    exact False.elim (apart slot rfl)
  · subst atom
    exact before.call_contents canonical site facts.roots.parameters calleeRoots row
  · subst atom
    exact before.call_parameter canonical.shape facts site formal interior blockMember called

#print axioms State.TouchFootprint.call_parameter
#print axioms State.TouchFootprint.call_contents

end Goose.GIR.ReplacementContentFlow.Model
