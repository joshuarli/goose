import Goose.GIR.ReplacementContentFlowProofsSliceSubstitution

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem substitute_touchValues (func : Func) (vt : Array (Option VTy)) (state : State)
    (accesses args : List ValueId) (roots : Roots) :
    substitute func (touchValues vt state accesses) args roots = substitute func state args roots := rfl

theorem State.CanonicalWithin.call_touched_eq {module : Module} {states : Array State}
    {func : Func} {vt : Array (Option VTy)} {provenance : Prov} {state effects : State}
    {fn : FnId} {args : List ValueId}
    (before : state.CanonicalWithin func vt provenance)
    (site : CallSiteFacts module func vt provenance fn args) (effectsAt : states[fn]? = some effects) :
    (Model.callState module states func state fn args).2.touched =
      state.touched.join (substitute func state args (publicTouches effects.touched)) := by
  apply callState_touched_of_holders site.calleeAt effectsAt
  intro type index member reference
  have formal := List.mem_zipIdx_iff_getElem?.mp member
  obtain ⟨outer,inner,element,same,flat⟩ := isRefSlice_shape reference
  subst type
  obtain ⟨argument,actualMutability,argumentAt,canonical,bounded⟩ := site.references index outer _ formal
  refine ⟨argument,.slice inner element,rootsAt provenance.vals argument,argumentAt,?_⟩
  exact before.holderValues argument (by rw [before.shape.values]; exact bounded)
    actualMutability (.slice inner element) canonical rfl

theorem fixed_call_touches_atomsWithin {module : Module} {states : Array State}
    {func : Func} {vt : Array (Option VTy)} {provenance : Prov} {state effects : State}
    {fn value : ValueId} {args : List ValueId} {origin : Option OriginId} {predicate : Atom → Prop}
    (before : state.CanonicalWithin func vt provenance)
    (site : CallSiteFacts module func vt provenance fn args) (effectsAt : states[fn]? = some effects)
    (fixed : step module states func vt state (.def value (.call fn args origin)) = state)
    (bounded : state.touched.AtomsWithin predicate) :
    (substitute func state args (publicTouches effects.touched)).AtomsWithin predicate := by
  have same := congrArg State.touched fixed
  have touched := before.call_touched_eq site effectsAt
  have exactTouch : state.touched.join
      (substitute func state args (publicTouches effects.touched)) = state.touched := by
    simpa only [step,Id.run_pure,interiorLoadedResults,loadedResults,List.filter_nil,
      touchValues,List.foldl_nil] using touched.symm.trans same
  rw [← exactTouch] at bounded
  exact bounded.join_right

theorem call_slice_argument_type {module : Module} {func : Func}
    {vt : Array (Option VTy)} {provenance : Prov} {results : Array (List RootRef)}
    {fn value : ValueId} {args : List ValueId} {origin : Option OriginId}
    (facts : FunctionCanonicalFacts module func vt provenance results)
    (site : CallSiteFacts module func vt provenance fn args)
    {block : Block} (blockMember : block ∈ func.blocks.toList)
    (called : Inst.def value (.call fn args origin) ∈ block.insts)
    {index : Nat} {mutability : Mutability} {element : Ty}
    (formal : site.callee.params[index]? = some (.slice mutability element))
    {argument : ValueId} (actual : args[index]? = some argument) :
    ∃ actualMutability, vt[argument]? = some (some (.data (.slice actualMutability element))) ∧
      argument < func.numValues := by
  have typed := facts.typing block blockMember _ called
  cases typed with
  | definition value op type typed canonical =>
      have signature : ({module.tyEnv func with vals := vt} : TyEnv).sigs[fn]? =
          some (site.callee.params,site.callee.results) := by
        change (module.funcs.map (fun callee => (callee.params,callee.results)))[fn]? = some _
        simp [site.calleeAt]
      obtain ⟨argumentType,argumentAt,passing⟩ := call_argument_passable signature typed formal actual
      have bounded := facts.uses block blockMember _ called argument
        (by simpa [Inst.uses,Op.uses] using List.mem_of_getElem? actual)
      cases argumentType with
      | slice actualMutability actualElement =>
          have same : actualElement = element := by
            have pieces := passing
            simp only [Ty.passableTo, Bool.and_eq_true] at pieces
            exact beq_iff_eq.mp pieces.1
          subst actualElement
          exact ⟨actualMutability,TyEnv.dataTy_known argumentAt,bounded⟩
      | _ => simp [Ty.passableTo] at passing

#print axioms fixed_call_touches_atomsWithin
#print axioms call_slice_argument_type

end Goose.GIR.ReplacementContentFlow.Model
