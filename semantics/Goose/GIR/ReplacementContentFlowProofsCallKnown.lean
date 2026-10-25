import Goose.GIR.ReplacementContentFlowProofsSliceSubstitution
import Goose.GIR.ReplacementContentFlowProofsCallArgumentObservation

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem normalize_atomsWithin {func : Func} {roots : Roots} {actual : List RootRef}
    (known : normalize func roots = some actual) :
    roots.AtomsWithin (fun atom => (normalizeAtom func atom).isSome = true) := by
  obtain ⟨atoms,rfl⟩ := normalize_known_shape known
  intro atom member
  obtain ⟨mapped,mappedAt,_⟩ := (normalize_fold_atoms func atoms [] actual known).2 atom member
  exact Option.isSome_iff_exists.mpr ⟨mapped,mappedAt⟩

theorem substitute_public_normalized {module : Module} {callee func : Func}
    {state : State} {args : List ValueId} {touches : Roots} {actual : List RootRef}
    (known : normalize callee touches = some actual)
    (supported : touches.Supported (atomUniverse module callee))
    (available : CallObservationReady callee func state args) :
    ∃ roots, normalize func (substitute func state args (publicTouches touches)) = some roots := by
  have rows := normalize_atomsWithin known
  have bounded := substitute_normalizableAtoms (publicTouches_normalizableAtoms rows)
    (publicTouches_supported supported) (by
      intro index bound
      obtain ⟨value,roots,valueAt,known⟩ := available.arguments index bound
      exact ⟨value,valueAt,normalize_atomsWithin known⟩) (by
      intro index row bound rowAt
      obtain ⟨value,roots,valueAt,known⟩ := available.contents index row bound rowAt
      exact ⟨value,valueAt,normalize_atomsWithin known⟩)
  obtain ⟨atoms,rfl⟩ := normalize_known_shape known
  obtain ⟨exposed,output,publicAt,substituted⟩ := substitute_public_known rows supported available
  apply bounded.normalize
  rw [publicAt,substituted]
  intro same
  cases same

private theorem argument_fold_known (module : Module) (func : Func)
    (types : Array (Option VTy)) (state : State) (args : List ValueId)
    (ready : ∀ value ∈ args, ∃ roots, normalize func (flowAt state.values value) = some roots)
    (initial : List RootRef) :
    ∃ roots, args.foldlM (fun roots value => do
      if !valRefLike types value then pure roots else
        let actual ← ownerDependencies module func (flowAt state.values value)
        pure (unionRoots roots actual)) initial = some roots := by
  induction args generalizing initial with
  | nil => exact ⟨initial,rfl⟩
  | cons value rest ih =>
      by_cases reference : valRefLike types value = true
      · obtain ⟨roots,known⟩ := ready value (by simp)
        obtain ⟨dependencies,dependenciesAt,_⟩ := ownerDependencies_known (module := module) known
        obtain ⟨output,outputAt⟩ := ih (fun next member => ready next (by simp [member]))
          (unionRoots initial dependencies)
        exact ⟨output,by simpa [List.foldlM_cons,reference,dependenciesAt] using outputAt⟩
      · obtain ⟨output,outputAt⟩ := ih (fun next member => ready next (by simp [member])) initial
        exact ⟨output,by simpa [List.foldlM_cons,reference] using outputAt⟩

theorem callQuery_known {module : Module} {callee func : Func}
    {types : Array (Option VTy)} {states : Array State} {state effects : State}
    {fn value : ValueId} {args : List ValueId} {origin : Option OriginId} {touched : List RootRef}
    (checked : checkInstruction module func types state (.def value (.call fn args origin)) = true)
    (_calleeAt : module.funcs[fn]? = some callee)
    (effectsAt : states[fn]? = some effects)
    (arity : args.length = callee.params.length)
    (known : normalize callee effects.touched = some touched)
    (supported : effects.touched.Supported (atomUniverse module callee))
    (available : CallObservationReady callee func state args) :
    ∃ roots, callQuery module func types states state fn args = some roots := by
  have parts := checked
  simp only [checkInstruction,Bool.and_eq_true] at parts
  have calls : checkCall module func state fn args = true := parts.2.2
  have typed : (Op.call fn args none |>.resultTy ({module.tyEnv func with vals := types} : TyEnv)).toOption.isNone = false := by
    have typeKnown := parts.2.1
    change (Op.call fn args origin |>.resultTy ({module.tyEnv func with vals := types} : TyEnv)).toOption.isNone = false
    cases resultAt : (Op.call fn args origin |>.resultTy ({module.tyEnv func with vals := types} : TyEnv)).toOption with
    | none => simp [resultAt] at typeKnown
    | some type => rfl
  have arguments : ∀ argument ∈ args, ∃ roots, normalize func (flowAt state.values argument) = some roots := by
    intro argument member
    obtain ⟨index,bound,elementAt⟩ := List.mem_iff_getElem.mp member
    obtain ⟨value,roots,valueAt,known⟩ := available.arguments index (by omega)
    have actual : args[index]? = some argument := by simp [List.getElem?_eq_getElem bound,elementAt]
    have same := Option.some.inj (valueAt.symm.trans actual)
    exact ⟨roots,by simpa only [same] using known⟩
  obtain ⟨argumentRoots,argumentsAt⟩ := argument_fold_known module func types state args arguments []
  obtain ⟨touchRoots,touchesAt⟩ := substitute_public_normalized known supported available
  obtain ⟨dependencies,dependenciesAt,_⟩ := ownerDependencies_known (module := module) touchesAt
  refine ⟨unionRoots argumentRoots dependencies,?_⟩
  simp only [callQuery,calls,typed,Bool.not_true,Bool.false_or,Bool.false_eq_true,ite_false,
    effectsAt,pure,bind,Option.bind_some]
  simp only [pure,bind] at argumentsAt
  rw [argumentsAt]
  simp only [Option.bind_some,dependenciesAt]

theorem check_instruction {module : Module} {func : Func} {types : Array (Option VTy)}
    {state : State} {block : Block} {inst : Inst}
    (checked : check module func types state = true)
    (blockMember : block ∈ func.blocks.toList) (member : inst ∈ block.insts) :
    checkInstruction module func types state inst = true := by
  simp only [check,Bool.and_eq_true] at checked
  obtain ⟨index,blockAt⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp blockMember)
  obtain ⟨bound,same⟩ := Array.getElem?_eq_some_iff.mp blockAt
  have row := (Array.all_eq_true.mp checked.2) index bound
  rw [same] at row
  exact List.all_eq_true.mp (Bool.and_eq_true_iff.mp row).2 inst member

#print axioms normalize_atomsWithin
#print axioms substitute_public_normalized
#print axioms callQuery_known
#print axioms check_instruction

end Goose.GIR.ReplacementContentFlow.Model

namespace Goose.GIR

open Goose.Core ReplacementContentFlow.Model

theorem ReplacementContentFlow.forFunction_call_known {cache : ReplacementContentFlow}
    {func callee : Func} {types : Array (Option VTy)} {states : Array State} {state effects : State}
    {fn value : ValueId} {args : List ValueId} {origin : Option OriginId} {touched : List RootRef}
    (built : (cache.forFunction func types).model = some state)
    (statesAt : cache.model = some states)
    {block : Block} (blockMember : block ∈ func.blocks.toList)
    (called : Inst.def value (.call fn args origin) ∈ block.insts)
    (calleeAt : cache.source.funcs[fn]? = some callee)
    (effectsAt : states[fn]? = some effects)
    (arity : args.length = callee.params.length)
    (known : normalize callee effects.touched = some touched)
    (supported : effects.touched.Supported (atomUniverse cache.source callee))
    (available : CallObservationReady callee func state args) :
    ∃ roots, (cache.forFunction func types).call fn args = some roots := by
  obtain ⟨canonical,_,_,_,checked⟩ := ReplacementContentFlow.forFunction_model_checked built
  subst types
  obtain ⟨roots,query⟩ := callQuery_known (check_instruction checked blockMember called)
    calleeAt effectsAt arity known supported available
  refine ⟨roots,?_⟩
  rw [ReplacementFunctionFlow.call_model]
  change ((cache.forFunction func (func.valueTypes cache.source)).model.bind fun current =>
    cache.model.bind fun currentStates => callQuery cache.source func (func.valueTypes cache.source)
      currentStates current fn args) = some roots
  simp only [built,statesAt,Option.bind_some,query]

#print axioms ReplacementContentFlow.forFunction_call_known

end Goose.GIR
