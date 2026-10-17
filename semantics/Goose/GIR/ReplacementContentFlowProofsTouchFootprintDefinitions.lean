import Goose.GIR.ReplacementContentFlowProofsTouchFootprintMemory

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem State.TouchFootprint.definitionResult {module : Module} {func : Func}
    {types : Array (Option VTy)} {provenance : Prov} {results : Array (List RootRef)}
    {policy : Atom → Prop} {state : State} {value : ValueId} {op : Op} {type : VTy}
    (before : state.TouchFootprint func types policy)
    (canonical : state.CanonicalWithin func types provenance)
    (facts : FunctionCanonicalFacts module func types provenance results)
    (typed : op.resultTy {module.tyEnv func with vals := types} = .ok type)
    (valueType : types[value]? = some (some type)) (interior : wholeOwnerReference type = false)
    (ordinary : ∀ fn args origin, op ≠ .call fn args origin)
    (sourceBound : ∀ source, BackingOp op source →
      (flowAt state.values source).AtomsWithin (TouchFootprintAtom func policy))
    (globalBound : ∀ index payload kind mutability,
      (module.tyEnv func).globals[index]? = some (payload,kind) →
      wholeOwnerReference (.data (.ref mutability payload)) = false →
      TouchFootprintAtom func policy (.global index))
    (uses : ∀ source ∈ (.def value op : Inst).uses, source < func.numValues) :
    (result func types state value op).AtomsWithin (TouchFootprintAtom func policy) := by
  by_cases reference : type.refLike = true
  · have like : valRefLike types value = true := by simp [valRefLike,valueType,reference]
    have classified := DefinitionTyping.of_resultTy (env := {module.tyEnv func with vals := types})
      facts.valuesShape facts.globalStorage facts.fields op typed
    cases classified with
    | scalar op type ordinary scalar => rw [scalar] at reference; cases reference
    | slot index storage mutability row =>
        simp only [result,like,Bool.not_true,Bool.false_eq_true,ite_false,Roots.AtomsWithin,List.mem_singleton]
        intro atom same
        subst atom
        exact TouchFootprintAtom.local func policy index
    | global index payload kind mutability row _ =>
        simp only [result,like,Bool.not_true,Bool.false_eq_true,ite_false,Roots.AtomsWithin,List.mem_singleton]
        intro atom same
        subst atom
        exact globalBound index payload kind mutability row interior
    | load source mutability payload sourceType =>
        have sourceRow := TyEnv.refTy_known sourceType
        have sourceBound : source < state.values.size := by
          rw [canonical.shape.values]
          exact uses source (by simp [Inst.uses,Op.uses])
        have physical := canonical.holderValues source sourceBound mutability payload sourceRow reference
        simpa only [result,like,Bool.not_true,Bool.false_eq_true,ite_false] using
          before.content canonical.shape facts.roots.parameters physical reference interior
    | freeze source mutability payload sourceType =>
        have sourceRow := TyEnv.refTy_known sourceType
        have sourceBound : source < state.values.size := by
          rw [canonical.shape.values]
          exact uses source (by simp [Inst.uses,Op.uses])
        simpa only [result,like,Bool.not_true,Bool.false_eq_true,ite_false] using
          before.values source sourceBound (.data (.ref mutability payload)) sourceRow interior
    | borrow source mutability payload sourceType owner =>
        simp only [wholeOwnerReference,owner] at interior
        cases interior
    | backing op source type backing _ =>
        rw [backing.result like state]
        exact sourceBound source backing
    | call fn args origin type => exact False.elim (ordinary fn args origin rfl)
  · have like : valRefLike types value = false := by simp [valRefLike,valueType,reference]
    simp [result,like,Roots.AtomsWithin]

theorem interiorLoadedResults_type {types : Array (Option VTy)} {value source : ValueId}
    {op : Op} {type : VTy} (member : source ∈ interiorLoadedResults types (.def value op))
    (typed : types[source]? = some (some type)) :
    source = value ∧ wholeOwnerReference type = false := by
  have loaded := (List.mem_filter.mp member).1
  have same : source = value := by cases op <;> simp_all [loadedResults]
  refine ⟨same,?_⟩
  have accepted := (List.mem_filter.mp member).2
  cases type with
  | view mutability element => rfl
  | data payload =>
      cases payload <;> try rfl
      rename_i mutability target
      cases target <;> simp_all [interiorLoadedResults,wholeOwnerReference,Ty.ownerElem?,
        Ty.interiorTarget?,Ty.isRefLike]

theorem State.TouchFootprint.noncallDefinition {module : Module} {states : Array State} {func : Func}
    {types : Array (Option VTy)} {provenance : Prov} {results : Array (List RootRef)}
    {policy : Atom → Prop} {state : State} {value : ValueId} {op : Op} {type : VTy}
    (before : state.TouchFootprint func types policy)
    (canonical : state.CanonicalWithin func types provenance)
    (facts : FunctionCanonicalFacts module func types provenance results)
    (typed : op.resultTy {module.tyEnv func with vals := types} = .ok type)
    (valueType : types[value]? = some (some type)) (valueBound : value < func.numValues)
    (ordinary : ∀ fn args origin, op ≠ .call fn args origin)
    (sourceBound : ∀ source, BackingOp op source →
      (flowAt state.values source).AtomsWithin (TouchFootprintAtom func policy))
    (globalBound : ∀ index payload kind mutability,
      (module.tyEnv func).globals[index]? = some (payload,kind) →
      wholeOwnerReference (.data (.ref mutability payload)) = false →
      TouchFootprintAtom func policy (.global index))
    (accessed : ∀ source ∈ accessOperands (.def value op), valRefLike types source = true →
      (flowAt state.values source).AtomsWithin (TouchFootprintAtom func policy))
    (uses : ∀ source ∈ (.def value op : Inst).uses, source < func.numValues) :
    (step module states func types state (.def value op)).TouchFootprint func types policy := by
  let exposed := Model.touchValues types state (accessOperands (.def value op))
  have exposedFootprint : exposed.TouchFootprint func types policy := before.touchValues accessed
  have exposedCanonical : exposed.CanonicalWithin func types provenance := canonical.touchValues _
  have assigned : ({ exposed with
       values := addFlow exposed.values value (result func types exposed value op) } : State).TouchFootprint func types policy := by
    apply exposedFootprint.addValue
    intro actual actualType interior
    have same : actual = type := Option.some.inj (Option.some.inj (actualType.symm.trans valueType))
    subst actual
    exact exposedFootprint.definitionResult exposedCanonical facts typed valueType interior ordinary
      sourceBound globalBound uses
  rw [step_def_noncall _ _ _ _ _ _ _ ordinary]
  apply assigned.touchValues
  intro source loaded reference
  have sourceType : ∃ actual, types[source]? = some (some actual) := by
    cases found : types[source]? with
    | none => simp [valRefLike,found] at reference
    | some row => cases row with
      | none => simp [valRefLike,found] at reference
      | some actual => exact ⟨actual,rfl⟩
  obtain ⟨actual,actualType⟩ := sourceType
  obtain ⟨same,interior⟩ := interiorLoadedResults_type loaded actualType
  have bounded : source < (addFlow exposed.values value (result func types exposed value op)).size := by
    simpa only [addFlow,Array.size_set!,exposed,touchValues_values,canonical.shape.values,same] using valueBound
  exact assigned.values source bounded actual actualType interior

#print axioms State.TouchFootprint.definitionResult

end Goose.GIR.ReplacementContentFlow.Model
