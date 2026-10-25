import Goose.GIR.ReplacementContentFlowProofsSliceInvariant

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem step_noncall_values {module : Module} {states : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {value : ValueId} {op : Op}
    (ordinary : ∀ fn args origin, op ≠ .call fn args origin) :
    (step module states func types state (.def value op)).values =
      addFlow state.values value (result func types state value op) := by
  rw [step_def_noncall _ _ _ _ _ _ _ ordinary]
  simp only [touchValues_values,result_touchValues]

theorem State.SliceOrigins.noncallDefinition {module : Module} {states finalStates : Array State} {func : Func}
    {types : Array (Option VTy)} {provenance : Prov} {results : Array (List RootRef)}
    {state final : State} {value : ValueId} {op : Op} {type : VTy} {observed : List Atom}
    (before : state.SliceOrigins func types observed)
    (canonical : state.CanonicalWithin func types provenance)
    (facts : FunctionCanonicalFacts module func types provenance results)
    (typed : op.resultTy {module.tyEnv func with vals := types} = .ok type)
    (valueType : types[value]? = some (some type)) (valueBound : value < func.numValues)
    (ordinary : ∀ fn args origin, op ≠ .call fn args origin)
    (growth : state.Extends final)
    (afterGrowth : (step module states func types state (.def value op)).Extends final)
    (fixed : step module finalStates func types final (.def value op) = final)
    (touches : final.touched = .known observed) :
    (step module states func types state (.def value op)).SliceOrigins func types observed := by
  have finalTouch : final.touched.AtomsWithin (SliceOrigin func observed) := by
    rw [touches]
    intro atom member
    exact Or.inl member
  constructor
  · rw [step_noncall_values ordinary]
    apply before.values.addFlow
    intro mutability element sliceType
    have same : type = .data (.slice mutability element) := Option.some.inj (Option.some.inj (valueType.symm.trans sliceType))
    subst type
    have like : valRefLike types value = true := by simp [valRefLike,valueType,VTy.refLike,Ty.isRefLike]
    have classified := SliceDefinition.of_resultTy (env := {module.tyEnv func with vals := types})
      facts.valuesShape facts.globalStorage facts.fields op typed
    cases classified with
    | load address =>
        have finalValue := fixed_slice_load_atomsWithin fixed valueType finalTouch
        have introduced := (afterGrowth.values.values value).atomsWithin finalValue
        change (flowAt (step module states func types state (.def value (.load address))).values value).AtomsWithin _ at introduced
        rw [step_noncall_values ordinary,flowAt_addFlow] at introduced
        have bounded : value < state.values.size := by rw [canonical.shape.values]; exact valueBound
        simp only [bounded,and_self,ite_true] at introduced
        exact introduced.join_right
    | backing op source backing accessed reference =>
        have finalSource := fixed_step_access_atomsWithin fixed
          (by intro actual fn args origin same; exact ordinary fn args origin (Inst.def.inj same).2)
          (accessed value) reference finalTouch
        rw [backing.result like state]
        exact (growth.values.values source).atomsWithin finalSource
    | call fn args origin => exact False.elim (ordinary fn args origin rfl)
  · intro mutability element result
    simpa only [step_returned] using before.returned mutability element result

theorem State.SliceOrigins.of_components {func : Func} {types : Array (Option VTy)} {observed : List Atom}
    {before after : State} (bounded : before.SliceOrigins func types observed)
    (values : after.values = before.values) (returned : after.returned = before.returned) :
    after.SliceOrigins func types observed := by
  constructor
  · rw [values]; exact bounded.values
  · rw [returned]; exact bounded.returned

theorem State.SliceOrigins.edge {func : Func} {types : Array (Option VTy)} {observed : List Atom}
    {state : State} {target : BlockId} {args : List ValueId} {block : Block}
    (before : state.SliceOrigins func types observed) (size : state.values.size = func.numValues)
    (targetAt : func.blocks[target]? = some block)
    (passing : ∀ parameter argument, (parameter,argument) ∈ block.params.zip args →
      types[parameter.1]? = types[argument]? ∧ argument < func.numValues) :
    (Model.edge func state target args).SliceOrigins func types observed := by
  simp only [Model.edge,targetAt]
  have result : ((block.params.zip args).foldl (fun state pair =>
      { state with values := addFlow state.values pair.1.1 (flowAt state.values pair.2) }) state).SliceOrigins func types observed ∧
      ((block.params.zip args).foldl (fun state pair =>
        { state with values := addFlow state.values pair.1.1 (flowAt state.values pair.2) }) state).values.size = func.numValues := by
    apply List.foldlRecOn (motive := fun current : State => current.SliceOrigins func types observed ∧
      current.values.size = func.numValues) (block.params.zip args) _ ⟨before,size⟩
    intro current valid pair member
    obtain ⟨same,bounded⟩ := passing pair.1 pair.2 member
    constructor
    · constructor
      · apply valid.1.values.addFlow
        intro mutability element type
        rw [same] at type
        exact valid.1.values pair.2 (by rw [valid.2]; exact bounded) mutability element type
      · exact valid.1.returned
    · simpa [ReplacementContentFlow.Model.addFlow] using valid.2
  exact result.1

theorem State.SliceOrigins.ret {module : Module} {states : Array State} {func : Func}
    {types : Array (Option VTy)} {observed : List Atom} {state : State} {value : ValueId}
    {origin : Option OriginId} {type : Ty}
    (before : state.SliceOrigins func types observed) (size : state.values.size = func.numValues)
    (bounded : value < func.numValues) (result : func.results = [type])
    (canonical : types[value]? = some (some (.data type))) :
    (step module states func types state (.term (.ret [value] origin))).SliceOrigins func types observed := by
  constructor
  · exact before.values
  · intro mutability element sliceResult
    have same : type = .slice mutability element := List.cons.inj (result.symm.trans sliceResult) |>.1
    subst type
    exact (before.returned mutability element result).join
      (before.values value (by rw [size]; exact bounded) mutability element canonical)

#print axioms State.SliceOrigins.noncallDefinition

end Goose.GIR.ReplacementContentFlow.Model
