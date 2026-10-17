import Goose.GIR.ReplacementContentFlowProofsCanonicalOps

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem State.CanonicalWithin.writeSlice {func : Func} {vt : Array (Option VTy)}
    {provenance : Prov} {state : State} {mutability : Mutability} {element : Ty}
    {address roots : Roots} {upper expected : List RootRef}
    (before : state.CanonicalWithin func vt provenance)
    (physical : HolderRoots func (.slice mutability element) upper address)
    (flat : element.flat = true)
    (closed : ∀ index root, root ∈ func.parameterRoots index →
      root = .param index ∨ ∃ global, root = .global global)
    (bounded : SymbolicRootsRefine func roots expected)
    (receivers : ∀ receiver ∈ upper,
      RootsRefine func expected (func.receiverContentCeiling provenance receiver))
    (observed : ∀ (index : Nat) (outer : Mutability),
      func.params[index]? = some (.ref outer (.slice mutability element)) →
      RootRef.param index ∈ upper →
      (func.roots.contents.find? (·.1 == index)).isSome = true) :
    (write func state address roots).CanonicalWithin func vt provenance := by
  cases address with
  | pending => exact before
  | unknown => exact False.elim physical
  | known atoms =>
      simp only [write]
      apply List.foldlRecOn (motive := fun current : State => current.CanonicalWithin func vt provenance)
        atoms _ before
      intro current valid atom member
      cases physical atom member with
      | slot slot storage row type target =>
          have ceiling : RootsRefine func expected (rootsAt provenance.slots slot) := by
            simpa [Func.receiverContentCeiling] using receivers (.local slot) target
          apply valid.addSlot (bounded.refine closed ceiling)
          · intro actual actualRow actualMutability payload actualType _
            have same : actual = storage := Option.some.inj (actualRow.symm.trans row)
            subst actual
            rw [type] at actualType
            cases actualType
          · intro actual actualRow actualMutability payload actualType _
            have same : actual = storage := Option.some.inj (actualRow.symm.trans row)
            subst actual
            rw [type] at actualType
            cases actualType
      | parameter index actualMutability row target =>
          have slice : (func.params[index]?).any Ty.isRefSlice = true := by simp [row,Ty.isRefSlice,flat]
          have ceiling : RootsRefine func expected (func.contentRoots index) := by
            simpa [Func.receiverContentCeiling,slice] using receivers (.param index) target
          simp only [slice,ite_true]
          exact valid.addContent (bounded.refine closed ceiling) (observed index actualMutability row target)

private theorem call_forIn_preserves {α : Type} (values : List α) (predicate : State → Prop)
    (update : α → State → Id (ForInStep State))
    (preserved : ∀ value ∈ values, ∀ state, predicate state → match (update value state).run with
      | .done after | .yield after => predicate after)
    (state : State) (initial : predicate state) : predicate (forIn values state update).run := by
  induction values generalizing state with
  | nil => exact initial
  | cons value values ih =>
      have one := preserved value (by simp) state initial
      cases equation : (update value state).run with
      | done after => simpa [List.forIn_cons,equation] using one
      | yield after =>
          have next : predicate after := by simpa [equation] using one
          simpa [List.forIn_cons,equation] using ih
            (fun value member => preserved value (List.mem_cons_of_mem _ member)) after next

theorem State.CanonicalWithin.callState {module : Module} {states : Array State}
    {func callee : Func} {vt : Array (Option VTy)} {provenance : Prov}
    {state effects : State} {fn : FnId} {args : List ValueId}
    (before : state.CanonicalWithin func vt provenance)
    (calleeAt : module.funcs[fn]? = some callee) (effectsAt : states[fn]? = some effects)
    (closed : ∀ index root, root ∈ func.parameterRoots index →
      root = .param index ∨ ∃ global, root = .global global)
    (writes : ∀ type index, (type,index) ∈ callee.params.zipIdx → type.isRefSlice = true →
      ∀ roots, effects.writes[index]?.getD (.assigned .unknown) = .assigned roots →
        ∃ value mutability element expected,
          args[index]? = some value ∧ element.flat = true ∧
          HolderRoots func (.slice mutability element) (rootsAt provenance.vals value)
            (flowAt state.values value) ∧
          SymbolicRootsRefine func (substitute func state args roots) expected ∧
          (∀ receiver ∈ rootsAt provenance.vals value,
            RootsRefine func expected (func.receiverContentCeiling provenance receiver)) ∧
          ∀ (index : Nat) (outer : Mutability),
            func.params[index]? = some (.ref outer (.slice mutability element)) →
            RootRef.param index ∈ rootsAt provenance.vals value →
            (func.roots.contents.find? (·.1 == index)).isSome = true) :
    (Model.callState module states func state fn args).2.CanonicalWithin func vt provenance := by
  simp only [Model.callState,calleeAt,effectsAt,Id.run_bind,Id.run_pure]
  apply call_forIn_preserves _ (fun current => current.CanonicalWithin func vt provenance)
  · intro parameter member current valid
    by_cases reference : parameter.1.isRefSlice = true
    · simp only [reference,ite_true]
      cases writeRow : effects.writes[parameter.2]?.getD (.assigned .unknown) with
      | unchanged => exact valid
      | assigned roots =>
          obtain ⟨value,mutability,element,expected,argument,flat,physical,bounded,receivers,observed⟩ :=
            writes parameter.1 parameter.2 member reference roots writeRow
          simp only [argument,Option.map_some,Option.getD_some]
          exact valid.writeSlice physical flat closed bounded receivers observed
    · simpa [reference] using valid
  · exact before.touch _

theorem isRefSlice_shape {type : Ty} (reference : type.isRefSlice = true) :
    ∃ outer inner element, type = .ref outer (.slice inner element) ∧ element.flat = true := by
  cases type <;> simp_all [Ty.isRefSlice]
  rename_i mutability payload
  cases payload <;> simp_all [Ty.isRefSlice]
  exact ⟨_,_,_,⟨rfl,rfl,rfl⟩,reference⟩

theorem State.CanonicalWithin.callContentArguments {module : Module} {func callee : Func}
    {vt : Array (Option VTy)} {provenance : Prov} {state : State}
    {fn value : ValueId} {args : List ValueId} {origin : Option OriginId}
    (before : state.CanonicalWithin func vt provenance)
    (calleeAt : module.funcs[fn]? = some callee)
    (closed : ∀ index root, root ∈ func.parameterRoots index →
      root = .param index ∨ ∃ global, root = .global global)
    (parameters : ∀ type ∈ func.params, type.paramOk = true)
    (contentTypes : ∀ index ceiling,
      callee.roots.contents.find? (·.1 == index) = some (index,ceiling) →
      (callee.params[index]?).any Ty.isRefSlice = true)
    (arguments : ∀ (index : Nat) (outer : Mutability) (payload : Ty), callee.params[index]? = some (.ref outer payload) →
      ∃ argument actualMutability, args[index]? = some argument ∧
        vt[argument]? = some (some (.data (.ref actualMutability payload))) ∧ argument < func.numValues)
    (observed : ∀ (index : Nat) (argument : ValueId), args[index]? = some argument →
      (callee.params[index]?).any Ty.isRefSlice = true →
      ∀ receiver, RootRef.param receiver ∈ rootsAt provenance.vals argument →
        (func.params[receiver]?).any Ty.isRefSlice = true →
        (func.roots.contents.find? (·.1 == receiver)).isSome = true)
    (admitted : func.checkAdmittedRegions module vt provenance = .ok ())
    {block : Block} (blockMember : block ∈ func.blocks.toList)
    (called : Inst.def value (.call fn args origin) ∈ block.insts) :
    ∀ index ceiling, index < callee.params.length →
      callee.roots.contents.find? (·.1 == index) = some (index,ceiling) →
      ∃ argument, args[index]? = some argument ∧
        SymbolicRootsRefine func (content func state (flowAt state.values argument))
          (mapRawContentRoots provenance args ceiling) := by
  intro index ceiling indexBound annotation
  have slice := contentTypes index ceiling annotation
  cases formal : callee.params[index]? with
  | none => simp [formal] at slice
  | some type =>
      have reference : type.isRefSlice = true := by simpa [formal] using slice
      obtain ⟨outer,inner,element,typeEqual,flat⟩ := isRefSlice_shape reference
      subst type
      obtain ⟨argument,actualMutability,argumentRow,canonical,bounded⟩ := arguments index outer _ formal
      have bound : argument < state.values.size := by rw [before.shape.values]; exact bounded
      have physical := before.holderValues argument bound actualMutability (.slice inner element) canonical rfl
      refine ⟨argument,argumentRow,?_⟩
      apply before.memory.call_content before.shape physical closed parameters rfl
        (observed index argument argumentRow slice)
      intro receiver member
      have selection := Array.mem_of_find?_eq_some annotation
      have receiverMember : receiver ∈ rootsAt provenance.vals args[index]! := by
        simpa [List.getElem!_eq_getElem?_getD,argumentRow] using member
      exact func.checkAdmittedRegions_call_receiver_reverse admitted blockMember called
        calleeAt (by simpa using selection) slice receiverMember

theorem State.CanonicalWithin.callState_closed {module : Module} {states : Array State}
    {func callee : Func} {vt calleeTypes : Array (Option VTy)} {provenance calleeProvenance : Prov}
    {state effects : State} {fn value : ValueId} {args : List ValueId} {origin : Option OriginId}
    (before : state.CanonicalWithin func vt provenance)
    (calleeAt : module.funcs[fn]? = some callee) (effectsAt : states[fn]? = some effects)
    (calleeBounded : effects.CanonicalWithin callee calleeTypes calleeProvenance)
    (supported : effects.Supported (atomUniverse module callee))
    (unique : (callee.roots.contents.toList.map Prod.fst).Nodup)
    (closed : ∀ index root, root ∈ func.parameterRoots index →
      root = .param index ∨ ∃ global, root = .global global)
    (parameters : ∀ type ∈ func.params, type.paramOk = true)
    (external : ∀ index slot, RootRef.local slot ∉ callee.contentRoots index)
    (contracts : ∀ index, RootsRefine func (mapRawContentRoots provenance args [.param index])
      (mapRawContentRoots provenance args (callee.parameterRoots index)))
    (contentTypes : ∀ index ceiling,
      callee.roots.contents.find? (·.1 == index) = some (index,ceiling) →
      (callee.params[index]?).any Ty.isRefSlice = true)
    (arguments : ∀ index, index < callee.params.length →
      ∃ argument, args[index]? = some argument ∧ argument < func.numValues)
    (references : ∀ (index : Nat) (outer : Mutability) (payload : Ty),
      callee.params[index]? = some (.ref outer payload) →
      ∃ argument actualMutability, args[index]? = some argument ∧
        vt[argument]? = some (some (.data (.ref actualMutability payload))) ∧ argument < func.numValues)
    (observed : ∀ (index : Nat) (argument : ValueId), args[index]? = some argument →
      (callee.params[index]?).any Ty.isRefSlice = true →
      ∀ receiver, RootRef.param receiver ∈ rootsAt provenance.vals argument →
        (func.params[receiver]?).any Ty.isRefSlice = true →
        (func.roots.contents.find? (·.1 == receiver)).isSome = true)
    (admitted : func.checkAdmittedRegions module vt provenance = .ok ())
    {block : Block} (blockMember : block ∈ func.blocks.toList)
    (called : Inst.def value (.call fn args origin) ∈ block.insts) :
    (Model.callState module states func state fn args).2.CanonicalWithin func vt provenance := by
  have argumentBounds : ∀ index, index < callee.params.length →
      ∃ argument, args[index]? = some argument ∧
        SymbolicRootsRefine func (flowAt state.values argument)
          (mapRawContentRoots provenance args [.param index]) := by
    intro index indexBound
    obtain ⟨argument,argumentRow,bounded⟩ := arguments index indexBound
    refine ⟨argument,argumentRow,?_⟩
    have bound : argument < state.values.size := by rw [before.shape.values]; exact bounded
    apply (before.values argument bound).source_mono
    intro root member
    simpa [mapRawContentRoots,argumentRow] using member
  have contentBounds := before.callContentArguments calleeAt closed parameters contentTypes
    references observed admitted blockMember called
  apply before.callState calleeAt effectsAt closed
  intro type index member reference roots assigned
  have formal := List.mem_zipIdx_iff_getElem?.mp member
  have indexBound : index < effects.writes.size := by
    rw [calleeBounded.shape.writes]
    exact (List.getElem?_eq_some_iff.mp formal).choose
  have rowObserved := calleeBounded.writeRows index indexBound roots assigned
  obtain ⟨row,annotation⟩ := Option.isSome_iff_exists.mp rowObserved
  have selection := Array.find?_some annotation
  have identity : row.1 = index := by simpa only [beq_iff_eq] using selection
  rcases row with ⟨selected,ceiling⟩
  change selected = index at identity
  subst selected
  have exactCeiling : callee.contentRoots index = ceiling := by
    rw [contentRoots_find unique index,annotation]
    rfl
  obtain ⟨outer,inner,element,typeEqual,flat⟩ := isRefSlice_shape reference
  subst type
  obtain ⟨argument,actualMutability,argumentRow,canonical,argumentBound⟩ := references index outer _ formal
  have bound : argument < state.values.size := by rw [before.shape.values]; exact argumentBound
  have physical := before.holderValues argument bound actualMutability (.slice inner element) canonical rfl
  have writeBound := calleeBounded.memory.writes index indexBound
  rw [assigned] at writeBound
  change SymbolicRootsRefine callee roots (callee.contentRoots index) at writeBound
  have writeSupport := supported.writes.getD index (.assigned .unknown) (by trivial)
  rw [assigned] at writeSupport
  have substituted := writeBound.substitute closed writeSupport (external index) contracts argumentBounds contentBounds
  refine ⟨argument,inner,element,mapRawContentRoots provenance args ceiling,argumentRow,flat,physical,?_,?_,?_⟩
  · simpa only [exactCeiling] using substituted
  · intro receiver receiverMember
    have mappedMember : receiver ∈ rootsAt provenance.vals args[index]! := by
      simpa [List.getElem!_eq_getElem?_getD,argumentRow] using receiverMember
    exact func.checkAdmittedRegions_call_receiver admitted blockMember called calleeAt
      (by simpa using Array.mem_of_find?_eq_some annotation)
      (by simp [formal,Ty.isRefSlice,flat]) mappedMember
  · intro receiver actualMutability receiverType receiverMember
    exact observed index argument argumentRow (by simp [formal,Ty.isRefSlice,flat]) receiver
      receiverMember (by simp [receiverType,Ty.isRefSlice,flat])


theorem State.CanonicalWithin.call {module : Module} {states : Array State}
    {func callee : Func} {vt calleeTypes : Array (Option VTy)} {provenance calleeProvenance : Prov}
    {results : Array (List RootRef)} {state effects : State}
    {fn value : ValueId} {args : List ValueId} {origin : Option OriginId} {type : Ty}
    (before : state.CanonicalWithin func vt provenance)
    (calleeAt : module.funcs[fn]? = some callee) (effectsAt : states[fn]? = some effects)
    (calleeBounded : effects.CanonicalWithin callee calleeTypes calleeProvenance)
    (supported : effects.Supported (atomUniverse module callee))
    (unique : (callee.roots.contents.toList.map Prod.fst).Nodup)
    (closed : ∀ index root, root ∈ func.parameterRoots index →
      root = .param index ∨ ∃ global, root = .global global)
    (parameters : ∀ type ∈ func.params, type.paramOk = true)
    (contentExternal : ∀ index slot, RootRef.local slot ∉ callee.contentRoots index)
    (resultExternal : ∀ slot, RootRef.local slot ∉ callee.roots.results[0]?.getD [])
    (contracts : ∀ index, RootsRefine func (mapRawContentRoots provenance args [.param index])
      (mapRawContentRoots provenance args (callee.parameterRoots index)))
    (contentTypes : ∀ index ceiling,
      callee.roots.contents.find? (·.1 == index) = some (index,ceiling) →
      (callee.params[index]?).any Ty.isRefSlice = true)
    (arguments : ∀ index, index < callee.params.length →
      ∃ argument, args[index]? = some argument ∧ argument < func.numValues)
    (references : ∀ (index : Nat) (outer : Mutability) (payload : Ty),
      callee.params[index]? = some (.ref outer payload) →
      ∃ argument actualMutability, args[index]? = some argument ∧
        vt[argument]? = some (some (.data (.ref actualMutability payload))) ∧ argument < func.numValues)
    (observed : ∀ (index : Nat) (argument : ValueId), args[index]? = some argument →
      (callee.params[index]?).any Ty.isRefSlice = true →
      ∀ receiver, RootRef.param receiver ∈ rootsAt provenance.vals argument →
        (func.params[receiver]?).any Ty.isRefSlice = true →
        (func.roots.contents.find? (·.1 == receiver)).isSome = true)
    (resultType : callee.results = [type])
    (canonical : vt[value]? = some (some (.data type)))
    (notHolder : ∀ mutability payload, type = .ref mutability payload → payload.isRefLike = false)
    (resultFloor : callee.roots.results[0]?.getD [] ⊆ rootsAt results fn)
    (valueBounded : value < provenance.vals.size)
    (quiet : func.provStep results vt (provenance,false) (.def value (.call fn args origin)) = (provenance,false))
    (admitted : func.checkAdmittedRegions module vt provenance = .ok ())
    {block : Block} (blockMember : block ∈ func.blocks.toList)
    (called : Inst.def value (.call fn args origin) ∈ block.insts) :
    (step module states func vt state (.def value (.call fn args origin))).CanonicalWithin func vt provenance := by
  let exposed := ReplacementContentFlow.Model.touchValues vt state (accessOperands (.def value (.call fn args origin)))
  have initial : exposed.CanonicalWithin func vt provenance := before.touchValues _
  have mutated := initial.callState_closed calleeAt effectsAt calleeBounded supported unique closed parameters
    contentExternal contracts contentTypes arguments references observed admitted blockMember called
  have argumentBounds : ∀ index, index < callee.params.length →
      ∃ argument, args[index]? = some argument ∧
        SymbolicRootsRefine func (flowAt exposed.values argument)
          (mapRawContentRoots provenance args [.param index]) := by
    intro index indexBound
    obtain ⟨argument,argumentRow,bounded⟩ := arguments index indexBound
    refine ⟨argument,argumentRow,?_⟩
    have bound : argument < exposed.values.size := by rw [initial.shape.values]; exact bounded
    apply (initial.values argument bound).source_mono
    intro root member
    simpa [mapRawContentRoots,argumentRow] using member
  have contentBounds := initial.callContentArguments calleeAt closed parameters contentTypes
    references observed admitted blockMember called
  have ceiling : mapRawContentRoots provenance args (callee.roots.results[0]?.getD []) ⊆
      rootsAt provenance.vals value := by
    intro root member
    have mapped : root ∈ rootsOfDef results vt func provenance value (.call fn args origin) := by
      obtain ⟨original,originalMember,mapped⟩ := (mapRawContentRoots_member _ _ _ _).mp member
      apply List.mem_flatMap.mpr
      refine ⟨original,resultFloor originalMember,?_⟩
      cases original with
      | «local» slot => simpa [mapRawContentRoots] using mapped
      | global global => simpa [mapRawContentRoots] using mapped
      | param index =>
          cases argument : args[index]? <;> simpa [mapRawContentRoots,argument] using mapped
    exact provStep_def_roots valueBounded quiet mapped
  have produced : SymbolicRootsRefine func
      (if valRefLike vt value then (Model.callState module states func exposed fn args).1 else .known [])
      (rootsAt provenance.vals value) := by
    by_cases reference : type.isRefLike = true
    · have like : valRefLike vt value = true := by simp [valRefLike,canonical,VTy.refLike,reference]
      simp only [like,ite_true]
      exact (call_result_symbolic calleeAt effectsAt closed
        (calleeBounded.returned type resultType reference) supported.returned resultExternal
        contracts argumentBounds contentBounds).source_mono ceiling
    · have like : valRefLike vt value = false := by simp [valRefLike,canonical,VTy.refLike,reference]
      simp only [like,Bool.false_eq_true,ite_false]
      exact .known_empty _ _
  have assigned := mutated.addValue produced (by
    intro mutability payload typed reference
    have same : type = .ref mutability payload := by
      rw [canonical] at typed
      exact VTy.data.inj (Option.some.inj (Option.some.inj typed))
    simp [notHolder mutability payload same] at reference) (by
    intro mutability payload typed owner
    have same : type = .ref mutability payload := by
      rw [canonical] at typed
      exact VTy.data.inj (Option.some.inj (Option.some.inj typed))
    subst type
    have like : valRefLike vt value = true := by simp [valRefLike,canonical,VTy.refLike,Ty.isRefLike]
    simp only [like,ite_true,callState_result _ _ _ _ _ _ _ _ calleeAt effectsAt]
    apply (calleeBounded.returnedOwners mutability payload resultType owner).substitute
      (calleeBounded.returned _ resultType rfl) resultExternal
    intro index formalMutability formal
    obtain ⟨argument,actualMutability,argumentRow,argumentType,bounded⟩ := references index formalMutability payload formal
    refine ⟨argument,argumentRow,?_⟩
    apply initial.ownerValues argument (by rw [initial.shape.values]; exact bounded) actualMutability payload argumentType owner)
  have equation : step module states func vt state (.def value (.call fn args origin)) =
      ReplacementContentFlow.Model.touchValues vt
        { (Model.callState module states func exposed fn args).2 with
          values := addFlow (Model.callState module states func exposed fn args).2.values value
            (if valRefLike vt value then (Model.callState module states func exposed fn args).1 else .known []) }
        (interiorLoadedResults vt (.def value (.call fn args origin))) := by rfl
  rw [equation]
  exact assigned.touchValues _

#print axioms State.CanonicalWithin.writeSlice
#print axioms State.CanonicalWithin.callState

end Goose.GIR.ReplacementContentFlow.Model
