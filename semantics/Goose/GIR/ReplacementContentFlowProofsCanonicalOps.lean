import Goose.GIR.ReplacementContentFlowProofsCanonicalInvariant
import Goose.GIR.ReplacementContentFlowProofsCanonicalCalls

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem HolderValues.addFlow {func : Func} {vt : Array (Option VTy)} {provenance : Prov}
    {values : Array Roots} {index : Nat} {roots : Roots}
    (before : HolderValues func vt provenance values)
    (added : ∀ mutability payload, vt[index]? = some (some (.data (.ref mutability payload))) →
      payload.isRefLike = true → HolderRoots func payload (rootsAt provenance.vals index) roots) :
    HolderValues func vt provenance (addFlow values index roots) := by
  intro value bounded mutability payload type reference
  have priorBound : value < values.size := by simpa [ReplacementContentFlow.Model.addFlow] using bounded
  rw [flowAt_addFlow]
  split
  · rename_i updated
    have same := updated.1
    subst value
    exact (before index priorBound mutability payload type reference).join (added mutability payload type reference)
  · exact before value priorBound mutability payload type reference

theorem HolderSlots.addFlow {func : Func} {provenance : Prov} {values : Array Roots}
    {index : Nat} {roots : Roots} (before : HolderSlots func provenance values)
    (added : ∀ storage, func.slots[index]? = some storage → ∀ mutability payload,
      storage.ty = .ref mutability payload → payload.isRefLike = true →
        HolderRoots func payload (rootsAt provenance.slots index) roots) :
    HolderSlots func provenance (addFlow values index roots) := by
  intro slot storage row bounded mutability payload type reference
  have priorBound : slot < values.size := by simpa [ReplacementContentFlow.Model.addFlow] using bounded
  rw [flowAt_addFlow]
  split
  · rename_i updated
    have same := updated.1
    subst slot
    exact (before index storage row priorBound mutability payload type reference).join
      (added storage row mutability payload type reference)
  · exact before slot storage row priorBound mutability payload type reference

theorem State.CanonicalWithin.touch {func : Func} {vt : Array (Option VTy)} {provenance : Prov}
    {state : State} (before : state.CanonicalWithin func vt provenance) (touched : Roots) :
    ({ state with touched } : State).CanonicalWithin func vt provenance :=
  ⟨⟨before.shape.values,before.shape.slots,before.shape.contents,before.shape.writes⟩,
    before.values,before.memory.touch touched,before.writeRows,before.holderValues,before.holderSlots,
    before.ownerValues,before.ownerSlots,before.returned,before.returnedOwners⟩

theorem State.CanonicalWithin.touchValues {func : Func} {vt : Array (Option VTy)} {provenance : Prov}
    {state : State} (before : state.CanonicalWithin func vt provenance) (values : List ValueId) :
    (ReplacementContentFlow.Model.touchValues vt state values).CanonicalWithin func vt provenance :=
  before.touch _

theorem State.CanonicalWithin.addValue {func : Func} {vt : Array (Option VTy)} {provenance : Prov}
    {state : State} {index : Nat} {roots : Roots}
    (before : state.CanonicalWithin func vt provenance)
    (added : SymbolicRootsRefine func roots (rootsAt provenance.vals index))
    (physical : ∀ mutability payload, vt[index]? = some (some (.data (.ref mutability payload))) →
      payload.isRefLike = true → HolderRoots func payload (rootsAt provenance.vals index) roots)
    (owners : ∀ mutability payload, vt[index]? = some (some (.data (.ref mutability payload))) →
      payload.ownerElem?.isSome = true → OwnerOrigins func payload roots) :
    ({ state with values := addFlow state.values index roots } : State).CanonicalWithin func vt provenance :=
  { before with
    shape := { before.shape with values := by simpa [ReplacementContentFlow.Model.addFlow] using before.shape.values }
    values := before.values.addFlow added
    memory := ⟨before.memory.slots,before.memory.contents,before.memory.writes⟩
    holderValues := before.holderValues.addFlow physical
    ownerValues := before.ownerValues.addFlow owners }

theorem State.CanonicalWithin.addSlot {func : Func} {vt : Array (Option VTy)} {provenance : Prov}
    {state : State} {index : Nat} {roots : Roots}
    (before : state.CanonicalWithin func vt provenance)
    (added : SymbolicRootsRefine func roots (rootsAt provenance.slots index))
    (physical : ∀ storage, func.slots[index]? = some storage → ∀ mutability payload,
      storage.ty = .ref mutability payload → payload.isRefLike = true →
        HolderRoots func payload (rootsAt provenance.slots index) roots)
    (owners : ∀ storage, func.slots[index]? = some storage → ∀ mutability payload,
      storage.ty = .ref mutability payload → payload.ownerElem?.isSome = true → OwnerOrigins func payload roots) :
    ({ state with slots := addFlow state.slots index roots } : State).CanonicalWithin func vt provenance :=
  { before with
    shape := { before.shape with slots := by simpa [ReplacementContentFlow.Model.addFlow] using before.shape.slots }
    memory := before.memory.addSlot added
    holderSlots := before.holderSlots.addFlow physical
    ownerSlots := before.ownerSlots.addFlow owners }

theorem State.CanonicalWithin.addContent {func : Func} {vt : Array (Option VTy)} {provenance : Prov}
    {state : State} {index : Nat} {roots : Roots}
    (before : state.CanonicalWithin func vt provenance)
    (added : SymbolicRootsRefine func roots (func.contentRoots index))
    (observed : (func.roots.contents.find? (·.1 == index)).isSome = true) :
    ({ state with
      contents := addFlow state.contents index roots
      writes := state.writes.set! index
        ((state.writes[index]?.getD (.assigned .unknown)).join (.assigned roots)) } : State).CanonicalWithin
      func vt provenance :=
  { before with
    shape := ⟨before.shape.values,before.shape.slots,
      by simpa [ReplacementContentFlow.Model.addFlow] using before.shape.contents,
      by simpa using before.shape.writes⟩
    memory := before.memory.addContent added
    writeRows := before.writeRows.assign observed }

theorem step_def_noncall (module : Module) (states : Array State) (func : Func)
    (vt : Array (Option VTy)) (state : State) (value : ValueId) (op : Op)
    (ordinary : ∀ fn args origin, op ≠ .call fn args origin) :
    step module states func vt state (.def value op) =
      let exposed := ReplacementContentFlow.Model.touchValues vt state (accessOperands (.def value op))
      ReplacementContentFlow.Model.touchValues vt
        { exposed with values := addFlow exposed.values value (result func vt exposed value op) }
        (interiorLoadedResults vt (.def value op)) := by
  cases op <;> first | rfl | exact False.elim (ordinary _ _ _ rfl)

theorem State.CanonicalWithin.scalarDef {module : Module} {states : Array State}
    {func : Func} {vt : Array (Option VTy)} {provenance : Prov} {state : State} {value : ValueId} {op : Op}
    (before : state.CanonicalWithin func vt provenance)
    (ordinary : ∀ fn args origin, op ≠ .call fn args origin)
    (scalar : valRefLike vt value = false) :
    (step module states func vt state (.def value op)).CanonicalWithin func vt provenance := by
  rw [step_def_noncall _ _ _ _ _ _ _ ordinary]
  let exposed := ReplacementContentFlow.Model.touchValues vt state (accessOperands (.def value op))
  have initial : exposed.CanonicalWithin func vt provenance := before.touchValues _
  have assigned : ({ exposed with values := addFlow exposed.values value (.known []) } : State).CanonicalWithin
      func vt provenance := by
    apply initial.addValue (.known_empty _ _)
    · intro mutability payload type reference
      simp [HolderRoots,Roots.AtomsWithin]
    · intro mutability payload type owner
      simp [OwnerOrigins,Roots.AtomsWithin]
  simpa only [result,scalar,Bool.not_false,ite_true,exposed] using assigned.touchValues
    (interiorLoadedResults vt (.def value op))

theorem State.CanonicalWithin.forwardBacking {module : Module} {states : Array State}
    {results : Array (List RootRef)} {func : Func} {vt : Array (Option VTy)}
    {provenance : Prov} {state : State} {value source : ValueId} {op : Op}
    (before : state.CanonicalWithin func vt provenance)
    (ordinary : ∀ fn args origin, op ≠ .call fn args origin)
    (forward : ∀ current, result func vt current value op = flowAt current.values source)
    (canonical : rootsOfDef results vt func provenance value op = rootsAt provenance.vals source)
    (target : ∀ mutability payload, vt[value]? = some (some (.data (.ref mutability payload))) →
      payload.isRefLike = false ∧ payload.ownerElem?.isSome = false)
    (sourceBounded : source < state.values.size) (bounded : value < provenance.vals.size)
    (quiet : func.provStep results vt (provenance,false) (.def value op) = (provenance,false)) :
    (step module states func vt state (.def value op)).CanonicalWithin func vt provenance := by
  have ceiling : rootsAt provenance.vals source ⊆ rootsAt provenance.vals value := by
    rw [← canonical]
    exact provStep_def_roots bounded quiet
  rw [step_def_noncall _ _ _ _ _ _ _ ordinary]
  let exposed := ReplacementContentFlow.Model.touchValues vt state (accessOperands (.def value op))
  have initial : exposed.CanonicalWithin func vt provenance := before.touchValues _
  have assigned : ({ exposed with values := addFlow exposed.values value (flowAt exposed.values source) } : State).CanonicalWithin
      func vt provenance := by
    apply initial.addValue ((initial.values source sourceBounded).source_mono ceiling)
    · intro mutability payload type reference
      simp [(target mutability payload type).1] at reference
    · intro mutability payload type owner
      simp [(target mutability payload type).2] at owner
  simpa only [forward,exposed] using assigned.touchValues (interiorLoadedResults vt (.def value op))

theorem State.CanonicalWithin.writeTyped {func : Func} {vt : Array (Option VTy)}
    {provenance : Prov} {state : State} {value : ValueId} {payload : Ty} {address : Roots}
    {upper : List RootRef} (before : state.CanonicalWithin func vt provenance)
    (physical : HolderRoots func payload upper address)
    (canonical : vt[value]? = some (some (.data payload))) (bounded : value < state.values.size)
    (closed : ∀ index root, root ∈ func.parameterRoots index →
      root = .param index ∨ ∃ global, root = .global global)
    (parameters : ∀ type ∈ func.params, type.paramOk = true) (reference : payload.isRefLike = true)
    (locals : ∀ slot storage, func.slots[slot]? = some storage → storage.ty = payload →
      RootRef.local slot ∈ upper → rootsAt provenance.vals value ⊆ rootsAt provenance.slots slot)
    (contents : ∀ index mutability, func.params[index]? = some (.ref mutability payload) →
      RootRef.param index ∈ upper →
        (func.roots.contents.find? (·.1 == index)).isSome = true ∧
        RootsRefine func (rootsAt provenance.vals value) (func.contentRoots index)) :
    (ReplacementContentFlow.Model.write func state address (flowAt state.values value)).CanonicalWithin
      func vt provenance := by
  cases address with
  | pending => exact before
  | unknown => exact False.elim physical
  | known atoms =>
      simp only [ReplacementContentFlow.Model.write]
      apply List.foldlRecOn (motive := fun current : State => current.CanonicalWithin func vt provenance)
        atoms _ before
      intro current valid atom member
      cases physical atom member with
      | slot slot storage row type target =>
          have ceiling := locals slot storage row type target
          apply valid.addSlot ((before.values value bounded).source_mono ceiling)
          · intro actual actualRow mutability actualPayload actualType actualReference
            have same : actual = storage := Option.some.inj (actualRow.symm.trans row)
            subst actual
            have typed : vt[value]? = some (some (.data (.ref mutability actualPayload))) := by
              rw [← type,actualType] at canonical
              exact canonical
            exact (before.holderValues value bounded mutability actualPayload typed actualReference).mono ceiling
          · intro actual actualRow mutability actualPayload actualType owner
            have same : actual = storage := Option.some.inj (actualRow.symm.trans row)
            subst actual
            have typed : vt[value]? = some (some (.data (.ref mutability actualPayload))) := by
              rw [← type,actualType] at canonical
              exact canonical
            exact before.ownerValues value bounded mutability actualPayload typed owner
      | parameter index mutability row target =>
          have slice := paramOk_refLike_payload parameters row reference
          have found : (func.params[index]?).any Ty.isRefSlice = true := by simp [row,slice]
          simp only [found,ite_true]
          have bound := contents index mutability row target
          exact valid.addContent ((before.values value bounded).refine closed bound.2) bound.1

theorem State.CanonicalWithin.store {module : Module} {states : Array State}
    {results : Array (List RootRef)} {func : Func} {vt : Array (Option VTy)}
    {provenance : Prov} {state : State} {value address : ValueId} {payload : Ty}
    {mutability : Mutability} {origin : Option OriginId}
    (before : state.CanonicalWithin func vt provenance)
    (unique : (func.roots.contents.toList.map Prod.fst).Nodup)
    (closed : ∀ index root, root ∈ func.parameterRoots index →
      root = .param index ∨ ∃ global, root = .global global)
    (parameters : ∀ type ∈ func.params, type.paramOk = true)
    (canonical : vt[value]? = some (some (.data payload)))
    (addressType : vt[address]? = some (some (.data (.ref mutability payload))))
    (valueBounded : value < state.values.size) (addressBounded : address < state.values.size)
    (slots : provenance.slots.size = func.slots.size)
    (quiet : func.provStep results vt (provenance,false) (.eff (.store address value origin)) = (provenance,false))
    (admitted : func.checkAdmittedRegions module vt provenance = .ok ())
    {block : Block} (blockMember : block ∈ func.blocks.toList)
    (instruction : Inst.eff (.store address value origin) ∈ block.insts) :
    (step module states func vt state (.eff (.store address value origin))).CanonicalWithin func vt provenance := by
  let exposed := ReplacementContentFlow.Model.touchValues vt state (accessOperands (.eff (.store address value origin)))
  have initial : exposed.CanonicalWithin func vt provenance := before.touchValues _
  by_cases reference : payload.isRefLike = true
  · have like : valRefLike vt value = true := by simp [valRefLike,canonical,VTy.refLike,reference]
    have physical := initial.holderValues address addressBounded mutability payload addressType reference
    have written := initial.writeTyped physical canonical valueBounded closed parameters reference
      (fun slot storage row _ target => provStep_store_roots (by
        rw [slots]
        exact (Array.getElem?_eq_some_iff.mp row).choose) target quiet) (by
          intro index actualMutability row target
          have slice := paramOk_refLike_payload parameters row reference
          have found : (func.params[index]?).any Ty.isRefSlice = true := by simp [row,slice]
          obtain ⟨ceiling,annotation,bounded⟩ :=
            func.checkAdmittedRegions_store admitted blockMember instruction like target found
          have exactCeiling : func.contentRoots index = ceiling := by
            rw [contentRoots_find unique index,annotation]
            rfl
          exact ⟨by simp [annotation],by simpa only [exactCeiling] using bounded⟩)
    simpa only [step,Id.run_pure,like,ite_true,exposed] using written
  · have like : valRefLike vt value = false := by simp [valRefLike,canonical,VTy.refLike,reference]
    simpa only [step,Id.run_pure,like,Bool.false_eq_true,ite_false,exposed] using initial

theorem State.CanonicalWithin.ret {module : Module} {states : Array State}
    {func : Func} {vt : Array (Option VTy)} {provenance : Prov} {state : State}
    {value : ValueId} {origin : Option OriginId} {type : Ty}
    (before : state.CanonicalWithin func vt provenance)
    (result : func.results = [type]) (canonical : vt[value]? = some (some (.data type)))
    (bounded : value < state.values.size)
    (admitted : func.checkAdmittedRegions module vt provenance = .ok ())
    {block : Block} (blockMember : block ∈ func.blocks.toList)
    (instruction : Inst.term (.ret [value] origin) ∈ block.insts) :
    (step module states func vt state (.term (.ret [value] origin))).CanonicalWithin func vt provenance := by
  have equation : step module states func vt state (.term (.ret [value] origin)) =
      { state with returned := state.returned.join (flowAt state.values value) } := by
    simp [step,ReplacementContentFlow.Model.touchValues,accessOperands]
  rw [equation]
  refine { before with
    shape := ⟨before.shape.values,before.shape.slots,before.shape.contents,before.shape.writes⟩
    memory := ⟨before.memory.slots,before.memory.contents,before.memory.writes⟩
    returned := ?_
    returnedOwners := ?_ }
  · intro actual actualResult reference
    have same : actual = type := by simpa [result] using actualResult.symm
    subst actual
    have like : valRefLike vt value = true := by simp [valRefLike,canonical,VTy.refLike,reference]
    have ceiling := func.checkAdmittedRegions_return admitted blockMember instruction
      (by simp : (value,0) ∈ ([value] : List ValueId).zipIdx) like
    exact (before.returned type result reference).join ((before.values value bounded).source_mono ceiling)
  · intro mutability payload actualResult owner
    have same : type = .ref mutability payload := by simpa [result] using actualResult
    subst type
    exact (before.returnedOwners mutability payload result owner).join
      (before.ownerValues value bounded mutability payload canonical owner)

theorem State.CanonicalWithin.slotInit {module : Module} {states : Array State}
    {results : Array (List RootRef)} {func : Func} {vt : Array (Option VTy)}
    {provenance : Prov} {state : State} {slot : SlotId} {storage : Slot}
    {value : ValueId} {origin : Option OriginId}
    (before : state.CanonicalWithin func vt provenance)
    (row : func.slots[slot]? = some storage)
    (canonical : vt[value]? = some (some (.data storage.ty)))
    (bounded : value < state.values.size) (slots : provenance.slots.size = func.slots.size)
    (quiet : func.provStep results vt (provenance,false) (.eff (.slotInit slot value origin)) =
      (provenance,false)) :
    (step module states func vt state (.eff (.slotInit slot value origin))).CanonicalWithin func vt provenance := by
  have slotBound : slot < provenance.slots.size := by
    rw [slots]
    exact (Array.getElem?_eq_some_iff.mp row).choose
  have ceiling := provStep_slotInit_roots slotBound quiet
  have equation : step module states func vt state (.eff (.slotInit slot value origin)) =
      { state with slots := addFlow state.slots slot (flowAt state.values value) } := by
    simp [step,ReplacementContentFlow.Model.touchValues,accessOperands]
  rw [equation]
  apply before.addSlot ((before.values value bounded).source_mono ceiling)
  · intro actual actualRow mutability payload actualType reference
    have same : actual = storage := Option.some.inj (actualRow.symm.trans row)
    subst actual
    have typed : vt[value]? = some (some (.data (.ref mutability payload))) := by simpa [actualType] using canonical
    exact (before.holderValues value bounded mutability payload typed reference).mono ceiling

  · intro actual actualRow mutability payload actualType owner
    have same : actual = storage := Option.some.inj (actualRow.symm.trans row)
    subst actual
    have typed : vt[value]? = some (some (.data (.ref mutability payload))) := by simpa [actualType] using canonical
    exact before.ownerValues value bounded mutability payload typed owner

theorem State.CanonicalWithin.slotAddr {module : Module} {states : Array State}
    {results : Array (List RootRef)} {func : Func} {vt : Array (Option VTy)}
    {provenance : Prov} {state : State} {slot : SlotId} {storage : Slot}
    {value : ValueId} {mutability : Mutability}
    (before : state.CanonicalWithin func vt provenance)
    (row : func.slots[slot]? = some storage)
    (canonical : vt[value]? = some (some (.data (.ref mutability storage.ty))))
    (bounded : value < provenance.vals.size)
    (quiet : func.provStep results vt (provenance,false) (.def value (.slotAddr slot)) =
      (provenance,false)) :
    (step module states func vt state (.def value (.slotAddr slot))).CanonicalWithin func vt provenance := by
  have target : RootRef.local slot ∈ rootsAt provenance.vals value :=
    provStep_def_roots bounded quiet (by simp [rootsOfDef])
  have physical : HolderRoots func storage.ty (rootsAt provenance.vals value) (.known [.local slot]) := by
    intro atom member
    have same : atom = .local slot := by simpa using member
    subst atom
    exact .slot slot storage row rfl target
  have equation : step module states func vt state (.def value (.slotAddr slot)) =
      { state with values := addFlow state.values value (.known [.local slot]) } := by
    simp [step,ReplacementContentFlow.Model.touchValues,accessOperands,interiorLoadedResults,loadedResults,result,
      valRefLike,canonical,VTy.refLike,Ty.isRefLike]
  rw [equation]
  apply before.addValue physical.symbolic
  · intro actualMutability payload typed reference
    have same : storage.ty = payload := by
      rw [canonical] at typed
      exact (Ty.ref.inj (VTy.data.inj (Option.some.inj (Option.some.inj typed)))).2
    simpa only [same] using physical

  · intro actualMutability payload typed owner
    have same : storage.ty = payload := by
      rw [canonical] at typed
      exact (Ty.ref.inj (VTy.data.inj (Option.some.inj (Option.some.inj typed)))).2
    intro atom member
    have identical : atom = .local slot := by simpa using member
    subst atom
    exact .slot slot storage row same

theorem State.CanonicalWithin.refFreeze {module : Module} {states : Array State}
    {results : Array (List RootRef)} {func : Func} {vt : Array (Option VTy)}
    {provenance : Prov} {state : State} {value source : ValueId} {payload : Ty}
    {sourceMutability : Mutability}
    (before : state.CanonicalWithin func vt provenance)
    (canonical : vt[value]? = some (some (.data (.ref .readOnly payload))))
    (sourceType : vt[source]? = some (some (.data (.ref sourceMutability payload))))
    (sourceBounded : source < state.values.size) (bounded : value < provenance.vals.size)
    (quiet : func.provStep results vt (provenance,false) (.def value (.refFreeze source)) =
      (provenance,false)) :
    (step module states func vt state (.def value (.refFreeze source))).CanonicalWithin func vt provenance := by
  have ceiling : rootsAt provenance.vals source ⊆ rootsAt provenance.vals value :=
    provStep_def_roots bounded quiet
  have equation : step module states func vt state (.def value (.refFreeze source)) =
      { state with values := addFlow state.values value (flowAt state.values source) } := by
    simp [step,ReplacementContentFlow.Model.touchValues,accessOperands,interiorLoadedResults,loadedResults,result,
      valRefLike,canonical,VTy.refLike,Ty.isRefLike]
  rw [equation]
  apply before.addValue ((before.values source sourceBounded).source_mono ceiling)
  · intro actualMutability actualPayload typed reference
    have same : payload = actualPayload := by
      rw [canonical] at typed
      exact (Ty.ref.inj (VTy.data.inj (Option.some.inj (Option.some.inj typed)))).2
    subst actualPayload
    exact (before.holderValues source sourceBounded sourceMutability payload sourceType reference).mono ceiling

  · intro actualMutability actualPayload typed owner
    have same : payload = actualPayload := by
      rw [canonical] at typed
      exact (Ty.ref.inj (VTy.data.inj (Option.some.inj (Option.some.inj typed)))).2
    subst actualPayload
    exact before.ownerValues source sourceBounded sourceMutability payload sourceType owner

theorem State.CanonicalWithin.globalAddr {module : Module} {states : Array State}
    {results : Array (List RootRef)} {func : Func} {vt : Array (Option VTy)}
    {provenance : Prov} {state : State} {global : GlobalId} {type : Ty}
    {value : ValueId} {mutability : Mutability}
    (before : state.CanonicalWithin func vt provenance)
    (canonical : vt[value]? = some (some (.data (.ref mutability type))))
    (storage : type.isRefLike = false) (bounded : value < provenance.vals.size)
    (quiet : func.provStep results vt (provenance,false) (.def value (.globalAddr global)) = (provenance,false)) :
    (step module states func vt state (.def value (.globalAddr global))).CanonicalWithin func vt provenance := by
  have target : RootRef.global global ∈ rootsAt provenance.vals value :=
    provStep_def_roots bounded quiet (by simp [rootsOfDef])
  have equation : step module states func vt state (.def value (.globalAddr global)) =
      { state with values := addFlow state.values value (.known [.global global]) } := by
    simp [step,ReplacementContentFlow.Model.touchValues,accessOperands,interiorLoadedResults,loadedResults,result,
      valRefLike,canonical,VTy.refLike,Ty.isRefLike]
  rw [equation]
  apply before.addValue ((SymbolicRootsRefine.global_iff _ _ _).mpr target)
  · intro actualMutability payload typed reference
    have same : type = payload := by
      rw [canonical] at typed
      exact (Ty.ref.inj (VTy.data.inj (Option.some.inj (Option.some.inj typed)))).2
    subst payload
    simp [storage] at reference
  · intro actualMutability payload typed owner atom member
    have same : atom = .global global := by simpa using member
    subst atom
    exact .global global

theorem State.CanonicalWithin.ownerBorrow {module : Module} {states : Array State}
    {results : Array (List RootRef)} {func : Func} {vt : Array (Option VTy)}
    {provenance : Prov} {state : State} {value source : ValueId} {payload : Ty}
    {sourceMutability : Mutability}
    (before : state.CanonicalWithin func vt provenance)
    (canonical : vt[value]? = some (some (.data (.ref .mutable payload))))
    (sourceType : vt[source]? = some (some (.data (.ref sourceMutability payload))))
    (owner : payload.ownerElem?.isSome = true)
    (sourceBounded : source < state.values.size) (bounded : value < provenance.vals.size)
    (quiet : func.provStep results vt (provenance,false) (.def value (.ownerBorrow source)) = (provenance,false)) :
    (step module states func vt state (.def value (.ownerBorrow source))).CanonicalWithin func vt provenance := by
  have ceiling : rootsAt provenance.vals source ⊆ rootsAt provenance.vals value := provStep_def_roots bounded quiet
  have equation : step module states func vt state (.def value (.ownerBorrow source)) =
      { state with values := addFlow state.values value (flowAt state.values source) } := by
    simp [step,ReplacementContentFlow.Model.touchValues,accessOperands,interiorLoadedResults,loadedResults,result,
      valRefLike,canonical,VTy.refLike,Ty.isRefLike]
  rw [equation]
  apply before.addValue ((before.values source sourceBounded).source_mono ceiling)
  · intro actualMutability actualPayload typed reference
    have same : payload = actualPayload := by
      rw [canonical] at typed
      exact (Ty.ref.inj (VTy.data.inj (Option.some.inj (Option.some.inj typed)))).2
    subst actualPayload
    cases payload <;> simp_all [Ty.ownerElem?,Ty.isRefLike]
  · intro actualMutability actualPayload typed actualOwner
    have same : payload = actualPayload := by
      rw [canonical] at typed
      exact (Ty.ref.inj (VTy.data.inj (Option.some.inj (Option.some.inj typed)))).2
    subst actualPayload
    exact before.ownerValues source sourceBounded sourceMutability payload sourceType actualOwner

theorem State.CanonicalWithin.load {module : Module} {states : Array State}
    {results : Array (List RootRef)} {func : Func} {vt : Array (Option VTy)}
    {provenance : Prov} {state : State} {value address : ValueId} {payload : Ty} {mutability : Mutability}
    (before : state.CanonicalWithin func vt provenance)
    (unique : (func.roots.contents.toList.map Prod.fst).Nodup)
    (parameters : ∀ type ∈ func.params, type.paramOk = true)
    (canonical : vt[value]? = some (some (.data payload)))
    (addressType : vt[address]? = some (some (.data (.ref mutability payload))))
    (addressBounded : address < state.values.size) (bounded : value < provenance.vals.size)
    (quiet : func.provStep results vt (provenance,false) (.def value (.load address)) = (provenance,false))
    (observed : payload.isRefLike = true → ∀ index, RootRef.param index ∈ rootsAt provenance.vals address →
      (func.params[index]?).any Ty.isRefSlice = true →
      (func.roots.contents.find? (·.1 == index)).isSome = true) :
    (step module states func vt state (.def value (.load address))).CanonicalWithin func vt provenance := by
  let exposed := ReplacementContentFlow.Model.touchValues vt state (accessOperands (.def value (.load address)))
  have initial : exposed.CanonicalWithin func vt provenance := before.touchValues _
  by_cases reference : payload.isRefLike = true
  · have like : valRefLike vt value = true := by simp [valRefLike,canonical,VTy.refLike,reference]
    have physical := initial.holderValues address addressBounded mutability payload addressType reference
    have produced := initial.memory.load_closed unique initial.shape physical parameters canonical reference
      (observed reference) bounded quiet
    have localCeiling : ∀ slot, RootRef.local slot ∈ rootsAt provenance.vals address →
        rootsAt provenance.slots slot ⊆ rootsAt provenance.vals value := by
      intro slot target root member
      exact provStep_def_roots bounded quiet (rootsOfDef_load_local like target member)
    have assigned : ({ exposed with values := addFlow exposed.values value (content func exposed (flowAt exposed.values address)) } : State).CanonicalWithin func vt provenance := by
      apply initial.addValue produced
      · intro actualMutability actualPayload typed actualReference
        have same : payload = .ref actualMutability actualPayload := by
          rw [canonical] at typed
          exact VTy.data.inj (Option.some.inj (Option.some.inj typed))
        subst payload
        apply physical.content_reference parameters
        intro slot storage row type target
        have slotBound : slot < exposed.slots.size := by
          rw [initial.shape.slots]
          exact (Array.getElem?_eq_some_iff.mp row).choose
        exact (initial.holderSlots slot storage row slotBound actualMutability actualPayload type actualReference).mono
          (localCeiling slot target)
      · intro actualMutability actualPayload typed owner
        have same : payload = .ref actualMutability actualPayload := by
          rw [canonical] at typed
          exact VTy.data.inj (Option.some.inj (Option.some.inj typed))
        subst payload
        apply physical.content_reference parameters
        intro slot storage row type target
        have slotBound : slot < exposed.slots.size := by
          rw [initial.shape.slots]
          exact (Array.getElem?_eq_some_iff.mp row).choose
        exact initial.ownerSlots slot storage row slotBound actualMutability actualPayload type owner
    have equation : step module states func vt state (.def value (.load address)) =
        ReplacementContentFlow.Model.touchValues vt
          { exposed with values := addFlow exposed.values value (content func exposed (flowAt exposed.values address)) }
          (interiorLoadedResults vt (.def value (.load address))) := by
      simp only [step,Id.run_pure,result,like,Bool.not_true,Bool.false_eq_true,ite_false,exposed]
    rw [equation]
    exact assigned.touchValues _
  · have like : valRefLike vt value = false := by simp [valRefLike,canonical,VTy.refLike,reference]
    have assigned : ({ exposed with values := addFlow exposed.values value (.known []) } : State).CanonicalWithin
        func vt provenance := by
      apply initial.addValue (.known_empty _ _)
      · intro actualMutability actualPayload typed actualReference
        simp [HolderRoots,Roots.AtomsWithin]
      · intro actualMutability actualPayload typed owner
        simp [OwnerOrigins,Roots.AtomsWithin]
    have equation : step module states func vt state (.def value (.load address)) =
        ReplacementContentFlow.Model.touchValues vt { exposed with values := addFlow exposed.values value (.known []) }
          (interiorLoadedResults vt (.def value (.load address))) := by
      simp only [step,Id.run_pure,result,like,Bool.not_false,ite_true,exposed]
    rw [equation]
    exact assigned.touchValues _

#print axioms State.CanonicalWithin.ret
#print axioms State.CanonicalWithin.slotInit
#print axioms State.CanonicalWithin.load

end Goose.GIR.ReplacementContentFlow.Model
