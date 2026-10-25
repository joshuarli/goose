import Goose.GIR.ReplacementContentFlowProofsCanonicalClosure

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem rootsOfDef_load_local {results : Array (List RootRef)} {vt : Array (Option VTy)}
    {func : Func} {provenance : Prov} {value address : ValueId} {slot : SlotId}
    (reference : valRefLike vt value = true)
    (target : RootRef.local slot ∈ rootsAt provenance.vals address) :
    rootsAt provenance.slots slot ⊆ rootsOfDef results vt func provenance value (.load address) := by
  intro root member
  simp only [rootsOfDef, reference, ite_true]
  apply (unionRoots_mem_iff _ _ _).mpr
  exact Or.inl (List.mem_flatMap.mpr ⟨.local slot,target,member⟩)

theorem rootsOfDef_load_contents {results : Array (List RootRef)} {vt : Array (Option VTy)}
    {func : Func} {provenance : Prov} {value address : ValueId} {index : Nat}
    {mutability : Mutability} {payload : Ty}
    (unique : (func.roots.contents.toList.map Prod.fst).Nodup)
    (type : vt[value]? = some (some (.data payload)))
    (formal : func.params[index]? = some (.ref mutability payload))
    (reference : (Ty.ref mutability payload).isRefSlice = true)
    (target : RootRef.param index ∈ rootsAt provenance.vals address) :
    func.contentRoots index ⊆ rootsOfDef results vt func provenance value (.load address) := by
  cases payload <;> simp only [Ty.isRefSlice] at reference <;> try contradiction
  case slice mutability element =>
    have like : valRefLike vt value = true := by simp [valRefLike,type,VTy.refLike,Ty.isRefLike]
    intro root member
    simp only [rootsOfDef,like,ite_true,type]
    apply (unionRoots_mem_iff _ _ _).mpr
    apply Or.inr
    apply List.mem_flatMap.mpr
    refine ⟨.param index,target,?_⟩
    rw [contentRoots_find unique index] at member
    simpa only [formal,Ty.isRefSlice,reference,ite_true] using member

theorem State.CanonicalMemory.load {results : Array (List RootRef)} {vt : Array (Option VTy)}
    {func : Func} {provenance : Prov} {state : State} {value address : ValueId} {payload : Ty}
    (before : state.CanonicalMemory func provenance)
    (unique : (func.roots.contents.toList.map Prod.fst).Nodup)
    (shape : state.Shape func)
    (physical : HolderRoots func payload (rootsAt provenance.vals address) (flowAt state.values address))
    (parameters : ∀ type ∈ func.params, type.paramOk = true)
    (type : vt[value]? = some (some (.data payload)))
    (reference : payload.isRefLike = true)
    (observed : ∀ index, RootRef.param index ∈ rootsAt provenance.vals address →
      (func.params[index]?).any Ty.isRefSlice = true →
      (func.roots.contents.find? (·.1 == index)).isSome = true) :
    SymbolicRootsRefine func (content func state (flowAt state.values address))
      (rootsOfDef results vt func provenance value (.load address)) := by
  have like : valRefLike vt value = true := by simp [valRefLike,type,VTy.refLike,reference]
  apply physical.content_symbolic_typed parameters reference
  · intro slot storage row _ target
    have bound : slot < state.slots.size := by
      rw [shape.slots]
      exact (Array.getElem?_eq_some_iff.mp row).choose
    exact (before.slots slot bound).source_mono (rootsOfDef_load_local like target)
  · intro index mutability formal target
    have slice := paramOk_refLike_payload parameters formal reference
    have observed := observed index target (by simp [formal,slice])
    have bound : index < state.contents.size := by
      rw [shape.contents]
      exact (List.getElem?_eq_some_iff.mp formal).choose
    exact (before.contents index bound observed).source_mono
      (rootsOfDef_load_contents unique type formal slice target)

theorem State.CanonicalMemory.load_closed {results : Array (List RootRef)} {vt : Array (Option VTy)}
    {func : Func} {provenance : Prov} {state : State} {value address : ValueId} {payload : Ty}
    (before : state.CanonicalMemory func provenance)
    (unique : (func.roots.contents.toList.map Prod.fst).Nodup) (shape : state.Shape func)
    (physical : HolderRoots func payload (rootsAt provenance.vals address) (flowAt state.values address))
    (parameters : ∀ type ∈ func.params, type.paramOk = true)
    (type : vt[value]? = some (some (.data payload))) (reference : payload.isRefLike = true)
    (observed : ∀ index, RootRef.param index ∈ rootsAt provenance.vals address →
      (func.params[index]?).any Ty.isRefSlice = true →
      (func.roots.contents.find? (·.1 == index)).isSome = true)
    (bounded : value < provenance.vals.size)
    (quiet : func.provStep results vt (provenance,false) (.def value (.load address)) = (provenance,false)) :
    SymbolicRootsRefine func (content func state (flowAt state.values address)) (rootsAt provenance.vals value) :=
  (before.load unique shape physical parameters type reference observed).source_mono (provStep_def_roots bounded quiet)

theorem State.CanonicalMemory.store {m : Module} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {func : Func} {provenance : Prov} {state : State}
    {address value : ValueId} {payload : Ty} {origin : Option OriginId}
    (before : state.CanonicalMemory func provenance)
    (unique : (func.roots.contents.toList.map Prod.fst).Nodup)
    (physical : HolderRoots func payload (rootsAt provenance.vals address) (flowAt state.values address))
    (valueBound : SymbolicRootsRefine func (flowAt state.values value) (rootsAt provenance.vals value))
    (closed : ∀ index root, root ∈ func.parameterRoots index →
      root = .param index ∨ ∃ global, root = .global global)
    (parameters : ∀ type ∈ func.params, type.paramOk = true)
    (payloadReference : payload.isRefLike = true)
    (reference : valRefLike vt value = true)
    (slots : provenance.slots.size = func.slots.size)
    (quiet : func.provStep results vt (provenance,false) (.eff (.store address value origin)) =
      (provenance,false))
    (admitted : func.checkAdmittedRegions m vt provenance = .ok ())
    {block : Block} (blockMember : block ∈ func.blocks.toList)
    (instruction : Inst.eff (.store address value origin) ∈ block.insts) :
    (ReplacementContentFlow.Model.write func state (flowAt state.values address) (flowAt state.values value)).CanonicalMemory
      func provenance := by
  apply before.write physical closed parameters payloadReference valueBound
  · intro slot storage row _ target
    have bounded : slot < provenance.slots.size := by
      rw [slots]
      exact (Array.getElem?_eq_some_iff.mp row).choose
    exact (RootsRefine.refl func (rootsAt provenance.vals value)).source_mono
      (provStep_store_roots bounded target quiet)
  · intro index mutability row target
    have slice := paramOk_refLike_payload parameters row payloadReference
    have sliceReference : (func.params[index]?).any Ty.isRefSlice = true := by simp [row,slice]
    obtain ⟨ceiling,annotation,bounded⟩ :=
      func.checkAdmittedRegions_store admitted blockMember instruction reference target sliceReference
    have exactCeiling : func.contentRoots index = ceiling := by
      rw [contentRoots_find unique index,annotation]
      rfl
    simpa only [exactCeiling] using bounded

#print axioms State.CanonicalMemory.load
#print axioms State.CanonicalMemory.load_closed

end Goose.GIR.ReplacementContentFlow.Model
