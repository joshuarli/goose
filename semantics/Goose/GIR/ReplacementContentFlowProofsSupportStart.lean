import Goose.GIR.ReplacementContentFlowProofsSupport

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem Atom.ofRootRef_injective : Function.Injective Atom.ofRootRef := by
  intro left right equal
  cases left <;> cases right <;> simp_all [Atom.ofRootRef]

theorem start_shape (f : Func) (vt : Array (Option VTy)) : (start f vt).Shape f := by
  constructor
  · cases found : f.blocks[0]? with
    | none => simp [start, found]
    | some entry =>
      rw [start_values_fold vt found]
      apply List.foldlRecOn (motive := fun (values : Array Roots) => values.size = f.numValues)
        entry.params.zipIdx _ (by simp)
      intro current known parameter _
      simpa using known
  all_goals
    cases found : f.blocks[0]? <;> simp [start, found, List.forIn_pure_yield_eq_foldl]

theorem ArrayBounded.replicate {α : Type} {predicate : α → Prop} (size : Nat) (value : α)
    (valid : predicate value) : ArrayBounded predicate (Array.replicate size value) := by
  intro current member
  have equal : current = value := (List.mem_replicate.mp (by simpa using member)).2
  simpa only [equal] using valid

theorem start_components (f : Func) (vt : Array (Option VTy)) :
    start f vt = { values := (start f vt).values
                   slots := Array.replicate f.slots.size .pending
                   contents := f.params.toArray.mapIdx fun index type =>
                     if type.isRefSlice then .known [.contents index] else .known []
                   writes := Array.replicate f.params.length .unchanged
                   returned := .known [] } := by
  cases found : f.blocks[0]? <;>
    simp [start, found, List.forIn_pure_yield_eq_foldl]

theorem start_returned (f : Func) (vt : Array (Option VTy)) :
    (start f vt).returned = .known [] := congrArg State.returned (start_components f vt)

theorem start_supported {m : Module} {f : Func} (vt : Array (Option VTy))
    (valid : annotationsValid m f = true)
    (entryBound : ∀ (entry : Block), f.blocks[0]? = some entry → entry.params.length ≤ f.params.length) :
    (start f vt).Supported (atomUniverse m f) := by
  have values : ArrayBounded (Roots.Supported (atomUniverse m f)) (start f vt).values := by
    cases found : f.blocks[0]? with
    | none => simpa [start, found] using
        ArrayBounded.replicate f.numValues Roots.pending (show Roots.pending.Supported (atomUniverse m f) from trivial)
    | some entry =>
      rw [start_values_fold vt found]
      apply List.foldlRecOn (motive := fun values => ArrayBounded (Roots.Supported (atomUniverse m f)) values)
        entry.params.zipIdx _ (ArrayBounded.replicate f.numValues Roots.pending trivial)
      intro current known parameter member
      apply known.set
      split
      · have bound := List.snd_lt_of_mem_zipIdx member
        have limit := entryBound entry found
        simpa [Roots.Supported] using (atomUniverse_param m f parameter.2).mpr (by omega)
      · simp [Roots.Supported]
  rw [start_components]
  constructor
  · exact values
  · exact ArrayBounded.replicate _ _ trivial
  · intro roots member
    obtain ⟨index, bound, equal⟩ : ∃ (index : Nat) (bound : index < f.params.length),
        (if f.params[index].isRefSlice then Roots.known [.contents index] else .known []) = roots := by
      simpa using member
    subst roots
    split
    · simpa [Roots.Supported] using (atomUniverse_contents m f index).mpr (by simpa using bound)
    · simp [Roots.Supported]
  · exact ArrayBounded.replicate _ _ trivial
  · simp [Roots.Supported]
  · simp [Roots.Supported]

def FunctionAddressesBounded (m : Module) (f : Func) : Prop :=
  (∀ block ∈ f.blocks.toList, ∀ inst ∈ block.insts,
    ∀ value slot, inst = .def value (.slotAddr slot) → slot < f.slots.size) ∧
  (∀ block ∈ f.blocks.toList, ∀ inst ∈ block.insts,
    ∀ value global, inst = .def value (.globalAddr global) → global < m.globals.size)

def ModuleFinite (m : Module) (states : Array State) : Prop :=
  ModuleSupported m states ∧ ModuleBounded m states

theorem moduleStart_finite (m : Module) (types : Array (Array (Option VTy)))
    (annotations : ∀ (index : Nat) (f : Func), m.funcs[index]? = some f → annotationsValid m f = true)
    (entries : ∀ (index : Nat) (f : Func), m.funcs[index]? = some f →
      ∀ (entry : Block), f.blocks[0]? = some entry → entry.params.length ≤ f.params.length) :
    ModuleFinite m (moduleStart m types) := by
  have supported : ModuleSupported m (moduleStart m types) := by
    intro index f state found produced
    simp only [moduleStart, Array.getElem?_mapIdx, found, Option.map_some] at produced
    cases produced
    exact start_supported _ (annotations index f found) (entries index f found)
  refine ⟨supported, ⟨by simp [moduleStart], ?_⟩⟩
  intro index f state found produced
  have within := (supported index f state found produced).bounded
  rw [atomUniverse_length] at within
  refine ⟨within, ?_⟩
  simp only [moduleStart, Array.getElem?_mapIdx, found, Option.map_some] at produced
  cases produced
  exact start_shape _ _

theorem moduleRound_finite {m : Module} {types : Array (Array (Option VTy))} {states : Array State}
    (addresses : ∀ (index : Nat) (f : Func), m.funcs[index]? = some f → FunctionAddressesBounded m f)
    (valid : ModuleFinite m states) : ModuleFinite m (moduleRound m types states) := by
  have supported : ModuleSupported m (moduleRound m types states) := by
    intro index f state found produced
    have functionBound : index < m.funcs.size := (Array.getElem?_eq_some_iff.mp found).choose
    have stateBound : index < states.size := by have := valid.2.size; omega
    have inputAt : states[index]? = some states[index] := Array.getElem?_eq_getElem stateBound
    have input := valid.1 index f states[index] found inputAt
    simp only [moduleRound, Array.getElem?_mapIdx, found, Option.map_some, inputAt, Option.getD_some] at produced
    cases produced
    exact round_supported valid.1 input _ (addresses index f found).1 (addresses index f found).2
  refine ⟨supported, ⟨by simp [moduleRound], ?_⟩⟩
  intro index f state found produced
  have within := (supported index f state found produced).bounded
  rw [atomUniverse_length] at within
  refine ⟨within, ?_⟩
  have functionBound : index < m.funcs.size := (Array.getElem?_eq_some_iff.mp found).choose
  have stateBound : index < states.size := by have := valid.2.size; omega
  have inputAt : states[index]? = some states[index] := Array.getElem?_eq_getElem stateBound
  have inputShape := (valid.2.state index f states[index] found inputAt).2
  simp only [moduleRound, Array.getElem?_mapIdx, found, Option.map_some, inputAt, Option.getD_some] at produced
  cases produced
  exact (round_extends _ _ _ _ _).shape inputShape

theorem close_success_of_finite (m : Module) (types : Array (Array (Option VTy)))
    (annotations : ∀ (index : Nat) (f : Func), m.funcs[index]? = some f → annotationsValid m f = true)
    (entries : ∀ (index : Nat) (f : Func), m.funcs[index]? = some f →
      ∀ (entry : Block), f.blocks[0]? = some entry → entry.params.length ≤ f.params.length)
    (addresses : ∀ (index : Nat) (f : Func), m.funcs[index]? = some f → FunctionAddressesBounded m f) :
    ∃ result, close m types = some result := by
  apply closeFrom_success_of_bounded_rank (moduleHeight m) (ModuleFinite m) (moduleFuel m - 1)
    (fun _ => moduleRound_finite addresses)
  · intro states valid
    have within := moduleHeight_le_fuel valid.2
    omega
  · intro states valid changed
    exact moduleRound_height_lt valid.2 changed
  · exact moduleStart_finite m types annotations entries
  · have within := moduleHeight_le_fuel (moduleStart_finite m types annotations entries).2
    omega

theorem closeFrom_finite {m : Module} {types : Array (Array (Option VTy))}
    (addresses : ∀ (index : Nat) (f : Func), m.funcs[index]? = some f → FunctionAddressesBounded m f)
    {fuel : Nat} {initial result : Array State} (valid : ModuleFinite m initial)
    (closed : closeFrom m types fuel initial = some result) : ModuleFinite m result := by
  induction fuel generalizing initial with
  | zero => simp [closeFrom] at closed
  | succ fuel ih =>
    simp only [closeFrom] at closed
    split at closed
    · cases closed; exact valid
    · exact ih (moduleRound_finite addresses valid) closed

theorem close_finite (m : Module) (types : Array (Array (Option VTy)))
    (annotations : ∀ (index : Nat) (f : Func), m.funcs[index]? = some f → annotationsValid m f = true)
    (entries : ∀ (index : Nat) (f : Func), m.funcs[index]? = some f →
      ∀ (entry : Block), f.blocks[0]? = some entry → entry.params.length ≤ f.params.length)
    (addresses : ∀ (index : Nat) (f : Func), m.funcs[index]? = some f → FunctionAddressesBounded m f) :
    ∃ result, close m types = some result ∧ ModuleFinite m result ∧ moduleRound m types result = result := by
  obtain ⟨result, closed⟩ := close_success_of_finite m types annotations entries addresses
  exact ⟨result, closed, closeFrom_finite addresses (moduleStart_finite m types annotations entries) closed,
    close_fixed closed⟩

theorem slotAddr_inBounds (env : TyEnv) (slot : SlotId) (type : VTy)
    (typed : (Op.slotAddr slot).resultTy env = .ok type) : slot < env.slots.size := by
  cases found : env.slots[slot]? with
  | none => simp [Op.resultTy, found, tyErr] at typed
  | some value => exact (Array.getElem?_eq_some_iff.mp found).choose

theorem globalAddr_inBounds (env : TyEnv) (global : GlobalId) (type : VTy)
    (typed : (Op.globalAddr global).resultTy env = .ok type) : global < env.globals.size := by
  cases found : env.globals[global]? with
  | none => simp [Op.resultTy, found, tyErr] at typed
  | some value => exact (Array.getElem?_eq_some_iff.mp found).choose

#print axioms Atom.ofRootRef_injective
#print axioms start_shape
#print axioms start_returned
#print axioms start_supported
#print axioms moduleStart_finite
#print axioms moduleRound_finite
#print axioms close_success_of_finite
#print axioms close_finite
#print axioms slotAddr_inBounds
#print axioms globalAddr_inBounds

end Goose.GIR.ReplacementContentFlow.Model
