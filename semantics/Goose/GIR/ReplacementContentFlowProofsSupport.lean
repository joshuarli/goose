import Goose.GIR.ReplacementContentFlowProofsRank

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem list_nodup_eraseDups {α : Type} [BEq α] [LawfulBEq α] (values : List α) :
    values.eraseDups.Nodup := by
  cases values with
  | nil => simp
  | cons first rest =>
    rw [List.eraseDups_cons, List.nodup_cons]
    constructor
    · simp only [List.mem_eraseDups, List.mem_filter]
      simp
    · exact list_nodup_eraseDups (rest.filter fun value => !value == first)
termination_by values.length
decreasing_by
  have bound := List.length_filter_le (fun value => !value == first) rest
  simp only [List.length_cons]
  omega

def atomUniverse (m : Module) (f : Func) : List Atom :=
  (List.range f.slots.size).map Atom.local ++ (List.range m.globals.size).map Atom.global ++
  (List.range f.params.length).map Atom.param ++ (List.range f.params.length).map Atom.contents

theorem atomUniverse_length (m : Module) (f : Func) :
    (atomUniverse m f).length = functionAtomBound m f := by
  simp [atomUniverse, functionAtomBound]
  omega

def Roots.Supported (atoms : List Atom) : Roots → Prop
  | .known roots => roots.Nodup ∧ roots ⊆ atoms
  | _ => True

theorem Roots.Supported.bounded {atoms : List Atom} {roots : Roots}
    (valid : roots.Supported atoms) : roots.Bounded atoms.length := by
  cases roots with
  | pending => trivial
  | unknown => trivial
  | known list => exact valid.1.length_le_of_subset valid.2

theorem Roots.Supported.join {atoms : List Atom} {before added : Roots}
    (valid : before.Supported atoms) (introduced : added.Supported atoms) :
    (before.join added).Supported atoms := by
  cases before <;> cases added <;> simp_all [Roots.join, Roots.Supported]
  rename_i left right
  apply List.foldlRecOn (motive := fun current => current.Nodup ∧ current ⊆ atoms)
    right _ valid
  intro current accumulated root member
  split
  · exact accumulated
  · rename_i absent
    constructor
    · rw [List.nodup_append]
      refine ⟨accumulated.1, by simp, ?_⟩
      intro a included b singleton
      have equal : b = root := by simpa using singleton
      subst b
      intro same
      subst a
      exact absent included
    · intro a included
      rcases List.mem_append.mp included with earlier | singleton
      · exact accumulated.2 earlier
      · have equal : a = root := by simpa using singleton
        subst a
        exact introduced.2 member

def Roots.Forall (predicate : Atom → Prop) : Roots → Prop
  | .known roots => ∀ root ∈ roots, predicate root
  | _ => True

theorem Roots.Supported.bind {atoms : List Atom} (roots : Roots) (map : Atom → Roots)
    (mapped : roots.Forall fun atom => (map atom).Supported atoms) :
    (roots.bind map).Supported atoms := by
  cases roots with
  | pending => trivial
  | unknown => trivial
  | known list =>
    unfold Roots.bind
    apply List.foldlRecOn (motive := fun (current : Roots) => current.Supported atoms)
      list _ (by simp [Roots.Supported])
    intro current valid root member
    have known := mapped root member
    cases current <;> cases equation : map root <;>
      simp_all only [Roots.Supported]
    exact Roots.Supported.join (before := .known _) (added := .known _) valid known

def Write.Supported (atoms : List Atom) : Write → Prop
  | .unchanged => True
  | .assigned roots => roots.Supported atoms

theorem Write.Supported.bounded {atoms : List Atom} {write : Write}
    (valid : write.Supported atoms) : write.Bounded atoms.length := by
  cases write with
  | unchanged => trivial
  | assigned roots => exact Roots.Supported.bounded valid

theorem Write.Supported.join {atoms : List Atom} {before added : Write}
    (valid : before.Supported atoms) (introduced : added.Supported atoms) :
    (before.join added).Supported atoms := by
  cases before <;> cases added <;> simp_all [Write.join, Write.Supported]
  exact valid.join introduced

structure State.Supported (atoms : List Atom) (state : State) : Prop where
  values : ArrayBounded (Roots.Supported atoms) state.values
  slots : ArrayBounded (Roots.Supported atoms) state.slots
  contents : ArrayBounded (Roots.Supported atoms) state.contents
  writes : ArrayBounded (Write.Supported atoms) state.writes
  touched : state.touched.Supported atoms
  returned : state.returned.Supported atoms

theorem State.Supported.bounded {atoms : List Atom} {state : State}
    (valid : state.Supported atoms) : state.Bounded atoms.length :=
  ⟨fun _ member => (valid.values _ member).bounded,
   fun _ member => (valid.slots _ member).bounded,
   fun _ member => (valid.contents _ member).bounded,
   fun _ member => (valid.writes _ member).bounded,
   valid.touched.bounded, valid.returned.bounded⟩

theorem ArrayBounded.getD {α : Type} {predicate : α → Prop} {values : Array α}
    (valid : ArrayBounded predicate values) (index : Nat) (fallback : α) (defaultValid : predicate fallback) :
    predicate (values[index]?.getD fallback) := by
  cases equation : values[index]? with
  | none => exact defaultValid
  | some value => exact valid value (List.mem_of_getElem? (by simpa using equation))

theorem ArrayBounded.set {α : Type} {predicate : α → Prop} {values : Array α}
    (valid : ArrayBounded predicate values) (index : Nat) (value : α) (newValid : predicate value) :
    ArrayBounded predicate (values.set! index value) := by
  intro current member
  have cases : current ∈ values.toList ∨ current = value :=
    List.mem_or_eq_of_mem_set (by simpa using member)
  rcases cases with earlier | equal
  · exact valid current (by simpa using earlier)
  · simpa only [equal] using newValid

theorem ArrayBounded.map {α β : Type} {predicate : α → Prop} {next : β → Prop}
    {values : Array α} (valid : ArrayBounded predicate values) (map : α → β)
    (mapped : ∀ value, predicate value → next (map value)) : ArrayBounded next (values.map map) := by
  intro result member
  rw [Array.toList_map, List.mem_map] at member
  obtain ⟨value, original, equal⟩ := member
  subst result
  exact mapped value (valid value original)

theorem flowAt_supported {atoms : List Atom} {values : Array Roots}
    (valid : ArrayBounded (Roots.Supported atoms) values) (index : Nat) :
    (flowAt values index).Supported atoms :=
  valid.getD index .unknown trivial

theorem addFlow_supported {atoms : List Atom} {values : Array Roots}
    (valid : ArrayBounded (Roots.Supported atoms) values) (index : Nat) (roots : Roots)
    (introduced : roots.Supported atoms) : ArrayBounded (Roots.Supported atoms) (addFlow values index roots) :=
  valid.set index _ ((flowAt_supported valid index).join introduced)

theorem content_supported {atoms : List Atom} {f : Func} {state : State}
    (valid : state.Supported atoms) (address : Roots) : (content f state address).Supported atoms := by
  apply Roots.Supported.bind
  cases address with
  | pending => trivial
  | unknown => trivial
  | known roots =>
    intro root _
    cases root with
    | «local» slot => exact flowAt_supported valid.slots slot
    | param index =>
      simp only
      split
      · exact flowAt_supported valid.contents index
      · trivial
    | global index => trivial
    | contents index => trivial

theorem publicTouches_supported {atoms : List Atom} {roots : Roots}
    (valid : roots.Supported atoms) : (publicTouches roots).Supported atoms := by
  apply Roots.Supported.bind
  cases roots with
  | pending => trivial
  | unknown => trivial
  | known list =>
    intro root member
    cases root <;> simp_all [Roots.Supported]
    all_goals exact valid.2 member

theorem atomUniverse_global (m : Module) (f : Func) (index : GlobalId) :
    Atom.global index ∈ atomUniverse m f ↔ index < m.globals.size := by
  simp [atomUniverse, List.mem_append, List.mem_map]

theorem atomUniverse_local (m : Module) (f : Func) (index : SlotId) :
    Atom.local index ∈ atomUniverse m f ↔ index < f.slots.size := by
  simp [atomUniverse, List.mem_append, List.mem_map]

theorem atomUniverse_param (m : Module) (f : Func) (index : Nat) :
    Atom.param index ∈ atomUniverse m f ↔ index < f.params.length := by
  simp [atomUniverse, List.mem_append, List.mem_map]

theorem atomUniverse_contents (m : Module) (f : Func) (index : Nat) :
    Atom.contents index ∈ atomUniverse m f ↔ index < f.params.length := by
  simp [atomUniverse, List.mem_append, List.mem_map]

theorem substitute_supported {m : Module} {callee f : Func} {state : State} {roots : Roots}
    (valid : state.Supported (atomUniverse m f)) (args : List ValueId)
    (input : roots.Supported (atomUniverse m callee)) :
    (substitute f state args roots).Supported (atomUniverse m f) := by
  apply Roots.Supported.bind
  cases roots with
  | pending => trivial
  | unknown => trivial
  | known list =>
    intro root member
    cases root with
    | «local» slot => trivial
    | global index =>
      have bounded := (atomUniverse_global m callee index).mp (input.2 member)
      simpa [Roots.Supported] using (atomUniverse_global m f index).mpr bounded
    | param index =>
      dsimp only
      cases args[index]? with
      | none => trivial
      | some value => exact flowAt_supported valid.values value
    | contents index =>
      dsimp only
      cases args[index]? with
      | none => trivial
      | some value => exact content_supported valid _

theorem State.Supported.values_join {atoms : List Atom} {state : State}
    (valid : state.Supported atoms) (value : ValueId) (roots : Roots) (input : roots.Supported atoms) :
    ({ state with values := addFlow state.values value roots } : State).Supported atoms :=
  { valid with values := addFlow_supported valid.values value roots input }

theorem State.Supported.slots_join {atoms : List Atom} {state : State}
    (valid : state.Supported atoms) (slot : SlotId) (roots : Roots) (input : roots.Supported atoms) :
    ({ state with slots := addFlow state.slots slot roots } : State).Supported atoms :=
  { valid with slots := addFlow_supported valid.slots slot roots input }

theorem State.Supported.contents_join {atoms : List Atom} {state : State}
    (valid : state.Supported atoms) (index : Nat) (roots : Roots) (input : roots.Supported atoms) :
    ({ state with
        contents := addFlow state.contents index roots
        writes := state.writes.set! index
          ((state.writes[index]?.getD (.assigned .unknown)).join (.assigned roots)) } : State).Supported atoms :=
  { valid with
    contents := addFlow_supported valid.contents index roots input
    writes := valid.writes.set index _
      (Write.Supported.join (valid.writes.getD index (.assigned .unknown) trivial) input) }

theorem State.Supported.touched_join {atoms : List Atom} {state : State}
    (valid : state.Supported atoms) (roots : Roots) (input : roots.Supported atoms) :
    ({ state with touched := state.touched.join roots } : State).Supported atoms :=
  { valid with touched := valid.touched.join input }

theorem State.Supported.touched_unknown {atoms : List Atom} {state : State}
    (valid : state.Supported atoms) : ({ state with touched := .unknown } : State).Supported atoms :=
  { valid with touched := trivial }

theorem State.Supported.memory_unknown {atoms : List Atom} {state : State}
    (valid : state.Supported atoms) :
    ({ state with
        slots := state.slots.map fun _ => .unknown
        contents := state.contents.map fun _ => .unknown
        writes := state.writes.map fun _ => .assigned .unknown } : State).Supported atoms :=
  { valid with
    slots := valid.slots.map _ (by intros; trivial)
    contents := valid.contents.map _ (by intros; trivial)
    writes := valid.writes.map _ (by intros; trivial) }

theorem state_foldl_supported {α : Type} {atoms : List Atom} (values : List α)
    (update : State → α → State)
    (preserved : ∀ state, state.Supported atoms → ∀ value ∈ values, (update state value).Supported atoms)
    {state : State} (valid : state.Supported atoms) : (values.foldl update state).Supported atoms := by
  apply List.foldlRecOn (motive := fun state => state.Supported atoms) values update valid
  exact preserved

theorem write_supported {atoms : List Atom} {f : Func} {state : State}
    (valid : state.Supported atoms) (address roots : Roots) (input : roots.Supported atoms) :
    (write f state address roots).Supported atoms := by
  cases address with
  | pending => exact valid
  | unknown => exact valid.memory_unknown
  | known list =>
    apply state_foldl_supported
    · intro current accumulated root _
      cases root with
      | «local» slot => exact accumulated.slots_join _ _ input
      | global index => exact accumulated.touched_unknown
      | contents index => exact accumulated.touched_unknown
      | param index =>
        dsimp only
        split
        · exact accumulated.contents_join _ _ input
        · exact accumulated
    · exact valid

theorem state_forIn_supported {α : Type} {atoms : List Atom} (values : List α)
    (update : α → State → Id (ForInStep State))
    (preserved : ∀ value state, state.Supported atoms → match (update value state).run with
      | .done after | .yield after => after.Supported atoms)
    {state : State} (valid : state.Supported atoms) :
    (forIn values state update).run.Supported atoms := by
  induction values generalizing state with
  | nil => exact valid
  | cons value rest ih =>
    have next := preserved value state valid
    cases equation : (update value state).run with
    | done after => simpa [List.forIn_cons, equation] using next
    | yield after =>
      have nextValid : after.Supported atoms := by simpa [equation] using next
      simpa [List.forIn_cons, equation] using ih nextValid

def ModuleSupported (m : Module) (states : Array State) : Prop :=
  ∀ (index : Nat) (f : Func) (state : State),
    m.funcs[index]? = some f → states[index]? = some state → state.Supported (atomUniverse m f)

theorem callState_supported {m : Module} {states : Array State} {f : Func} {state : State}
    (inputs : ModuleSupported m states) (valid : state.Supported (atomUniverse m f))
    (fn : FnId) (args : List ValueId) :
    (callState m states f state fn args).1.Supported (atomUniverse m f) ∧
      (callState m states f state fn args).2.Supported (atomUniverse m f) := by
  cases calleeAt : m.funcs[fn]? with
  | none => simpa only [callState, calleeAt, Id.run_pure] using And.intro (show Roots.unknown.Supported (atomUniverse m f) from trivial) valid.touched_unknown
  | some callee =>
    cases effectsAt : states[fn]? with
    | none => simpa only [callState, calleeAt, effectsAt, Id.run_pure] using And.intro (show Roots.unknown.Supported (atomUniverse m f) from trivial) valid.touched_unknown
    | some effects =>
      have effectsValid := inputs fn callee effects calleeAt effectsAt
      simp only [callState, calleeAt, effectsAt, Id.run_bind, Id.run_pure]
      constructor
      · exact substitute_supported valid args effectsValid.returned
      · apply state_forIn_supported
        · intro parameter current currentValid
          by_cases isSlice : parameter.1.isRefSlice = true
          · simp only [isSlice, ↓reduceIte]
            have stored := effectsValid.writes.getD parameter.2 (.assigned .unknown) trivial
            cases equation : effects.writes[parameter.2]?.getD (.assigned .unknown) with
            | unchanged => exact currentValid
            | assigned roots =>
              rw [equation] at stored
              exact write_supported currentValid _ _ (substitute_supported valid args stored)
          · simpa [isSlice] using currentValid
        · exact valid.touched_join _ (substitute_supported valid args (publicTouches_supported effectsValid.touched))

theorem touchValues_supported {atoms : List Atom} {state : State}
    (valid : state.Supported atoms) (vt : Array (Option VTy)) (values : List ValueId) :
    (touchValues vt state values).Supported atoms := by
  unfold touchValues
  refine { valid with touched := ?_ }
  dsimp only
  apply List.foldlRecOn (motive := fun (roots : Roots) => roots.Supported atoms) values _ valid.touched
  intro current known value _
  split
  · exact known.join (flowAt_supported valid.values value)
  · exact known

theorem edge_supported {atoms : List Atom} {state : State} {f : Func}
    (valid : state.Supported atoms) (target : BlockId) (args : List ValueId) :
    (edge f state target args).Supported atoms := by
  unfold edge
  split
  · exact valid.touched_unknown
  · apply state_foldl_supported
    · intro current accumulated pair _
      exact accumulated.values_join _ _ (flowAt_supported accumulated.values _)
    · exact valid

theorem result_supported {m : Module} {f : Func} {state : State}
    (valid : state.Supported (atomUniverse m f)) (vt : Array (Option VTy))
    (value : ValueId) (op : Op)
    (slotBound : ∀ slot, op = .slotAddr slot → slot < f.slots.size)
    (globalBound : ∀ global, op = .globalAddr global → global < m.globals.size) :
    (result f vt state value op).Supported (atomUniverse m f) := by
  unfold result
  split
  · simp [Roots.Supported]
  · split
    all_goals first
      | exact flowAt_supported valid.values _
      | exact content_supported valid _
      | trivial
      | simp [Roots.Supported, atomUniverse_local, atomUniverse_global]
    all_goals first
      | exact slotBound _ rfl
      | exact globalBound _ rfl

theorem step_supported {m : Module} {states : Array State} {f : Func} {state : State}
    (inputs : ModuleSupported m states) (valid : state.Supported (atomUniverse m f))
    (vt : Array (Option VTy)) (inst : Inst)
    (slotBound : ∀ value slot, inst = .def value (.slotAddr slot) → slot < f.slots.size)
    (globalBound : ∀ value global, inst = .def value (.globalAddr global) → global < m.globals.size) :
    (step m states f vt state inst).Supported (atomUniverse m f) := by
  unfold step
  have exposed := touchValues_supported valid vt (sourceOperands inst)
  generalize touchValues vt state (sourceOperands inst) = current at *
  split
  · rename_i value fn args org
    have called := callState_supported inputs exposed fn args
    apply touchValues_supported
    apply called.2.values_join
    split
    · exact called.1
    · simp [Roots.Supported]
  · apply touchValues_supported
    apply exposed.values_join
    apply result_supported exposed vt
    · intro slot equal
      apply slotBound
      subst_vars
      rfl
    · intro global equal
      apply globalBound
      subst_vars
      rfl
  · exact exposed.slots_join _ _ (flowAt_supported exposed.values _)
  · split
    · exact write_supported exposed _ _ (flowAt_supported exposed.values _)
    · exact exposed
  · exact edge_supported exposed _ _
  · exact edge_supported (edge_supported exposed _ _) _ _
  · exact { exposed with returned := exposed.returned.join (flowAt_supported exposed.values _) }
  · exact exposed

theorem round_supported {m : Module} {states : Array State} {f : Func} {state : State}
    (inputs : ModuleSupported m states) (valid : state.Supported (atomUniverse m f))
    (vt : Array (Option VTy))
    (slotBounds : ∀ block ∈ f.blocks.toList, ∀ inst ∈ block.insts,
      ∀ value slot, inst = .def value (.slotAddr slot) → slot < f.slots.size)
    (globalBounds : ∀ block ∈ f.blocks.toList, ∀ inst ∈ block.insts,
      ∀ value global, inst = .def value (.globalAddr global) → global < m.globals.size) :
    (round m states f vt state).Supported (atomUniverse m f) := by
  unfold round
  rw [← Array.foldl_toList]
  apply state_foldl_supported
  · intro current accumulated block included
    apply state_foldl_supported
    · intro next nextValid inst member
      exact step_supported inputs nextValid vt inst
        (slotBounds block included inst member) (globalBounds block included inst member)
    · exact accumulated
  · exact valid

theorem State.Extends.shape {f : Func} {before after : State}
    (growth : before.Extends after) (valid : before.Shape f) : after.Shape f :=
  ⟨growth.values.size.symm.trans valid.values, growth.slots.size.symm.trans valid.slots,
   growth.contents.size.symm.trans valid.contents, growth.writes.size.symm.trans valid.writes⟩

theorem start_values_fold {f : Func} (vt : Array (Option VTy)) {entry : Block}
    (found : f.blocks[0]? = some entry) :
    (start f vt).values = entry.params.zipIdx.foldl (fun values parameter =>
      values.set! parameter.1.1
        (if valRefLike vt parameter.1.1 then .known [.param parameter.2] else .known []))
      (Array.replicate f.numValues Roots.pending) := by
  simp only [start, found, Id.run_bind, Id.run_pure]
  rw [List.forIn_pure_yield_eq_foldl]
  rfl

theorem array_foldl_set_unchanged {α β : Type} (items : List α) (key : α → Nat) (value : α → β)
    (index : Nat) (separate : ∀ item ∈ items, key item ≠ index) (initial : Array β) (fallback : β) :
    ((items.foldl (fun values item => values.set! (key item) (value item)) initial)[index]?).getD fallback =
      (initial[index]?).getD fallback := by
  induction items generalizing initial with
  | nil => rfl
  | cons head rest ih =>
    rw [List.foldl_cons, ih (fun item member => separate item (List.mem_cons_of_mem head member))]
    simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne
      (separate head (by simp)) ]

theorem array_foldl_set_lookup {α β : Type} (items : List α) (key : α → Nat) (value : α → β)
    (unique : (items.map key).Nodup) (item : α) (member : item ∈ items)
    (initial : Array β) (bounded : key item < initial.size) (fallback : β) :
    ((items.foldl (fun values next => values.set! (key next) (value next)) initial)[key item]?).getD fallback =
      value item := by
  induction items generalizing initial with
  | nil => simp at member
  | cons head rest ih =>
    have distinct := List.nodup_cons.mp unique
    rcases List.mem_cons.mp member with equal | later
    · subst item
      rw [List.foldl_cons, array_foldl_set_unchanged rest key value (key head) (by
        intro other included equal
        exact distinct.1 (List.mem_map.mpr ⟨other, included, equal⟩))]
      simp only [Array.set!_eq_setIfInBounds, Array.getD_getElem?_setIfInBounds, bounded, ite_true]
    · exact ih distinct.2 later _ (by simpa using bounded)

theorem start_parameter {f : Func} (vt : Array (Option VTy)) {entry : Block}
    (found : f.blocks[0]? = some entry) (unique : (entry.params.map (·.1)).Nodup)
    (index value : Nat) (type : VTy) (parameter : entry.params[index]? = some (value, type))
    (bounded : value < f.numValues) :
    flowAt (start f vt).values value =
      if valRefLike vt value then .known [.param index] else .known [] := by
  rw [start_values_fold vt found]
  unfold flowAt
  refine array_foldl_set_lookup entry.params.zipIdx (fun parameter => parameter.1.1)
    (fun parameter => if valRefLike vt parameter.1.1 then Roots.known [.param parameter.2] else .known [])
    ?_ ((value, type), index) ?_ _ ?_ .unknown
  · have mapEq : (entry.params.zipIdx.map fun parameter => parameter.1.1) = entry.params.map (·.1) := by
      calc
        _ = (entry.params.zipIdx.map Prod.fst).map Prod.fst := by simp only [List.map_map, Function.comp_def]
        _ = _ := by rw [List.zipIdx_map_fst]
    rw [mapEq]
    exact unique
  · exact List.mem_zipIdx_iff_getElem?.mpr parameter
  · simpa using bounded

#print axioms list_nodup_eraseDups
#print axioms atomUniverse_length
#print axioms Roots.Supported.join
#print axioms Roots.Supported.bind
#print axioms State.Supported.bounded
#print axioms content_supported
#print axioms publicTouches_supported
#print axioms substitute_supported
#print axioms write_supported
#print axioms callState_supported
#print axioms result_supported
#print axioms step_supported
#print axioms round_supported
#print axioms start_values_fold
#print axioms array_foldl_set_lookup
#print axioms start_parameter

end Goose.GIR.ReplacementContentFlow.Model
