import Goose.GIR.ReplacementContentFlowProofsOrder
import Goose.GIR.ReplacementContentFlowProofs

namespace Goose.GIR.ReplacementContentFlow.Model

def Roots.Bounded (bound : Nat) : Roots → Prop
  | .known roots => roots.length ≤ bound
  | _ => True

def Roots.height (bound : Nat) : Roots → Nat
  | .pending => 0
  | .known roots => roots.length + 1
  | .unknown => bound + 2

theorem Roots.height_le (bound : Nat) (roots : Roots) (bounded : roots.Bounded bound) :
    roots.height bound ≤ bound + 2 := by
  cases roots <;> simp_all [Roots.Bounded, Roots.height] <;> omega

theorem Roots.Extends.height_le {bound : Nat} {before after : Roots}
    (growth : before.Extends after) (bounded : before.Bounded bound) :
    before.height bound ≤ after.height bound := by
  cases before <;> cases after <;> simp_all [Roots.Extends, Roots.Bounded, Roots.height]
  · exact growth.length_le
  · omega

theorem Roots.Extends.eq_of_height_eq {bound : Nat} {before after : Roots}
    (growth : before.Extends after) (bounded : before.Bounded bound)
    (same : before.height bound = after.height bound) : before = after := by
  cases before <;> cases after <;> simp_all [Roots.Extends, Roots.Bounded, Roots.height]
  · exact growth.eq_of_length_le (by omega)
  · omega

def Write.Bounded (bound : Nat) : Write → Prop
  | .unchanged => True
  | .assigned roots => roots.Bounded bound

def Write.height (bound : Nat) : Write → Nat
  | .unchanged => 0
  | .assigned roots => roots.height bound + 1

theorem Write.height_le (bound : Nat) (write : Write) (bounded : write.Bounded bound) :
    write.height bound ≤ bound + 3 := by
  cases write with
  | unchanged => simp [Write.height]
  | assigned roots => have known := Roots.height_le bound roots bounded; simpa [Write.height] using Nat.add_le_add_right known 1

theorem Write.Extends.height_le {bound : Nat} {before after : Write}
    (growth : before.Extends after) (bounded : before.Bounded bound) :
    before.height bound ≤ after.height bound := by
  cases before <;> cases after <;> simp_all [Write.Extends, Write.height, Write.Bounded]
  exact Roots.Extends.height_le growth bounded

theorem Write.Extends.eq_of_height_eq {bound : Nat} {before after : Write}
    (growth : before.Extends after) (bounded : before.Bounded bound)
    (same : before.height bound = after.height bound) : before = after := by
  cases before <;> cases after <;> simp_all [Write.Extends, Write.height, Write.Bounded]
  exact Roots.Extends.eq_of_height_eq growth bounded same

def arrayHeight {α : Type} (height : α → Nat) (values : Array α) : Nat :=
  (values.toList.map height).sum

def ArrayBounded {α : Type} (predicate : α → Prop) (values : Array α) : Prop :=
  ∀ value ∈ values.toList, predicate value

theorem arrayHeight_le {α : Type} (height : α → Nat) (bound : Nat) (values : Array α)
    (bounded : ArrayBounded (fun value => height value ≤ bound) values) :
    arrayHeight height values ≤ values.size * bound := by
  unfold arrayHeight
  suffices ∀ (list : List α), (∀ value ∈ list, height value ≤ bound) →
      (list.map height).sum ≤ list.length * bound by
    simpa using this values.toList bounded
  intro list valid
  induction list with
  | nil => simp
  | cons head tail ih =>
    have first := valid head (by simp)
    have rest := ih (fun value member => valid value (List.mem_cons_of_mem head member))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [Nat.succ_mul]
    omega

theorem arrayHeight_comparison {α : Type} {default : α} {relation : α → α → Prop}
    (height : α → Nat) (predicate : α → Prop)
    (growing : ∀ {before after}, predicate before → relation before after → height before ≤ height after)
    (strict : ∀ {before after}, predicate before → relation before after → height before = height after → before = after)
    {before after : Array α} (valid : ArrayBounded predicate before)
    (growth : ArrayExtends default relation before after) :
    arrayHeight height before ≤ arrayHeight height after ∧
      (arrayHeight height before = arrayHeight height after → before = after) := by
  have cells : ∀ (index : Nat) (a b : α), before[index]? = some a → after[index]? = some b →
      relation a b := by
    intro index a b left right
    simpa only [left, right, Option.getD_some] using growth.values index
  have paired : ∀ (left right : List α), left.length = right.length →
      (∀ value ∈ left, predicate value) →
      (∀ (index : Nat) a b, left[index]? = some a → right[index]? = some b → relation a b) →
      (left.map height).sum ≤ (right.map height).sum ∧
        ((left.map height).sum = (right.map height).sum → left = right) := by
    intro left
    induction left with
    | nil => intro right sizes _ _; cases right <;> simp_all
    | cons head tail ih =>
      intro right sizes bounded relations
      cases right with
      | nil => simp at sizes
      | cons first rest =>
        have bound := bounded head (by simp)
        have related := relations 0 head first rfl rfl
        have firstGrowth := growing bound related
        have remaining := ih rest (by simpa using sizes)
          (fun value member => bounded value (List.mem_cons_of_mem head member))
          (fun index a b left right => relations (index + 1) a b left right)
        simp only [List.map_cons, List.sum_cons]
        constructor
        · omega
        · intro equal
          have firstEqual : height head = height first := by omega
          have restEqual : (tail.map height).sum = (rest.map height).sum := by omega
          cases strict bound related firstEqual
          cases remaining.2 restEqual
          rfl
  have comparison := paired before.toList after.toList (by simpa using growth.size) valid (by simpa using cells)
  exact ⟨comparison.1, fun same => Array.toList_inj.mp (comparison.2 same)⟩

structure State.Bounded (bound : Nat) (state : State) : Prop where
  values : ArrayBounded (Roots.Bounded bound) state.values
  slots : ArrayBounded (Roots.Bounded bound) state.slots
  contents : ArrayBounded (Roots.Bounded bound) state.contents
  writes : ArrayBounded (Write.Bounded bound) state.writes
  touched : state.touched.Bounded bound
  returned : state.returned.Bounded bound

def State.height (bound : Nat) (state : State) : Nat :=
  arrayHeight (Roots.height bound) state.values + arrayHeight (Roots.height bound) state.slots +
  arrayHeight (Roots.height bound) state.contents + arrayHeight (Write.height bound) state.writes +
  state.touched.height bound + state.returned.height bound

theorem State.Extends.height_comparison {bound : Nat} {before after : State}
    (valid : before.Bounded bound) (growth : before.Extends after) :
    before.height bound ≤ after.height bound ∧
      (before.height bound = after.height bound → before = after) := by
  have values := arrayHeight_comparison (Roots.height bound) (Roots.Bounded bound)
    (fun bounded related => related.height_le bounded)
    (fun bounded related => related.eq_of_height_eq bounded) valid.values growth.values
  have slots := arrayHeight_comparison (Roots.height bound) (Roots.Bounded bound)
    (fun bounded related => related.height_le bounded)
    (fun bounded related => related.eq_of_height_eq bounded) valid.slots growth.slots
  have contents := arrayHeight_comparison (Roots.height bound) (Roots.Bounded bound)
    (fun bounded related => related.height_le bounded)
    (fun bounded related => related.eq_of_height_eq bounded) valid.contents growth.contents
  have writes := arrayHeight_comparison (Write.height bound) (Write.Bounded bound)
    (fun bounded related => related.height_le bounded)
    (fun bounded related => related.eq_of_height_eq bounded) valid.writes growth.writes
  have touched := growth.touched.height_le valid.touched
  have returned := growth.returned.height_le valid.returned
  constructor
  · unfold State.height
    omega
  · intro equal
    unfold State.height at equal
    have valuesEq := values.2 (by omega)
    have slotsEq := slots.2 (by omega)
    have contentsEq := contents.2 (by omega)
    have writesEq := writes.2 (by omega)
    have touchedEq := growth.touched.eq_of_height_eq valid.touched (by omega)
    have returnedEq := growth.returned.eq_of_height_eq valid.returned (by omega)
    cases before
    cases after
    cases valuesEq
    cases slotsEq
    cases contentsEq
    cases writesEq
    cases touchedEq
    cases returnedEq
    rfl

theorem State.Extends.height_lt_of_ne {bound : Nat} {before after : State}
    (valid : before.Bounded bound) (growth : before.Extends after) (changed : after ≠ before) :
    before.height bound < after.height bound := by
  have comparison := growth.height_comparison valid
  have different : before.height bound ≠ after.height bound := fun equal => changed (comparison.2 equal).symm
  omega

structure State.Shape (f : Func) (state : State) : Prop where
  values : state.values.size = f.numValues
  slots : state.slots.size = f.slots.size
  contents : state.contents.size = f.params.length
  writes : state.writes.size = f.params.length

theorem State.height_le_shape {bound : Nat} {f : Func} {state : State}
    (valid : state.Bounded bound) (shape : state.Shape f) :
    state.height bound ≤ (f.numValues + f.slots.size + 2 * f.params.length + 2) * (bound + 3) := by
  have values := arrayHeight_le (Roots.height bound) (bound + 3) state.values
    (fun value member => Nat.le_trans (Roots.height_le _ _ (valid.values value member)) (by omega))
  have slots := arrayHeight_le (Roots.height bound) (bound + 3) state.slots
    (fun value member => Nat.le_trans (Roots.height_le _ _ (valid.slots value member)) (by omega))
  have contents := arrayHeight_le (Roots.height bound) (bound + 3) state.contents
    (fun value member => Nat.le_trans (Roots.height_le _ _ (valid.contents value member)) (by omega))
  have writes := arrayHeight_le (Write.height bound) (bound + 3) state.writes
    (fun value member => Write.height_le _ _ (valid.writes value member))
  have touched := Roots.height_le _ _ valid.touched
  have returned := Roots.height_le _ _ valid.returned
  unfold State.height
  rw [shape.values] at values
  rw [shape.slots] at slots
  rw [shape.contents] at contents
  rw [shape.writes] at writes
  simp only [Nat.add_mul, Nat.mul_succ, Nat.succ_mul] at *
  omega

theorem State.height_le_capacity {m : Module} {f : Func} {state : State}
    (valid : state.Bounded (m.globals.size + f.slots.size + 2 * f.params.length))
    (shape : state.Shape f) : state.height (m.globals.size + f.slots.size + 2 * f.params.length) ≤ capacity m f := by
  apply Nat.le_trans (State.height_le_shape valid shape)
  unfold capacity
  apply Nat.mul_le_mul_right
  omega

def indexedHeight (size : Nat) (height : Nat → Nat) : Nat :=
  ((List.range size).map height).sum

theorem indexedHeight_comparison (size : Nat) (before after : Nat → Nat)
    (growth : ∀ index < size, before index ≤ after index) :
    indexedHeight size before ≤ indexedHeight size after ∧
      (indexedHeight size before = indexedHeight size after → ∀ index < size, before index = after index) := by
  induction size with
  | zero => simp [indexedHeight]
  | succ size ih =>
    have earlier := ih (fun index bounded => growth index (by omega))
    have last := growth size (by omega)
    simp only [indexedHeight, List.range_succ, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at *
    constructor
    · omega
    · intro equal index bounded
      by_cases atLast : index = size
      · subst index; omega
      · exact earlier.2 (by omega) index (by omega)

def functionAtomBound (m : Module) (f : Func) : Nat :=
  m.globals.size + f.slots.size + 2 * f.params.length

def State.empty : State :=
  { values := #[], slots := #[], contents := #[], writes := #[] }

def moduleCellHeight (m : Module) (states : Array State) (index : Nat) : Nat :=
  match m.funcs[index]?, states[index]? with
  | some f, some state => state.height (functionAtomBound m f)
  | _, _ => 0

def moduleHeight (m : Module) (states : Array State) : Nat :=
  indexedHeight m.funcs.size (moduleCellHeight m states)

structure ModuleBounded (m : Module) (states : Array State) : Prop where
  size : states.size = m.funcs.size
  state : ∀ (index : Nat) (f : Func) (state : State), m.funcs[index]? = some f → states[index]? = some state →
    state.Bounded (functionAtomBound m f) ∧ state.Shape f

theorem moduleRound_extends {m : Module} {types : Array (Array (Option VTy))}
    {states : Array State} (sizes : states.size = m.funcs.size) :
    ArrayExtends State.empty State.Extends states (moduleRound m types states) := by
  constructor
  · simpa [moduleRound] using sizes
  · intro index
    by_cases bound : index < m.funcs.size
    · have stateBound : index < states.size := by omega
      simp only [moduleRound, Array.getElem?_mapIdx, Array.getElem?_eq_getElem bound,
        Option.map_some, Option.getD_some, Array.getElem?_eq_getElem stateBound]
      exact round_extends _ _ _ _ _
    · have absent : m.funcs[index]? = none := Array.getElem?_eq_none_iff.mpr (by omega)
      have absentState : states[index]? = none := Array.getElem?_eq_none_iff.mpr (by omega)
      simp only [moduleRound, Array.getElem?_mapIdx, absent, absentState, Option.map_none, Option.getD_none]
      exact State.Extends.refl _

theorem moduleHeight_comparison {m : Module} {before after : Array State}
    (valid : ModuleBounded m before)
    (growth : ArrayExtends State.empty State.Extends before after) :
    moduleHeight m before ≤ moduleHeight m after ∧
      (moduleHeight m before = moduleHeight m after → before = after) := by
  have cellComparison : ∀ index < m.funcs.size,
      moduleCellHeight m before index ≤ moduleCellHeight m after index ∧
      (moduleCellHeight m before index = moduleCellHeight m after index → before[index]? = after[index]?) := by
    intro index bounded
    have sizes := valid.size
    have leftBound : index < before.size := by omega
    have rightBound : index < after.size := by have := growth.size; omega
    have model := valid.state index m.funcs[index] before[index]
      (Array.getElem?_eq_getElem bounded) (Array.getElem?_eq_getElem leftBound)
    have related := growth.values index
    simp only [Array.getElem?_eq_getElem leftBound, Array.getElem?_eq_getElem rightBound, Option.getD_some] at related
    have comparison := related.height_comparison model.1
    simp only [moduleCellHeight, Array.getElem?_eq_getElem bounded, Array.getElem?_eq_getElem leftBound,
      Array.getElem?_eq_getElem rightBound]
    exact ⟨comparison.1, fun same => congrArg some (comparison.2 same)⟩
  have comparison := indexedHeight_comparison m.funcs.size _ _
    (fun index bounded => (cellComparison index bounded).1)
  refine ⟨comparison.1, ?_⟩
  intro same
  apply Array.ext growth.size
  intro index leftBound rightBound
  have bounded : index < m.funcs.size := by have := valid.size; omega
  have equal := (cellComparison index bounded).2 (comparison.2 same index bounded)
  simpa only [Array.getElem?_eq_getElem leftBound, Array.getElem?_eq_getElem rightBound, Option.some.injEq] using equal

theorem moduleRound_height_lt {m : Module} {types : Array (Array (Option VTy))}
    {states : Array State} (valid : ModuleBounded m states)
    (changed : moduleRound m types states ≠ states) :
    moduleHeight m states < moduleHeight m (moduleRound m types states) := by
  have comparison := moduleHeight_comparison valid (moduleRound_extends (types := types) valid.size)
  have different : moduleHeight m states ≠ moduleHeight m (moduleRound m types states) :=
    fun equal => changed (comparison.2 equal).symm
  omega

theorem indexedHeight_array {α : Type} (height : α → Nat) (values : Array α) :
    indexedHeight values.size (fun index => ((values[index]?).map height).getD 0) = arrayHeight height values := by
  unfold indexedHeight arrayHeight
  congr 1
  apply List.ext_getElem?
  intro index
  by_cases bounded : index < values.size
  · simp [List.getElem?_map, List.getElem?_range bounded, Array.getElem?_eq_getElem bounded]
  · have rangeAbsent : (List.range values.size)[index]? = none := List.getElem?_eq_none_iff.mpr (by simpa using bounded)
    have arrayAbsent : values[index]? = none := Array.getElem?_eq_none_iff.mpr (by omega)
    simp only [List.getElem?_map, rangeAbsent, Option.map_none, Array.getElem?_toList, arrayAbsent]

theorem moduleFuel_eq (m : Module) : moduleFuel m = arrayHeight (capacity m) m.funcs + 1 := by
  have seeded : ∀ (list : List Func) (seed : Nat),
      list.foldl (fun acc f => acc + capacity m f) seed = seed + (list.map (capacity m)).sum := by
    intro list
    induction list with
    | nil => intro seed; simp
    | cons head rest ih => intro seed; simp only [List.foldl_cons, ih, List.map_cons, List.sum_cons, Nat.add_assoc]
  unfold moduleFuel arrayHeight
  rw [← Array.foldl_toList, seeded]
  omega

theorem moduleHeight_le_fuel {m : Module} {states : Array State}
    (valid : ModuleBounded m states) : moduleHeight m states < moduleFuel m := by
  have comparison := indexedHeight_comparison m.funcs.size (moduleCellHeight m states)
    (fun index => ((m.funcs[index]?).map (capacity m)).getD 0) (by
      intro index bounded
      have stateBound : index < states.size := by have := valid.size; omega
      have model := valid.state index m.funcs[index] states[index]
        (Array.getElem?_eq_getElem bounded) (Array.getElem?_eq_getElem stateBound)
      simpa only [moduleCellHeight, functionAtomBound, Array.getElem?_eq_getElem bounded,
        Array.getElem?_eq_getElem stateBound, Option.map_some, Option.getD_some] using
        State.height_le_capacity (m := m) (f := m.funcs[index]) (state := states[index]) model.1 model.2)
  rw [indexedHeight_array] at comparison
  have fuel := moduleFuel_eq m
  exact Nat.lt_of_le_of_lt comparison.1 (by omega)

theorem closeFrom_success_of_module_bound {m : Module} {types : Array (Array (Option VTy))}
    (preserved : ∀ states, ModuleBounded m states → ModuleBounded m (moduleRound m types states))
    {initial : Array State} (valid : ModuleBounded m initial) :
    ∃ result, closeFrom m types (moduleFuel m) initial = some result := by
  apply closeFrom_success_of_bounded_rank (moduleHeight m) (ModuleBounded m) (moduleFuel m - 1)
    preserved
  · intro states bounded
    have known := moduleHeight_le_fuel bounded
    omega
  · intro states bounded changed
    exact moduleRound_height_lt bounded changed
  · exact valid
  · have positive := moduleHeight_le_fuel valid
    omega

#print axioms Roots.Extends.eq_of_height_eq
#print axioms Write.Extends.eq_of_height_eq
#print axioms arrayHeight_comparison
#print axioms State.Extends.height_comparison
#print axioms State.Extends.height_lt_of_ne
#print axioms State.height_le_capacity
#print axioms moduleRound_extends
#print axioms moduleHeight_comparison
#print axioms moduleRound_height_lt
#print axioms moduleFuel_eq
#print axioms moduleHeight_le_fuel
#print axioms closeFrom_success_of_module_bound

end Goose.GIR.ReplacementContentFlow.Model
