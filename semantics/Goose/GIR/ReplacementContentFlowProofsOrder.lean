import Goose.GIR.ReplacementContentFlow

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

def Roots.Extends : Roots → Roots → Prop
  | .pending, _ => True
  | _, .unknown => True
  | .known before, .known after => before.Sublist after
  | _, _ => False

theorem Roots.Extends.refl (roots : Roots) : roots.Extends roots := by
  cases roots <;> simp [Roots.Extends]

theorem Roots.Extends.trans {before middle after : Roots}
    (first : before.Extends middle) (second : middle.Extends after) : before.Extends after := by
  cases before <;> cases middle <;> cases after <;> simp_all [Roots.Extends]
  exact first.trans second

theorem Roots.Extends.antisymm {before after : Roots}
    (first : before.Extends after) (second : after.Extends before) : before = after := by
  cases before <;> cases after <;> simp_all [Roots.Extends]
  exact first.eq_of_length_le second.length_le

theorem Roots.extends_join (before added : Roots) : before.Extends (before.join added) := by
  cases before with
  | pending => trivial
  | unknown => cases added <;> trivial
  | known roots =>
      cases added with
      | pending => exact List.Sublist.refl roots
      | unknown => trivial
      | known introduced =>
          change roots.Sublist _
          apply List.foldlRecOn (motive := fun current => roots.Sublist current)
            introduced _ (List.Sublist.refl roots)
          intro current known next _
          split
          · exact known
          · exact known.trans (List.sublist_append_left _ _)

def Write.Extends : Write → Write → Prop
  | .unchanged, _ => True
  | .assigned before, .assigned after => before.Extends after
  | _, _ => False

theorem Write.Extends.refl (write : Write) : write.Extends write := by
  cases write with
  | unchanged => trivial
  | assigned roots => exact Roots.Extends.refl roots

theorem Write.Extends.trans {before middle after : Write}
    (first : before.Extends middle) (second : middle.Extends after) : before.Extends after := by
  cases before <;> cases middle <;> cases after <;> simp_all [Write.Extends]
  exact first.trans second

theorem Write.Extends.antisymm {before after : Write}
    (first : before.Extends after) (second : after.Extends before) : before = after := by
  cases before <;> cases after <;> simp_all [Write.Extends]
  exact Roots.Extends.antisymm first second

theorem Write.extends_join (before added : Write) : before.Extends (before.join added) := by
  cases before <;> cases added <;> simp [Write.join, Write.Extends, Roots.Extends.refl, Roots.extends_join]

structure ArrayExtends {α : Type} (default : α) (relation : α → α → Prop)
    (before after : Array α) : Prop where
  size : before.size = after.size
  values : ∀ index : Nat, relation (before[index]?.getD default) (after[index]?.getD default)

theorem ArrayExtends.refl {α : Type} (default : α) (relation : α → α → Prop)
    (reflexive : ∀ value, relation value value) (values : Array α) :
    ArrayExtends default relation values values := ⟨rfl, fun _ => reflexive _⟩

theorem ArrayExtends.trans {α : Type} {default : α} {relation : α → α → Prop}
    (transitive : ∀ {a b c}, relation a b → relation b c → relation a c)
    {before middle after : Array α}
    (first : ArrayExtends default relation before middle)
    (second : ArrayExtends default relation middle after) : ArrayExtends default relation before after :=
  ⟨first.size.trans second.size, fun index => transitive (first.values index) (second.values index)⟩

theorem ArrayExtends.antisymm {α : Type} {default : α} {relation : α → α → Prop}
    (antisymmetric : ∀ {a b}, relation a b → relation b a → a = b)
    {before after : Array α}
    (first : ArrayExtends default relation before after)
    (second : ArrayExtends default relation after before) : before = after := by
  apply Array.ext first.size
  intro index beforeBound afterBound
  have equal := antisymmetric (first.values index) (second.values index)
  simpa only [Array.getElem?_eq_getElem beforeBound, Array.getElem?_eq_getElem afterBound,
    Option.getD_some] using equal

theorem ArrayExtends.set {α : Type} {default : α} {relation : α → α → Prop}
    (reflexive : ∀ value, relation value value) (values : Array α) (index : Nat) (value : α)
    (growth : relation (values[index]?.getD default) value) :
    ArrayExtends default relation values (values.set! index value) := by
  constructor
  · simp
  · intro cell
    simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    split
    · rename_i same
      subst cell
      split
      · exact growth
      · rename_i outside
        have absent : values[index]? = none := Array.getElem?_eq_none_iff.mpr (by omega)
        rw [absent]
        exact reflexive _
    · exact reflexive _

theorem addFlow_extends (values : Array Roots) (index : Nat) (roots : Roots) :
    ArrayExtends .unknown Roots.Extends values (addFlow values index roots) :=
  ArrayExtends.set Roots.Extends.refl values index _ (Roots.extends_join _ _)

structure State.Extends (before after : State) : Prop where
  values : ArrayExtends .unknown Roots.Extends before.values after.values
  slots : ArrayExtends .unknown Roots.Extends before.slots after.slots
  contents : ArrayExtends .unknown Roots.Extends before.contents after.contents
  writes : ArrayExtends (.assigned .unknown) Write.Extends before.writes after.writes
  touched : before.touched.Extends after.touched
  returned : before.returned.Extends after.returned

theorem State.Extends.refl (state : State) : state.Extends state :=
  ⟨ArrayExtends.refl _ _ Roots.Extends.refl _, ArrayExtends.refl _ _ Roots.Extends.refl _,
    ArrayExtends.refl _ _ Roots.Extends.refl _, ArrayExtends.refl _ _ Write.Extends.refl _,
    Roots.Extends.refl _, Roots.Extends.refl _⟩

theorem State.Extends.trans {before middle after : State}
    (first : before.Extends middle) (second : middle.Extends after) : before.Extends after :=
  ⟨ArrayExtends.trans (relation := Roots.Extends) (fun {_ _ _} left right => Roots.Extends.trans left right) first.values second.values,
    ArrayExtends.trans (relation := Roots.Extends) (fun {_ _ _} left right => Roots.Extends.trans left right) first.slots second.slots,
    ArrayExtends.trans (relation := Roots.Extends) (fun {_ _ _} left right => Roots.Extends.trans left right) first.contents second.contents,
    ArrayExtends.trans (relation := Write.Extends) (fun {_ _ _} left right => Write.Extends.trans left right) first.writes second.writes,
    first.touched.trans second.touched, first.returned.trans second.returned⟩

theorem State.Extends.antisymm {before after : State}
    (first : before.Extends after) (second : after.Extends before) : before = after := by
  cases before
  cases after
  cases ArrayExtends.antisymm Roots.Extends.antisymm first.values second.values
  cases ArrayExtends.antisymm Roots.Extends.antisymm first.slots second.slots
  cases ArrayExtends.antisymm Roots.Extends.antisymm first.contents second.contents
  cases ArrayExtends.antisymm Write.Extends.antisymm first.writes second.writes
  cases Roots.Extends.antisymm first.touched second.touched
  cases Roots.Extends.antisymm first.returned second.returned
  rfl

theorem State.extends_values (state : State) (value : ValueId) (roots : Roots) :
    state.Extends { state with values := addFlow state.values value roots } :=
  { State.Extends.refl state with values := addFlow_extends _ _ _ }

theorem State.extends_slots (state : State) (slot : SlotId) (roots : Roots) :
    state.Extends { state with slots := addFlow state.slots slot roots } :=
  { State.Extends.refl state with slots := addFlow_extends _ _ _ }

theorem State.extends_contents (state : State) (index : Nat) (roots : Roots) :
    state.Extends { state with
      contents := addFlow state.contents index roots
      writes := state.writes.set! index
        ((state.writes[index]?.getD (.assigned .unknown)).join (.assigned roots)) } :=
  { State.Extends.refl state with
    contents := addFlow_extends _ _ _
    writes := ArrayExtends.set Write.Extends.refl _ _ _ (Write.extends_join _ _) }

theorem State.extends_touched (state : State) (roots : Roots) :
    state.Extends { state with touched := state.touched.join roots } :=
  { State.Extends.refl state with touched := Roots.extends_join _ _ }

theorem State.extends_touched_unknown (state : State) :
    state.Extends { state with touched := .unknown } :=
  { State.Extends.refl state with touched := by cases state.touched <;> trivial }

theorem State.extends_returned (state : State) (roots : Roots) :
    state.Extends { state with returned := state.returned.join roots } :=
  { State.Extends.refl state with returned := Roots.extends_join _ _ }

theorem ArrayExtends.map_top {α : Type} {default top : α} {relation : α → α → Prop}
    (highest : ∀ value, relation value top) (reflexive : ∀ value, relation value value)
    (values : Array α) : ArrayExtends default relation values (values.map fun _ => top) := by
  constructor
  · simp
  · intro index
    by_cases bound : index < values.size
    · simp only [Array.getElem?_map, Array.getElem?_eq_getElem bound, Option.map_some, Option.getD_some]
      exact highest _
    · have absent : values[index]? = none := Array.getElem?_eq_none_iff.mpr (by omega)
      simp only [Array.getElem?_map, absent, Option.map_none, Option.getD_none]
      exact reflexive _

theorem State.extends_memory_unknown (state : State) :
    state.Extends { state with
      slots := state.slots.map (fun _ => .unknown)
      contents := state.contents.map (fun _ => .unknown)
      writes := state.writes.map (fun _ => .assigned .unknown) } :=
  { State.Extends.refl state with
    slots := ArrayExtends.map_top (by intro value; cases value <;> trivial) Roots.Extends.refl _
    contents := ArrayExtends.map_top (by intro value; cases value <;> trivial) Roots.Extends.refl _
    writes := ArrayExtends.map_top (by intro value; cases value with
      | unchanged => trivial
      | assigned roots => cases roots <;> trivial) Write.Extends.refl _ }

theorem state_foldl_extends {α : Type} (values : List α) (update : State → α → State)
    (growth : ∀ (state : State) (value : α), state.Extends (update state value)) (state : State) :
    state.Extends (values.foldl update state) := by
  apply List.foldlRecOn (motive := fun next => state.Extends next) values update (State.Extends.refl state)
  intro current known value _
  exact known.trans (growth current value)

theorem write_extends (f : Func) (state : State) (address roots : Roots) :
    state.Extends (write f state address roots) := by
  cases address with
  | pending => exact State.Extends.refl state
  | unknown => exact State.extends_memory_unknown state
  | known addresses =>
    apply state_foldl_extends
    intro current address
    cases address with
    | «local» slot => exact State.extends_slots _ _ _
    | global index => exact State.extends_touched_unknown _
    | contents index => exact State.extends_touched_unknown _
    | param index =>
      dsimp only
      split
      · exact State.extends_contents _ _ _
      · exact State.Extends.refl _

theorem state_forIn_extends {α : Type} (values : List α)
    (update : α → State → Id (ForInStep State))
    (growth : ∀ value state, match (update value state).run with
      | .done after | .yield after => state.Extends after) (state : State) :
    state.Extends (forIn values state update).run := by
  induction values generalizing state with
  | nil => exact State.Extends.refl _
  | cons value values ih =>
    have known := growth value state
    cases equation : (update value state).run with
    | done after => simpa [List.forIn_cons, equation] using known
    | yield after =>
      have one : state.Extends after := by simpa [equation] using known
      simpa [List.forIn_cons, equation] using one.trans (ih after)

theorem callState_extends (m : Module) (states : Array State) (f : Func)
    (state : State) (fn : FnId) (args : List ValueId) :
    state.Extends (callState m states f state fn args).2 := by
  simp only [callState]
  split
  · split
    · rename_i callee _ effects _
      simp only [Id.run_bind]
      simp only [Id.run_pure]
      apply (State.extends_touched _ _).trans
      apply state_forIn_extends
      intro parameter current
      by_cases isSlice : parameter.1.isRefSlice = true
      · simp only [isSlice, ↓reduceIte]
        cases effects.writes[parameter.2]?.getD (.assigned .unknown) with
        | unchanged => exact State.Extends.refl _
        | assigned roots => exact write_extends _ _ _ _
      · simpa [isSlice] using State.Extends.refl current
    · exact State.extends_touched_unknown _
  · exact State.extends_touched_unknown _

theorem touchValues_extends (vt : Array (Option VTy)) (state : State) (values : List ValueId) :
    state.Extends (touchValues vt state values) := by
  apply State.Extends.mk
  · exact ArrayExtends.refl _ _ Roots.Extends.refl _
  · exact ArrayExtends.refl _ _ Roots.Extends.refl _
  · exact ArrayExtends.refl _ _ Roots.Extends.refl _
  · exact ArrayExtends.refl _ _ Write.Extends.refl _
  · apply List.foldlRecOn (motive := fun next => state.touched.Extends next) values _ (Roots.Extends.refl _)
    intro current known value _
    split
    · exact known.trans (Roots.extends_join _ _)
    · exact known
  · exact Roots.Extends.refl _

theorem edge_extends (f : Func) (state : State) (target : BlockId) (args : List ValueId) :
    state.Extends (edge f state target args) := by
  unfold edge
  split
  · exact State.extends_touched_unknown _
  · apply state_foldl_extends
    intro current pair
    exact State.extends_values _ _ _

theorem step_extends (m : Module) (states : Array State) (f : Func)
    (vt : Array (Option VTy)) (state : State) (inst : Inst) :
    state.Extends (step m states f vt state inst) := by
  unfold step
  apply (touchValues_extends vt state (accessOperands inst)).trans
  generalize touchValues vt state (accessOperands inst) = current
  split
  · exact ((callState_extends _ _ _ _ _ _).trans (State.extends_values _ _ _)).trans
      (touchValues_extends _ _ _)
  · exact (State.extends_values _ _ _).trans (touchValues_extends _ _ _)
  · exact State.extends_slots _ _ _
  · split
    · exact write_extends _ _ _ _
    · exact State.Extends.refl _
  · exact edge_extends _ _ _ _
  · exact (edge_extends _ _ _ _).trans (edge_extends _ _ _ _)
  · exact State.extends_returned _ _
  · exact State.Extends.refl _

theorem state_array_foldl_extends {α : Type} (values : Array α) (update : State → α → State)
    (growth : ∀ (state : State) (value : α), state.Extends (update state value)) (state : State) :
    state.Extends (values.foldl update state) := by
  rw [← Array.foldl_toList]
  exact state_foldl_extends _ _ growth _

theorem round_extends (m : Module) (states : Array State) (f : Func)
    (vt : Array (Option VTy)) (state : State) :
    state.Extends (round m states f vt state) := by
  apply state_array_foldl_extends
  intro current block
  exact state_foldl_extends _ _ (step_extends m states f vt) current

theorem state_foldl_fixed_each {α : Type} (values : List α) (update : State → α → State)
    (growth : ∀ (state : State) (value : α), state.Extends (update state value))
    (state : State) (stable : values.foldl update state = state) :
    ∀ value ∈ values, update state value = state := by
  induction values with
  | nil => simp
  | cons first rest ih =>
    have one : update state first = state := by
      apply State.Extends.antisymm
      · have tail := state_foldl_extends rest update growth (update state first)
        change update state first |>.Extends state
        rw [show rest.foldl update (update state first) = state from stable] at tail
        exact tail
      · exact growth state first
    intro value member
    rcases List.mem_cons.mp member with equal | later
    · simpa only [equal] using one
    · exact ih (by simpa only [List.foldl_cons, one] using stable) value later

theorem state_array_foldl_fixed_each {α : Type} (values : Array α) (update : State → α → State)
    (growth : ∀ (state : State) (value : α), state.Extends (update state value))
    (state : State) (stable : values.foldl update state = state) :
    ∀ value ∈ values.toList, update state value = state := by
  apply state_foldl_fixed_each values.toList update growth state
  simpa only [Array.foldl_toList] using stable

theorem round_fixed_step (m : Module) (states : Array State) (f : Func)
    (vt : Array (Option VTy)) (state : State) (stable : round m states f vt state = state)
    (block : Block) (blockMember : block ∈ f.blocks.toList)
    (inst : Inst) (instMember : inst ∈ block.insts) :
    step m states f vt state inst = state := by
  have blockFixed : block.insts.foldl (step m states f vt) state = state :=
    state_array_foldl_fixed_each f.blocks _
      (fun current block => state_foldl_extends block.insts _ (step_extends m states f vt) current)
      state stable block blockMember
  exact state_foldl_fixed_each block.insts _ (step_extends m states f vt)
    state blockFixed inst instMember

#print axioms Roots.Extends.antisymm
#print axioms State.Extends.antisymm
#print axioms write_extends
#print axioms callState_extends
#print axioms step_extends
#print axioms round_extends
#print axioms round_fixed_step

end Goose.GIR.ReplacementContentFlow.Model
