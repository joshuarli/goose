import Goose.GIR.Validate
import Goose.GIR.Sound
import Goose.Core.Sound.Invert

namespace Goose.GIR

open Goose.Core

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

theorem refTy_metadata {env : TyEnv} {id : ValueId} {permission : Mutability} {target : Ty}
    (typed : env.refTy id = .ok (permission, target)) :
    env.vals[id]? = some (some (.data (.ref permission target))) := by
  unfold TyEnv.refTy at typed
  obtain ⟨ty, operand, typed⟩ := bind_ok typed
  cases ty <;> simp [tyErr] at typed
  case ref m t =>
    obtain ⟨rfl, rfl⟩ := typed
    exact dataTy_of operand

theorem viewTy_metadata {env : TyEnv} {id : ValueId} {permission : Mutability} {element : Ty}
    (typed : env.viewTy id = .ok (permission, element)) :
    env.vals[id]? = some (some (.view permission element)) := by
  unfold TyEnv.viewTy at typed
  obtain ⟨ty, operand, typed⟩ := bind_ok typed
  cases ty with
  | data _ => simp [tyErr] at typed
  | view m t =>
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at typed
    obtain ⟨rfl, rfl⟩ := typed
    exact valTy_of operand

theorem bin_metadata {env : TyEnv} {operator : BinOp} {ty : IntTy} {left right : ValueId}
    {origin : Option OriginId} {result : VTy}
    (typed : (Op.bin operator ty left right origin).resultTy env = .ok result) :
    env.vals[left]? = some (some (.data (.int ty))) ∧
    env.vals[right]? = some (some (.data (.int ty))) ∧ result = .data (.int ty) := by
  simp only [Op.resultTy] at typed
  obtain ⟨a, ha, typed⟩ := bind_ok typed
  obtain ⟨b, hb, typed⟩ := bind_ok typed
  have checked : (decide (a = ty) && decide (b = ty)) = true := by
    by_cases checked : (decide (a = ty) && decide (b = ty)) = true
    · exact checked
    · simp [checked, tyErr, bind, Except.bind] at typed
  simp only [Bool.and_eq_true, decide_eq_true_eq] at checked
  obtain ⟨rfl, rfl⟩ := checked
  simp only [decide_true, Bool.true_and, ite_true] at typed
  exact ⟨intTy_of ha, intTy_of hb, (Except.ok.inj typed).symm⟩

theorem cmp_metadata {env : TyEnv} {operator : CmpOp} {ty : IntTy} {left right : ValueId}
    {result : VTy} (typed : (Op.cmp operator ty left right).resultTy env = .ok result) :
    env.vals[left]? = some (some (.data (.int ty))) ∧
    env.vals[right]? = some (some (.data (.int ty))) ∧ result = .data .bool := by
  simp only [Op.resultTy] at typed
  obtain ⟨a, ha, typed⟩ := bind_ok typed
  obtain ⟨b, hb, typed⟩ := bind_ok typed
  have checked : (decide (a = ty) && decide (b = ty)) = true := by
    by_cases checked : (decide (a = ty) && decide (b = ty)) = true
    · exact checked
    · simp [checked, tyErr, bind, Except.bind] at typed
  simp only [Bool.and_eq_true, decide_eq_true_eq] at checked
  obtain ⟨rfl, rfl⟩ := checked
  simp only [decide_true, Bool.true_and, ite_true] at typed
  exact ⟨intTy_of ha, intTy_of hb, (Except.ok.inj typed).symm⟩

theorem un_metadata {env : TyEnv} {operator : UnOp} {ty : IntTy} {operand : ValueId}
    {origin : Option OriginId} {result : VTy}
    (typed : (Op.un operator ty operand origin).resultTy env = .ok result) :
    env.vals[operand]? = some (some (.data (.int ty))) ∧ result = .data (.int ty) := by
  simp only [Op.resultTy] at typed
  obtain ⟨a, ha, typed⟩ := bind_ok typed
  have checked : a = ty := by
    by_cases checked : a = ty
    · exact checked
    · simp [checked, tyErr, bind, Except.bind] at typed
  subst a
  simp only [ite_true] at typed
  refine ⟨intTy_of ha, ?_⟩
  cases operator <;> simp only [Bool.true_and, Bool.false_and, Bool.false_eq_true, ite_false] at typed
  · by_cases signed : ty.signed = false
    · simp [signed, tyErr, bind, Except.bind] at typed
    · simp [signed] at typed
      exact (Except.ok.inj typed).symm
  · exact (Except.ok.inj typed).symm

theorem next_metadata {env : TyEnv} {ty : IntTy} {operand : ValueId} {result : VTy}
    (typed : (Op.next ty operand).resultTy env = .ok result) :
    env.vals[operand]? = some (some (.data (.int ty))) ∧ result = .data (.int ty) := by
  simp only [Op.resultTy] at typed
  obtain ⟨a, ha, typed⟩ := bind_ok typed
  have checked : a = ty := by
    by_cases checked : a = ty
    · exact checked
    · simp [checked, tyErr, bind, Except.bind] at typed
  subst a
  simp only [ite_true] at typed
  exact ⟨intTy_of ha, (Except.ok.inj typed).symm⟩

theorem conv_metadata {env : TyEnv} {kind : ConvKind} {source target : IntTy}
    {operand : ValueId} {origin : Option OriginId} {result : VTy}
    (typed : (Op.conv kind source target operand origin).resultTy env = .ok result) :
    env.vals[operand]? = some (some (.data (.int source))) ∧ result = .data (.int target) := by
  simp only [Op.resultTy] at typed
  obtain ⟨a, ha, typed⟩ := bind_ok typed
  have checked : a = source := by
    by_cases checked : a = source
    · exact checked
    · simp [checked, tyErr, bind, Except.bind] at typed
  subst a
  simp only [ite_true] at typed
  refine ⟨intTy_of ha, ?_⟩
  cases kind <;> simp only [Bool.false_eq_true, ite_true, ite_false] at typed
  · by_cases range : target.minVal ≤ source.minVal ∧ source.maxVal ≤ target.maxVal
    · simpa [range, pure, Except.pure] using typed.symm
    · simp [range, tyErr, bind, Except.bind] at typed
  · exact (Except.ok.inj typed).symm
  · exact (Except.ok.inj typed).symm

theorem boolNot_metadata {env : TyEnv} {operand : ValueId} {result : VTy}
    (typed : (Op.boolNot operand).resultTy env = .ok result) :
    env.vals[operand]? = some (some (.data .bool)) ∧ result = .data .bool := by
  simp only [Op.resultTy] at typed
  obtain ⟨a, ha, typed⟩ := bind_ok typed
  have checked : a = Ty.bool := by
    by_cases checked : a = Ty.bool
    · exact checked
    · simp [checked, tyErr, bind, Except.bind] at typed
  subst a
  simp only [ite_true] at typed
  exact ⟨dataTy_of ha, (Except.ok.inj typed).symm⟩

theorem boolCmp_metadata {env : TyEnv} {operator : CmpOp} {left right : ValueId} {result : VTy}
    (typed : (Op.boolCmp operator left right).resultTy env = .ok result) :
    env.vals[left]? = some (some (.data .bool)) ∧
    env.vals[right]? = some (some (.data .bool)) ∧ result = .data .bool := by
  simp only [Op.resultTy] at typed
  obtain ⟨a, ha, typed⟩ := bind_ok typed
  obtain ⟨b, hb, typed⟩ := bind_ok typed
  have checked : (decide (a = Ty.bool) && decide (b = Ty.bool)) = true := by
    by_cases checked : (decide (a = Ty.bool) && decide (b = Ty.bool)) = true
    · exact checked
    · simp [checked, tyErr, bind, Except.bind] at typed
  simp only [Bool.and_eq_true, decide_eq_true_eq] at checked
  obtain ⟨rfl, rfl⟩ := checked
  simp only [decide_true, Bool.true_and, ite_true] at typed
  cases operator <;> simp [tyErr, bind, Except.bind] at typed
  all_goals exact ⟨dataTy_of ha, dataTy_of hb, (Except.ok.inj typed).symm⟩

theorem constInt_metadata {env : TyEnv} {ty : IntTy} {value : Int} {result : VTy}
    (typed : (Op.constInt ty value).resultTy env = .ok result) :
    ty.inRange value = true ∧ result = .data (.int ty) := by
  simp only [Op.resultTy] at typed
  split at typed
  · exact ⟨‹_›, (Except.ok.inj typed).symm⟩
  · simp [tyErr] at typed

theorem constBool_metadata {env : TyEnv} {value : Bool} {result : VTy}
    (typed : (Op.constBool value).resultTy env = .ok result) : result = .data .bool :=
  (Except.ok.inj typed).symm

theorem constUnit_metadata {env : TyEnv} {result : VTy}
    (typed : Op.constUnit.resultTy env = .ok result) : result = .data .unit :=
  (Except.ok.inj typed).symm

theorem refFreeze_metadata {env : TyEnv} {reference : ValueId} {result : VTy}
    (typed : (Op.refFreeze reference).resultTy env = .ok result) :
    ∃ permission target, env.vals[reference]? = some (some (.data (.ref permission target))) ∧
      result = .data (.ref .readOnly target) := by
  simp only [Op.resultTy] at typed
  obtain ⟨⟨permission, target⟩, operand, typed⟩ := bind_ok typed
  exact ⟨permission, target, refTy_metadata operand, (Except.ok.inj typed).symm⟩

theorem load_metadata {env : TyEnv} {reference : ValueId} {result : VTy}
    (typed : (Op.load reference).resultTy env = .ok result) :
    ∃ permission target, env.vals[reference]? = some (some (.data (.ref permission target))) ∧
      result = .data target := by
  simp only [Op.resultTy] at typed
  obtain ⟨⟨permission, target⟩, operand, typed⟩ := bind_ok typed
  exact ⟨permission, target, refTy_metadata operand, (Except.ok.inj typed).symm⟩

theorem viewLen_metadata {env : TyEnv} {view : ValueId} {result : VTy}
    (typed : (Op.viewLen view).resultTy env = .ok result) :
    ∃ permission element, env.vals[view]? = some (some (.view permission element)) ∧
      result = .data (.int .i64) := by
  simp only [Op.resultTy] at typed
  obtain ⟨⟨permission, element⟩, operand, typed⟩ := bind_ok typed
  exact ⟨permission, element, viewTy_metadata operand, (Except.ok.inj typed).symm⟩

private theorem view_index_metadata {env : TyEnv} {view index : ValueId} {result : VTy}
    (typed : (do let (permission, element) ← env.viewTy view
                 let _ ← env.intTy index
                 pure (VTy.data (.ref permission element))) = .ok result) :
    ∃ permission element indexTy,
      env.vals[view]? = some (some (.view permission element)) ∧
      env.vals[index]? = some (some (.data (.int indexTy))) ∧
      result = .data (.ref permission element) := by
  obtain ⟨⟨permission, element⟩, operand, typed⟩ := bind_ok typed
  obtain ⟨indexTy, integer, typed⟩ := bind_ok typed
  exact ⟨permission, element, indexTy, viewTy_metadata operand, intTy_of integer,
    (Except.ok.inj typed).symm⟩

theorem refElem_metadata {env : TyEnv} {view index : ValueId} {result : VTy}
    (typed : (Op.refElem view index).resultTy env = .ok result) :
    ∃ permission element indexTy,
      env.vals[view]? = some (some (.view permission element)) ∧
      env.vals[index]? = some (some (.data (.int indexTy))) ∧
      result = .data (.ref permission element) := view_index_metadata typed

theorem indexChecked_metadata {env : TyEnv} {view index : ValueId} {origin : OriginId}
    {result : VTy} (typed : (Op.indexChecked view index origin).resultTy env = .ok result) :
    ∃ permission element indexTy,
      env.vals[view]? = some (some (.view permission element)) ∧
      env.vals[index]? = some (some (.data (.int indexTy))) ∧
      result = .data (.ref permission element) := view_index_metadata typed

theorem indexProven_metadata {env : TyEnv} {view index : ValueId} {result : VTy}
    (typed : (Op.indexProven view index).resultTy env = .ok result) :
    ∃ permission element indexTy,
      env.vals[view]? = some (some (.view permission element)) ∧
      env.vals[index]? = some (some (.data (.int indexTy))) ∧
      result = .data (.ref permission element) := view_index_metadata typed


theorem slotAddr_metadata {env : TyEnv} {id : SlotId} {result : VTy}
    (typed : (Op.slotAddr id).resultTy env = .ok result) :
    ∃ slot permission, env.slots[id]? = some slot ∧ result = .data (.ref permission slot.ty) := by
  simp only [Op.resultTy] at typed
  cases lookup : env.slots[id]? with
  | none => simp [lookup, tyErr] at typed
  | some slot =>
    simp only [lookup] at typed
    exact ⟨slot, _, rfl, (Except.ok.inj typed).symm⟩

theorem globalAddr_metadata {env : TyEnv} {id : GlobalId} {result : VTy}
    (typed : (Op.globalAddr id).resultTy env = .ok result) :
    ∃ target kind permission, env.globals[id]? = some (target, kind) ∧
      result = .data (.ref permission target) := by
  simp only [Op.resultTy] at typed
  cases lookup : env.globals[id]? with
  | none => simp [lookup, tyErr] at typed
  | some pair =>
    rcases pair with ⟨target, kind⟩
    simp only [lookup] at typed
    exact ⟨target, kind, _, rfl, (Except.ok.inj typed).symm⟩

theorem snapshot_metadata {env : TyEnv} {reference : ValueId} {mode : SnapshotMode} {result : VTy}
    (typed : (Op.snapshot mode reference).resultTy env = .ok result) :
    ∃ permission owner element resultPermission,
      env.vals[reference]? = some (some (.data (.ref permission owner))) ∧
      arrayElem? owner = some element ∧ result = .view resultPermission element := by
  simp only [Op.resultTy] at typed
  obtain ⟨⟨permission, owner⟩, operand, typed⟩ := bind_ok typed
  cases arrayType : arrayElem? owner with
  | none => simp [arrayType, tyErr] at typed
  | some element =>
    simp only [arrayType] at typed
    exact ⟨permission, owner, element, _, refTy_metadata operand, arrayType,
      (Except.ok.inj typed).symm⟩

theorem sliceView_metadata {env : TyEnv} {sliceId : ValueId} {result : VTy}
    (typed : (Op.sliceView sliceId).resultTy env = .ok result) :
    ∃ permission element, env.vals[sliceId]? = some (some (.data (.slice permission element))) ∧
      result = .view permission element := by
  simp only [Op.resultTy] at typed
  obtain ⟨source, operand, typed⟩ := bind_ok typed
  cases source <;> simp [tyErr] at typed
  case slice permission element =>
    exact ⟨permission, element, dataTy_of operand, (Except.ok.inj typed).symm⟩

theorem boundTy_metadata {env : TyEnv} {bound : Bnd}
    (typed : env.boundTy bound = .ok ()) :
    ∀ id, (bound = .val id ∨ bound = .fromEnd id) →
      ∃ ty, env.vals[id]? = some (some (.data (.int ty))) := by
  intro id mentioned
  cases bound with
  | omitted => simp at mentioned
  | val value | fromEnd value =>
    have same : value = id := by simpa using mentioned
    subst value
    simp only [TyEnv.boundTy] at typed
    obtain ⟨ty, operand, _⟩ := bind_ok typed
    exact ⟨ty, intTy_of operand⟩

theorem viewSlice_metadata {env : TyEnv} {permission : Mutability} {view : ValueId}
    {lo hi : Bnd} {origin : OriginId} {result : VTy}
    (typed : (Op.viewSlice permission view lo hi origin).resultTy env = .ok result) :
    ∃ sourcePermission element,
      env.vals[view]? = some (some (.view sourcePermission element)) ∧
      env.boundTy lo = .ok () ∧ env.boundTy hi = .ok () ∧
      result = .data (.slice permission element) := by
  simp only [Op.resultTy] at typed
  obtain ⟨⟨sourcePermission, element⟩, operand, typed⟩ := bind_ok typed
  have allowed : sourcePermission.atLeast permission = true := by
    by_cases allowed : sourcePermission.atLeast permission = true
    · exact allowed
    · simp [allowed, tyErr, bind, Except.bind] at typed
  simp only [allowed, ite_true] at typed
  obtain ⟨lowUnit, low, typed⟩ := bind_ok typed
  cases lowUnit
  obtain ⟨highUnit, high, typed⟩ := bind_ok typed
  cases highUnit
  exact ⟨sourcePermission, element, viewTy_metadata operand, low, high,
    (Except.ok.inj typed).symm⟩

theorem arrayLen_metadata {env : TyEnv} {reference : ValueId} {result : VTy}
    (typed : (Op.arrayLen reference).resultTy env = .ok result) :
    ∃ permission owner element,
      env.vals[reference]? = some (some (.data (.ref permission owner))) ∧
      arrayElem? owner = some element ∧ result = .data (.int .i64) := by
  simp only [Op.resultTy] at typed
  obtain ⟨⟨permission, owner⟩, operand, typed⟩ := bind_ok typed
  cases arrayType : arrayElem? owner with
  | none => simp [arrayType, tyErr] at typed
  | some element =>
    simp only [arrayType, Option.isSome_some, ite_true] at typed
    exact ⟨permission, owner, element, refTy_metadata operand, arrayType,
      (Except.ok.inj typed).symm⟩

theorem push_metadata {env : TyEnv} {reference value : ValueId} {origin : Option OriginId}
    {result : VTy} (typed : (Op.push reference value origin).resultTy env = .ok result) :
    ∃ permission owner element,
      env.vals[reference]? = some (some (.data (.ref permission owner))) ∧
      owner.ownerElem? = some element ∧ env.vals[value]? = some (some (.data element)) ∧
      result = .data (.ref .mutable element) := by
  simp only [Op.resultTy] at typed
  obtain ⟨⟨permission, owner⟩, operand, typed⟩ := bind_ok typed
  cases arrayType : owner.ownerElem? with
  | none => simp [arrayType, tyErr] at typed
  | some element =>
    simp only [arrayType] at typed
    obtain ⟨source, valueType, typed⟩ := bind_ok typed
    have same : source = element := by
      by_cases same : source = element
      · exact same
      · simp [same, tyErr, bind, Except.bind] at typed
    subst source
    simp only [ite_true] at typed
    exact ⟨permission, owner, element, refTy_metadata operand, arrayType, dataTy_of valueType,
      (Except.ok.inj typed).symm⟩

theorem pop_metadata {env : TyEnv} {reference : ValueId} {origin : OriginId} {result : VTy}
    (typed : (Op.pop reference origin).resultTy env = .ok result) :
    ∃ permission owner element,
      env.vals[reference]? = some (some (.data (.ref permission owner))) ∧
      owner.ownerElem? = some element ∧ result = .data element := by
  simp only [Op.resultTy] at typed
  obtain ⟨⟨permission, owner⟩, operand, typed⟩ := bind_ok typed
  cases arrayType : owner.ownerElem? with
  | none => simp [arrayType, tyErr] at typed
  | some element =>
    simp only [arrayType] at typed
    exact ⟨permission, owner, element, refTy_metadata operand, arrayType,
      (Except.ok.inj typed).symm⟩

theorem arrFill_metadata {env : TyEnv} {ty : Ty} {value : ValueId} {result : VTy}
    (typed : (Op.arrFill ty value).resultTy env = .ok result) :
    ∃ element count, ty = .arr element count ∧
      env.vals[value]? = some (some (.data element)) ∧ result = .data ty := by
  cases ty <;> simp only [Op.resultTy] at typed
  case arr element count =>
    obtain ⟨source, operand, typed⟩ := bind_ok typed
    have same : source = element := by
      by_cases same : source = element
      · exact same
      · simp [same, tyErr, bind, Except.bind] at typed
    subst source
    simp only [ite_true] at typed
    exact ⟨element, count, rfl, dataTy_of operand, (Except.ok.inj typed).symm⟩
  all_goals simp [tyErr] at typed


private theorem metadata_forIn_ok {α : Type} {values : List α}
    {body : α → PUnit.{1} → TyR (ForInStep PUnit.{1})}
    (typed : forIn values PUnit.unit body = .ok ())
    (continues : ∀ value accumulator step, body value accumulator = .ok step → step = .yield PUnit.unit) :
    ∀ value ∈ values, body value PUnit.unit = .ok (.yield PUnit.unit) := by
  induction values with
  | nil => simp
  | cons head tail ih =>
    rw [List.forIn_cons] at typed
    obtain ⟨step, first, rest⟩ := bind_ok typed
    have same := continues head PUnit.unit step first
    subst step
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact first
    · exact ih rest value member

private theorem array_literal_elements {env : TyEnv} {values : List ValueId} {element : Ty}
    (typed : (forIn values PUnit.unit fun value _ => do
      unless (← env.dataTy value) = element do tyErr "array element of another type than the array's"
      pure (.yield PUnit.unit)) = .ok ()) :
    ∀ value ∈ values, env.vals[value]? = some (some (.data element)) := by
  have each := metadata_forIn_ok typed (by
    intro value accumulator step checked
    obtain ⟨ty, _, checked⟩ := bind_ok checked
    by_cases same : ty = element
    · simpa [same, pure, Except.pure] using checked.symm
    · simp [same, tyErr, bind, Except.bind] at checked)
  intro value member
  obtain ⟨ty, operand, checked⟩ := bind_ok (each value member)
  have same : ty = element := by
    by_cases same : ty = element
    · exact same
    · simp [same, tyErr, bind, Except.bind] at checked
  subst ty
  exact dataTy_of operand

theorem arrLit_metadata {env : TyEnv} {ty : Ty} {values : List ValueId} {result : VTy}
    (typed : (Op.arrLit ty values).resultTy env = .ok result) :
    ∃ element, arrayElem? ty = some element ∧
      (∀ value ∈ values, env.vals[value]? = some (some (.data element))) ∧
      (∀ e count, ty = .arr e count → values.length = count) ∧
      (∀ e capacity, ty = .limited e capacity → values.length ≤ capacity) ∧
      result = .data ty := by
  cases ty <;> simp only [Op.resultTy] at typed
  case arr element count =>
    have countOk : values.length = count := by
      by_cases countOk : values.length = count
      · exact countOk
      · simp [countOk, tyErr, bind, Except.bind] at typed
    simp only [countOk, ite_true] at typed
    obtain ⟨accumulator, elements, typed⟩ := bind_ok typed
    cases accumulator
    exact ⟨element, rfl, array_literal_elements elements,
      (by intro e n equal; cases equal; exact countOk),
      (by intro e n equal; cases equal), (Except.ok.inj typed).symm⟩
  case grow element | growshrink element =>
    obtain ⟨accumulator, elements, typed⟩ := bind_ok typed
    cases accumulator
    exact ⟨element, rfl, array_literal_elements elements,
      (by intro e n equal; cases equal),
      (by intro e n equal; cases equal), (Except.ok.inj typed).symm⟩
  case limited element capacity =>
    have capacityOk : values.length ≤ capacity := by
      by_cases capacityOk : values.length ≤ capacity
      · exact capacityOk
      · simp [capacityOk, tyErr, bind, Except.bind] at typed
    simp only [capacityOk, ite_true] at typed
    obtain ⟨accumulator, elements, typed⟩ := bind_ok typed
    cases accumulator
    exact ⟨element, rfl, array_literal_elements elements,
      (by intro e n equal; cases equal),
      (by intro e n equal; cases equal; exact capacityOk), (Except.ok.inj typed).symm⟩
  all_goals simp [tyErr] at typed

theorem fieldAddr_metadata {env : TyEnv} {owner : ValueId} {index : Nat} {result : VTy}
    (typed : (Op.fieldAddr owner index).resultTy env = .ok result) :
    ∃ permission sid fields descriptor field,
      env.vals[owner]? = some (some (.data (.ref permission (.structT sid fields)))) ∧
      env.structs[sid]? = some descriptor ∧ descriptor.fields[index]? = some field ∧
      fields.toList[index]? = some field.ty ∧
      result = .data (.ref (Mutability.ofKind field.binding) field.ty) := by
  simp only [Op.resultTy] at typed
  obtain ⟨⟨permission, target⟩, operand, typed⟩ := bind_ok typed
  cases target with
  | structT sid fields =>
    cases lookup : env.structs[sid]? with
    | none => simp [lookup, tyErr] at typed
    | some descriptor =>
      simp only [lookup] at typed
      have same : fields = TyList.ofList (descriptor.fields.toList.map (·.ty)) := by
        by_cases same : fields = TyList.ofList (descriptor.fields.toList.map (·.ty))
        · exact same
        · simp [same, tyErr, bind, Except.bind] at typed
      simp only [same, beq_self_eq_true, ite_true] at typed
      cases selector : descriptor.fields[index]? with
      | none => simp [selector, tyErr] at typed
      | some field =>
        simp only [selector] at typed
        refine ⟨permission, sid, fields, descriptor, field, refTy_metadata operand,
          lookup, selector, ?_, (Except.ok.inj typed).symm⟩
        simp only [same, Goose.Core.Sound.tyList_toList_ofList, List.getElem?_map, Array.getElem?_toList,
          selector, Option.map_some]
  | _ => simp [tyErr] at typed

end Goose.GIR
