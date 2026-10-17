import Goose.Lower.Validation.SourceTouchSummaryBounds
import Goose.GIR.ReplacementContentFlowProofsCanonicalDefinitionTyping
import Goose.GIR.ReplacementContentFlowProofsTouchFootprint
import Goose.GIR.Sound

namespace Goose.Lower.Validation.SourceTouchOperandsTyping

open Goose.Core Goose.GIR Goose.GIR.ReplacementContentFlow.Model
open Goose.Lower.Validation.SummaryPreservation

private theorem checked_definition_result {module : GIR.Module} {func : Func}
    {types : Array (Option VTy)} {value : ValueId} {op : Op} {type : VTy}
    (checked : checkInstTypes func {module.tyEnv func with vals := types} types (.def value op) = .ok ())
    (produced : op.resultTy {module.tyEnv func with vals := types} = .ok type) :
    types[value]? = some (some type) := by
  by_cases row : types[value]? = some (some type)
  · exact row
  · simp [checkInstTypes, produced, row, bind, Except.bind] at checked

private theorem wholeOwnerReference_data_flat {type : Ty} (flat : type.flat = true) :
    wholeOwnerReference (.data type) = false := by
  cases type <;> simp_all [wholeOwnerReference, Ty.flat]

private theorem wholeOwner_row_conflict {types : Array (Option VTy)} {source : ValueId}
    {type other : VTy}
    (row : types[source]? = some (some type))
    (otherRow : types[source]? = some (some other))
    (owner : wholeOwnerReference type = true)
    (notOwner : wholeOwnerReference other = false) : False := by
  have same : type = other := Option.some.inj (Option.some.inj (row.symm.trans otherRow))
  rw [same, notOwner] at owner
  contradiction

private theorem ownerElement_flat_of_reference_shape {types : Array (Option VTy)}
    {env : TyEnv} {owner : ValueId} {mutability : Mutability} {payload element : Ty}
    (shapes : ValueTypeShapes types) (values : env.vals = types)
    (reference : env.refTy owner = .ok (mutability, payload))
    (elementOf : payload.ownerElem? = some element) : element.flat = true := by
  have envShapes : ValueTypeShapes env.vals := by simpa [values] using shapes
  have shape := ValueTypeShapes.reference envShapes reference
  rcases shape with storable | slice
  · exact storable_owner_element storable elementOf
  · cases payload <;> simp_all [Ty.isRefSlice, Ty.ownerElem?]

private theorem ownerElement_flat_of_data_shape {type element : Ty}
    (shape : DataTypeShape type) (elementOf : arrayElem? type = some element) :
    element.flat = true := by
  cases type <;> simp_all [DataTypeShape, arrayElem?, Ty.storable]

private theorem checked_effect {module : GIR.Module} {func : Func}
    {types : Array (Option VTy)} {effect : Effect}
    (checked : checkInstTypes func {module.tyEnv func with vals := types} types (.eff effect) = .ok ()) :
    checkEffectTypes {module.tyEnv func with vals := types} effect = .ok () := by
  simpa [checkInstTypes] using checked

private theorem fieldAddr_refStructTy {env : TyEnv} {source : ValueId} {field : Nat}
    {resultType : VTy}
    (typed : (Op.fieldAddr source field).resultTy env = .ok resultType) :
    ∃ mutability id fields, env.refTy source = .ok (mutability, .structT id fields) := by
  simp only [Op.resultTy] at typed
  cases sourceType : env.refTy source with
  | error message => simp [sourceType, bind, Except.bind] at typed
  | ok pair =>
      rcases pair with ⟨mutability, payload⟩
      cases payload with
      | structT id fields => exact ⟨mutability, id, fields, rfl⟩
      | _ => simp [sourceType, bind, Except.bind, tyErr] at typed

private theorem not_wholeOwner_of_dataTy_flat {types : Array (Option VTy)}
    {env : TyEnv} {source : ValueId} {type : Ty} {sourceType : VTy}
    (values : env.vals = types) (row : types[source]? = some (some sourceType))
    (owner : wholeOwnerReference sourceType = true)
    (typed : env.dataTy source = .ok type) (flat : type.flat = true) : False := by
  exact wholeOwner_row_conflict row (by simpa [values] using TyEnv.dataTy_known typed)
    owner (wholeOwnerReference_data_flat flat)

private theorem not_wholeOwner_of_dataTy {types : Array (Option VTy)}
    {env : TyEnv} {source : ValueId} {type : Ty} {sourceType : VTy}
    (values : env.vals = types) (row : types[source]? = some (some sourceType))
    (owner : wholeOwnerReference sourceType = true)
    (typed : env.dataTy source = .ok type)
    (notOwner : wholeOwnerReference (.data type) = false) : False := by
  exact wholeOwner_row_conflict row (by simpa [values] using TyEnv.dataTy_known typed) owner notOwner

private theorem not_wholeOwner_of_intTy {types : Array (Option VTy)}
    {env : TyEnv} {source : ValueId} {type : VTy} {width : IntTy}
    (values : env.vals = types) (row : types[source]? = some (some type))
    (owner : wholeOwnerReference type = true) (typed : env.intTy source = .ok width) : False := by
  exact wholeOwner_row_conflict row (by simpa [values] using intTy_of typed)
    owner (by simp [wholeOwnerReference])

private theorem not_wholeOwner_of_boolTy {types : Array (Option VTy)}
    {env : TyEnv} {source : ValueId} {type : VTy}
    (values : env.vals = types) (row : types[source]? = some (some type))
    (owner : wholeOwnerReference type = true) (typed : env.dataTy source = .ok .bool) : False := by
  exact wholeOwner_row_conflict row (by simpa [values] using TyEnv.dataTy_known typed)
    owner (by simp [wholeOwnerReference])

private theorem not_wholeOwner_of_viewTy {types : Array (Option VTy)}
    {env : TyEnv} {source : ValueId} {type : VTy} {mutability : Mutability} {element : Ty}
    (values : env.vals = types) (row : types[source]? = some (some type))
    (owner : wholeOwnerReference type = true) (typed : env.viewTy source = .ok (mutability, element)) : False := by
  exact wholeOwner_row_conflict row (by simpa [values] using TyEnv.viewTy_known typed)
    owner (by simp [wholeOwnerReference])

private theorem not_wholeOwner_of_sliceTy {types : Array (Option VTy)}
    {env : TyEnv} {source : ValueId} {type : VTy} {mutability : Mutability} {element : Ty}
    (values : env.vals = types) (row : types[source]? = some (some type))
    (owner : wholeOwnerReference type = true) (typed : env.dataTy source = .ok (.slice mutability element)) : False := by
  exact wholeOwner_row_conflict row (by simpa [values] using TyEnv.dataTy_known typed)
    owner (by simp [wholeOwnerReference])

private theorem boundValue_intTy {env : TyEnv} {source : ValueId}
    (typed : env.boundTy (.val source) = .ok ()) : ∃ width, env.intTy source = .ok width := by
  change (env.intTy source >>= fun _ => Except.ok ()) = .ok () at typed
  obtain ⟨width, inputTyped, _⟩ := GIR.bind_ok typed
  exact ⟨width, inputTyped⟩

private theorem boundFromEnd_intTy {env : TyEnv} {source : ValueId}
    (typed : env.boundTy (.fromEnd source) = .ok ()) : ∃ width, env.intTy source = .ok width := by
  change (env.intTy source >>= fun _ => Except.ok ()) = .ok () at typed
  obtain ⟨width, inputTyped, _⟩ := GIR.bind_ok typed
  exact ⟨width, inputTyped⟩

private theorem dataLoop_typed {env : TyEnv} {element : Ty} {values : List ValueId}
    (checked : forIn values PUnit.unit (fun value _ => do
      unless (← env.dataTy value) = element do tyErr "array element of another type than the array's"
      pure (ForInStep.yield PUnit.unit)) = .ok PUnit.unit) :
    ∀ value ∈ values, env.dataTy value = .ok element := by
  induction values with
  | nil => simp
  | cons first rest inductionHypothesis =>
      simp only [List.forIn_cons] at checked
      obtain ⟨step, firstCheck, restCheck⟩ := GIR.bind_ok checked
      cases dataResult : env.dataTy first with
      | error message => simp [dataResult, bind, Except.bind] at firstCheck
      | ok actual =>
          by_cases same : actual = element
          · have stepSame : step = .yield PUnit.unit := by
              simp [dataResult, same, bind, Except.bind, pure, Except.pure] at firstCheck
              exact firstCheck.symm
            have restTyped : forIn rest PUnit.unit (fun value _ => do
                unless (← env.dataTy value) = element do tyErr "array element of another type than the array's"
                pure (ForInStep.yield PUnit.unit)) = .ok PUnit.unit := by
              simpa [stepSame, pure, Except.pure] using restCheck
            intro value member
            rcases List.mem_cons.mp member with firstMember | restMember
            · subst value
              simpa [dataResult, same]
            · exact inductionHypothesis restTyped value restMember
          · simp [dataResult, same, tyErr, bind, Except.bind] at firstCheck

private theorem dataFieldLoop_typed {env : TyEnv} {values : List (ValueId × StructField)}
    (checked : forIn values PUnit.unit (fun (item : ValueId × StructField) _ => do
      unless (← env.dataTy item.1) == item.2.ty do tyErr "struct initializer has another field type"
      pure (ForInStep.yield PUnit.unit)) = .ok PUnit.unit) :
    ∀ pair ∈ values, env.dataTy pair.1 = .ok pair.2.ty := by
  induction values with
  | nil => simp
  | cons first rest inductionHypothesis =>
      simp only [List.forIn_cons] at checked
      obtain ⟨step, firstCheck, restCheck⟩ := GIR.bind_ok checked
      rcases first with ⟨value, field⟩
      cases dataResult : env.dataTy value with
      | error message => simp [dataResult, bind, Except.bind] at firstCheck
      | ok actual =>
          by_cases same : actual = field.ty
          · have stepSame : step = .yield PUnit.unit := by
              simp [dataResult, same, bind, Except.bind, pure, Except.pure] at firstCheck
              exact firstCheck.symm
            have restTyped : forIn rest PUnit.unit (fun (item : ValueId × StructField) _ => do
                unless (← env.dataTy item.1) == item.2.ty do tyErr "struct initializer has another field type"
                pure (ForInStep.yield PUnit.unit)) = .ok PUnit.unit := by
              simpa [stepSame, pure, Except.pure] using restCheck
            intro pair member
            rcases List.mem_cons.mp member with firstMember | restMember
            · cases firstMember
              simpa [dataResult, same]
            · exact inductionHypothesis restTyped pair restMember
          · simp [dataResult, same, tyErr, bind, Except.bind] at firstCheck

private theorem mem_zip_same_left {α β : Type} {left : List α} {right : List β}
    (lengths : left.length = right.length) {value : α} (member : value ∈ left) :
    ∃ field, field ∈ right ∧ (value, field) ∈ left.zip right := by
  induction left generalizing right with
  | nil => simp at member
  | cons first rest inductionHypothesis =>
      cases right with
      | nil => simp at lengths
      | cons field fields =>
          simp only [List.length_cons, Nat.succ.injEq] at lengths
          rcases List.mem_cons.mp member with same | restMember
          · subst value
            exact ⟨field, List.mem_cons_self, by simp⟩
          · obtain ⟨next, nextMember, zipped⟩ := inductionHypothesis lengths restMember
            exact ⟨next, List.mem_cons_of_mem _ nextMember, by simp [zipped]⟩

private theorem append_viewTy {env : TyEnv} {owner value : ValueId} {origin : Option OriginId}
    (checked : checkEffectTypes env (.append owner value origin) = .ok ()) :
    ∃ mutability element, env.viewTy value = .ok (mutability, element) := by
  cases reference : env.refTy owner with
  | error message => simp [checkEffectTypes, reference, bind, Except.bind, tyErr] at checked
  | ok pair =>
      cases pair with
      | mk mutability payload =>
          cases payload with
          | grow element | growshrink element | limited element capacity =>
              cases view : env.viewTy value with
              | error message => simp [checkEffectTypes, reference, view, bind, Except.bind, tyErr] at checked
              | ok pair => cases pair; exact ⟨_, _, rfl⟩
          | _ => simp [checkEffectTypes, reference, bind, Except.bind, tyErr] at checked

private theorem popN_count_intTy {env : TyEnv} {owner count : ValueId} {origin : Option OriginId}
    (checked : checkEffectTypes env (.popN owner count origin) = .ok ()) :
    ∃ width, env.intTy count = .ok width := by
  cases reference : env.refTy owner with
  | error message => simp [checkEffectTypes, reference, bind, Except.bind, tyErr] at checked
  | ok pair =>
      rcases pair with ⟨mutability, payload⟩
      cases ownerElement : payload.ownerElem? with
      | none => simp [checkEffectTypes, reference, ownerElement, bind, Except.bind, tyErr] at checked
      | some element =>
          cases countResult : env.intTy count with
          | error message => simp [checkEffectTypes, reference, ownerElement, countResult, bind, Except.bind, tyErr] at checked
          | ok width => exact ⟨width, rfl⟩

private theorem resize_size_intTy {env : TyEnv} {owner size : ValueId}
    {fill : Option ValueId} {origin : Option OriginId}
    (checked : checkEffectTypes env (.resize owner size fill origin) = .ok ()) :
    ∃ width, env.intTy size = .ok width := by
  cases reference : env.refTy owner with
  | error message => simp [checkEffectTypes, reference, bind, Except.bind, tyErr] at checked
  | ok pair =>
      rcases pair with ⟨mutability, payload⟩
      cases ownerElement : payload.ownerElem? with
      | none => simp [checkEffectTypes, reference, ownerElement, bind, Except.bind, tyErr] at checked
      | some element =>
          cases sizeResult : env.intTy size with
          | error message => simp [checkEffectTypes, reference, ownerElement, sizeResult, bind, Except.bind, tyErr] at checked
          | ok width => exact ⟨width, rfl⟩

private theorem resize_fill_dataTy {env : TyEnv} {owner size value : ValueId}
    {origin : Option OriginId} (shapes : ValueTypeShapes env.vals)
    (checked : checkEffectTypes env (.resize owner size (some value) origin) = .ok ()) :
    ∃ element, env.dataTy value = .ok element ∧ element.flat = true := by
  cases reference : env.refTy owner with
  | error message => simp [checkEffectTypes, reference, bind, Except.bind, tyErr] at checked
  | ok pair =>
      rcases pair with ⟨mutability, payload⟩
      cases ownerElement : payload.ownerElem? with
      | none => simp [checkEffectTypes, reference, ownerElement, bind, Except.bind, tyErr] at checked
      | some element =>
          cases sizeResult : env.intTy size with
          | error message => simp [checkEffectTypes, reference, ownerElement, sizeResult, bind, Except.bind, tyErr] at checked
          | ok width =>
              cases fillResult : env.dataTy value with
              | error message => simp [checkEffectTypes, reference, ownerElement, sizeResult, fillResult, bind, Except.bind, tyErr] at checked
              | ok actual =>
                  have same : actual = element := by
                    by_cases same : actual = element
                    · exact same
                    · simp [checkEffectTypes, reference, ownerElement, sizeResult, fillResult, same, bind, Except.bind, tyErr] at checked
                  have flat := ownerElement_flat_of_reference_shape shapes rfl reference ownerElement
                  exact ⟨element, by simpa [same] using fillResult, flat⟩

private theorem replace_run_typed {env : TyEnv} {owner run : ValueId} {origin : Option OriginId}
    (checked : checkEffectTypes env (.replace owner run origin) = .ok ()) :
    (∃ element, env.dataTy run = .ok (.grow element)) ∨
      (∃ element, env.dataTy run = .ok (.growshrink element)) := by
  cases reference : env.refTy owner with
  | error message => simp [checkEffectTypes, reference, bind, Except.bind, tyErr] at checked
  | ok pair =>
      rcases pair with ⟨mutability, payload⟩
      cases payload with
      | grow element =>
          cases runResult : env.dataTy run with
          | error message => simp [checkEffectTypes, reference, runResult, bind, Except.bind, tyErr] at checked
          | ok actual =>
              have same : actual = .grow element := by
                by_cases same : actual = .grow element
                · exact same
                · simp [checkEffectTypes, reference, runResult, same, bind, Except.bind, tyErr] at checked
              exact Or.inl ⟨element, by simpa [same] using runResult⟩
      | growshrink element =>
          cases runResult : env.dataTy run with
          | error message => simp [checkEffectTypes, reference, runResult, bind, Except.bind, tyErr] at checked
          | ok actual =>
              have same : actual = .growshrink element := by
                by_cases same : actual = .growshrink element
                · exact same
                · simp [checkEffectTypes, reference, runResult, same, bind, Except.bind, tyErr] at checked
              exact Or.inr ⟨element, by simpa [same] using runResult⟩
      | _ => simp [checkEffectTypes, reference, bind, Except.bind, tyErr] at checked

private def checkedPrintPart (env : TyEnv) : PrintPart → Except String (ForInStep PUnit)
  | .text _ => pure (ForInStep.yield PUnit.unit)
  | .val value => do
      match (← env.dataTy value) with
      | .int _ | .bool => pure (ForInStep.yield PUnit.unit)
      | _ => tyErr "a printed value is neither an integer nor a boolean"

private theorem printLoop_values_typed {env : TyEnv} {parts : List PrintPart}
    (checked : forIn parts PUnit.unit (fun part _ => checkedPrintPart env part) = .ok PUnit.unit) :
    ∀ value, value ∈ parts.flatMap PrintPart.uses →
      (∃ width, env.dataTy value = .ok (.int width)) ∨ env.dataTy value = .ok .bool := by
  induction parts with
  | nil => simp
  | cons first rest inductionHypothesis =>
      rw [List.forIn_cons] at checked
      obtain ⟨step, firstCheck, restCheck⟩ := GIR.bind_ok checked
      cases first with
      | text text =>
          have stepSame : step = .yield PUnit.unit := by
            have h : (Except.ok (.yield PUnit.unit) : Except String (ForInStep PUnit)) = .ok step := by
              simpa [checkedPrintPart, pure, Except.pure] using firstCheck
            exact (Except.ok.inj h).symm
          have restTyped : forIn rest PUnit.unit (fun part _ => checkedPrintPart env part) = .ok PUnit.unit := by
            simpa [stepSame] using restCheck
          intro value member
          rcases List.mem_flatMap.mp member with ⟨part, partMember, sourceMember⟩
          rcases List.mem_cons.mp partMember with same | tail
          · subst part
            simp [PrintPart.uses] at sourceMember
          · exact inductionHypothesis restTyped value
              (List.mem_flatMap.mpr ⟨part, tail, sourceMember⟩)
      | val printed =>
          cases result : env.dataTy printed with
          | error message => simp [checkedPrintPart, result, bind, Except.bind, tyErr] at firstCheck
          | ok dataType =>
              cases dataType with
              | int width =>
                  have stepSame : step = .yield PUnit.unit := by
                    have h : (Except.ok (.yield PUnit.unit) : Except String (ForInStep PUnit)) = .ok step := by
                      simpa [checkedPrintPart, result, bind, Except.bind, pure, Except.pure] using firstCheck
                    exact (Except.ok.inj h).symm
                  have restTyped : forIn rest PUnit.unit (fun part _ => checkedPrintPart env part) = .ok PUnit.unit := by
                    simpa [stepSame] using restCheck
                  intro value member
                  rcases List.mem_flatMap.mp member with ⟨part, partMember, sourceMember⟩
                  rcases List.mem_cons.mp partMember with same | tail
                  · subst part
                    simp [PrintPart.uses] at sourceMember
                    subst value
                    exact Or.inl ⟨width, result⟩
                  · exact inductionHypothesis restTyped value
                      (List.mem_flatMap.mpr ⟨part, tail, sourceMember⟩)
              | bool =>
                  have stepSame : step = .yield PUnit.unit := by
                    have h : (Except.ok (.yield PUnit.unit) : Except String (ForInStep PUnit)) = .ok step := by
                      simpa [checkedPrintPart, result, bind, Except.bind, pure, Except.pure] using firstCheck
                    exact (Except.ok.inj h).symm
                  have restTyped : forIn rest PUnit.unit (fun part _ => checkedPrintPart env part) = .ok PUnit.unit := by
                    simpa [stepSame] using restCheck
                  intro value member
                  rcases List.mem_flatMap.mp member with ⟨part, partMember, sourceMember⟩
                  rcases List.mem_cons.mp partMember with same | tail
                  · subst part
                    simp [PrintPart.uses] at sourceMember
                    subst value
                    exact Or.inr result
                  · exact inductionHypothesis restTyped value
                      (List.mem_flatMap.mpr ⟨part, tail, sourceMember⟩)
              | _ => simp [checkedPrintPart, result, bind, Except.bind, tyErr] at firstCheck

private theorem arrLit_fixed_inputs {env : TyEnv} {element : Ty} {count : Nat}
    {args : List ValueId} {resultType : VTy}
    (typed : (Op.arrLit (.arr element count) args).resultTy env = .ok resultType) :
    (∀ source ∈ args, env.dataTy source = .ok element) ∧
      resultType = .data (.arr element count) := by
  simp only [Op.resultTy] at typed
  by_cases length : args.length = count
  · simp [length] at typed
    obtain ⟨_, loopCheck, afterLoop⟩ := GIR.bind_ok typed
    have members := dataLoop_typed loopCheck
    exact ⟨members, Except.ok.inj afterLoop.symm⟩
  · simp [length, tyErr, bind, Except.bind] at typed

private theorem arrLit_grow_inputs {env : TyEnv} {element : Ty}
    {args : List ValueId} {resultType : VTy}
    (typed : (Op.arrLit (.grow element) args).resultTy env = .ok resultType) :
    (∀ source ∈ args, env.dataTy source = .ok element) ∧
      resultType = .data (.grow element) := by
  simp only [Op.resultTy] at typed
  obtain ⟨_, loopCheck, afterLoop⟩ := GIR.bind_ok typed
  have members := dataLoop_typed loopCheck
  exact ⟨members, Except.ok.inj afterLoop.symm⟩

private theorem arrLit_growshrink_inputs {env : TyEnv} {element : Ty}
    {args : List ValueId} {resultType : VTy}
    (typed : (Op.arrLit (.growshrink element) args).resultTy env = .ok resultType) :
    (∀ source ∈ args, env.dataTy source = .ok element) ∧
      resultType = .data (.growshrink element) := by
  simp only [Op.resultTy] at typed
  obtain ⟨_, loopCheck, afterLoop⟩ := GIR.bind_ok typed
  have members := dataLoop_typed loopCheck
  exact ⟨members, Except.ok.inj afterLoop.symm⟩

private theorem arrLit_limited_inputs {env : TyEnv} {element : Ty} {capacity : Nat}
    {args : List ValueId} {resultType : VTy}
    (typed : (Op.arrLit (.limited element capacity) args).resultTy env = .ok resultType) :
    (∀ source ∈ args, env.dataTy source = .ok element) ∧
      resultType = .data (.limited element capacity) := by
  simp only [Op.resultTy] at typed
  by_cases length : args.length ≤ capacity
  · simp [length] at typed
    obtain ⟨_, loopCheck, afterLoop⟩ := GIR.bind_ok typed
    have members := dataLoop_typed loopCheck
    exact ⟨members, Except.ok.inj afterLoop.symm⟩
  · simp [length, tyErr, bind, Except.bind] at typed

private theorem bin_result_int_inputs {env : TyEnv} {operator : BinOp} {width : IntTy}
    {left right : ValueId} {origin : Option OriginId} {resultType : VTy}
    (typed : (Op.bin operator width left right origin).resultTy env = .ok resultType) :
    env.intTy left = .ok width ∧ env.intTy right = .ok width := by
  cases leftResult : env.intTy left with
  | error message => simp [Op.resultTy, leftResult, bind, Except.bind] at typed
  | ok leftType =>
    cases rightResult : env.intTy right with
    | error message => simp [Op.resultTy, leftResult, rightResult, bind, Except.bind] at typed
    | ok rightType =>
      have same : leftType = width ∧ rightType = width := by
        by_cases same : leftType = width ∧ rightType = width
        · exact same
        · simp [Op.resultTy, leftResult, rightResult, same, bind, Except.bind, tyErr] at typed
      rcases same with ⟨leftEqual, rightEqual⟩
      exact ⟨by simpa [leftEqual] using leftResult, by simpa [rightEqual] using rightResult⟩

private theorem unary_result_int_input {env : TyEnv} {operator : UnOp} {width : IntTy}
    {source : ValueId} {origin : Option OriginId} {resultType : VTy}
    (typed : (Op.un operator width source origin).resultTy env = .ok resultType) :
    env.intTy source = .ok width := by
  cases result : env.intTy source with
  | error message => simp [Op.resultTy, result, bind, Except.bind] at typed
  | ok actual =>
    have same : actual = width := by
      by_cases same : actual = width
      · exact same
      · simp [Op.resultTy, result, same, bind, Except.bind, tyErr] at typed
    simpa [same] using result

private theorem cmp_result_int_inputs {env : TyEnv} {operator : CmpOp} {width : IntTy}
    {left right : ValueId} {resultType : VTy}
    (typed : (Op.cmp operator width left right).resultTy env = .ok resultType) :
    env.intTy left = .ok width ∧ env.intTy right = .ok width := by
  cases leftResult : env.intTy left with
  | error message => simp [Op.resultTy, leftResult, bind, Except.bind] at typed
  | ok leftType =>
    cases rightResult : env.intTy right with
    | error message => simp [Op.resultTy, leftResult, rightResult, bind, Except.bind] at typed
    | ok rightType =>
      have same : leftType = width ∧ rightType = width := by
        by_cases same : leftType = width ∧ rightType = width
        · exact same
        · simp [Op.resultTy, leftResult, rightResult, same, bind, Except.bind, tyErr] at typed
      rcases same with ⟨leftEqual, rightEqual⟩
      exact ⟨by simpa [leftEqual] using leftResult, by simpa [rightEqual] using rightResult⟩

private theorem boolCmp_result_bool_inputs {env : TyEnv} {operator : CmpOp}
    {left right : ValueId} {resultType : VTy}
    (typed : (Op.boolCmp operator left right).resultTy env = .ok resultType) :
    env.dataTy left = .ok .bool ∧ env.dataTy right = .ok .bool := by
  cases leftResult : env.dataTy left with
  | error message => simp [Op.resultTy, leftResult, bind, Except.bind] at typed
  | ok leftType =>
    cases rightResult : env.dataTy right with
    | error message => simp [Op.resultTy, leftResult, rightResult, bind, Except.bind] at typed
    | ok rightType =>
      have same : leftType = .bool ∧ rightType = .bool := by
        by_cases same : leftType = .bool ∧ rightType = .bool
        · exact same
        · simp [Op.resultTy, leftResult, rightResult, same, bind, Except.bind, tyErr] at typed
      rcases same with ⟨leftEqual, rightEqual⟩
      exact ⟨by simpa [leftEqual] using leftResult, by simpa [rightEqual] using rightResult⟩

private theorem boolNot_result_bool_input {env : TyEnv} {source : ValueId} {resultType : VTy}
    (typed : (Op.boolNot source).resultTy env = .ok resultType) :
    env.dataTy source = .ok .bool := by
  cases result : env.dataTy source with
  | error message => simp [Op.resultTy, result, bind, Except.bind] at typed
  | ok actual =>
    have same : actual = .bool := by
      by_cases same : actual = .bool
      · exact same
      · simp [Op.resultTy, result, same, bind, Except.bind, tyErr] at typed
    simpa [same] using result

private theorem refElem_viewTy {env : TyEnv} {source index : ValueId} {resultType : VTy}
    (typed : (Op.refElem source index).resultTy env = .ok resultType) :
    ∃ mutability element, env.viewTy source = .ok (mutability, element) := by
  cases result : env.viewTy source with
  | error message => simp_all [Op.resultTy, result, bind, Except.bind, tyErr]
  | ok pair => cases pair; exact ⟨_, _, rfl⟩

private theorem refElem_intTy {env : TyEnv} {source index : ValueId} {resultType : VTy}
    (typed : (Op.refElem source index).resultTy env = .ok resultType) :
    ∃ width, env.intTy index = .ok width := by
  cases viewResult : env.viewTy source with
  | error message => simp_all [Op.resultTy, viewResult, bind, Except.bind, tyErr]
  | ok pair =>
      cases indexResult : env.intTy index with
      | error message => simp_all [Op.resultTy, viewResult, indexResult, bind, Except.bind, tyErr]
      | ok width => exact ⟨width, rfl⟩

private theorem indexChecked_viewTy {env : TyEnv} {source index : ValueId}
    {origin : Option OriginId} {resultType : VTy}
    (typed : (Op.indexChecked source index origin).resultTy env = .ok resultType) :
    ∃ mutability element, env.viewTy source = .ok (mutability, element) := by
  cases result : env.viewTy source with
  | error message => simp_all [Op.resultTy, result, bind, Except.bind, tyErr]
  | ok pair => cases pair; exact ⟨_, _, rfl⟩

private theorem indexChecked_intTy {env : TyEnv} {source index : ValueId}
    {origin : Option OriginId} {resultType : VTy}
    (typed : (Op.indexChecked source index origin).resultTy env = .ok resultType) :
    ∃ width, env.intTy index = .ok width := by
  cases viewResult : env.viewTy source with
  | error message => simp_all [Op.resultTy, viewResult, bind, Except.bind, tyErr]
  | ok pair =>
      cases indexResult : env.intTy index with
      | error message => simp_all [Op.resultTy, viewResult, indexResult, bind, Except.bind, tyErr]
      | ok width => exact ⟨width, rfl⟩

private theorem indexProven_viewTy {env : TyEnv} {source index : ValueId} {resultType : VTy}
    (typed : (Op.indexProven source index).resultTy env = .ok resultType) :
    ∃ mutability element, env.viewTy source = .ok (mutability, element) := by
  cases result : env.viewTy source with
  | error message => simp_all [Op.resultTy, result, bind, Except.bind, tyErr]
  | ok pair => cases pair; exact ⟨_, _, rfl⟩

private theorem indexProven_intTy {env : TyEnv} {source index : ValueId} {resultType : VTy}
    (typed : (Op.indexProven source index).resultTy env = .ok resultType) :
    ∃ width, env.intTy index = .ok width := by
  cases viewResult : env.viewTy source with
  | error message => simp_all [Op.resultTy, viewResult, bind, Except.bind, tyErr]
  | ok pair =>
      cases indexResult : env.intTy index with
      | error message => simp_all [Op.resultTy, viewResult, indexResult, bind, Except.bind, tyErr]
      | ok width => exact ⟨width, rfl⟩

private theorem viewLen_viewTy {env : TyEnv} {source : ValueId} {resultType : VTy}
    (typed : (Op.viewLen source).resultTy env = .ok resultType) :
    ∃ mutability element, env.viewTy source = .ok (mutability, element) := by
  cases result : env.viewTy source with
  | error message => simp_all [Op.resultTy, result, bind, Except.bind, tyErr]
  | ok pair => cases pair; exact ⟨_, _, rfl⟩

private theorem viewSlice_viewTy {env : TyEnv} {mutability : Mutability} {source : ValueId}
    {low high : Bnd} {origin : Option OriginId} {resultType : VTy}
    (typed : (Op.viewSlice mutability source low high origin).resultTy env = .ok resultType) :
    ∃ sourceMutability element, env.viewTy source = .ok (sourceMutability, element) := by
  cases result : env.viewTy source with
  | error message => simp_all [Op.resultTy, result, bind, Except.bind, tyErr]
  | ok pair => cases pair; exact ⟨_, _, rfl⟩

theorem backing_source_nonwhole_or_direct {env : TyEnv} {types : Array (Option VTy)}
    {value source : ValueId} {op : Op} {resultType : VTy}
    (shapes : ValueTypeShapes types) (values : env.vals = types)
    (produced : op.resultTy env = .ok resultType) (backing : BackingOp op source) :
    (∃ sourceType, types[source]? = some (some sourceType) ∧
      wholeOwnerReference sourceType = false) ∨
      source ∈ directTouchOperands (.def value op) := by
  cases backing with
  | field source field =>
      obtain ⟨mutability, id, fields, sourceTyped⟩ := fieldAddr_refStructTy produced
      have sourceRow := TyEnv.refTy_known sourceTyped
      left
      refine ⟨.data (.ref mutability (.structT id fields)), ?_, ?_⟩
      · simpa [values] using sourceRow
      · simp [wholeOwnerReference, Ty.ownerElem?]
  | element source index =>
      obtain ⟨mutability, element, sourceTyped⟩ := refElem_viewTy produced
      left
      refine ⟨.view mutability element, ?_, ?_⟩
      · simpa [values] using TyEnv.viewTy_known sourceTyped
      · simp [wholeOwnerReference]
  | slice mutability source low high origin =>
      obtain ⟨sourceMutability, element, sourceTyped⟩ := viewSlice_viewTy produced
      left
      refine ⟨.view sourceMutability element, ?_, ?_⟩
      · simpa [values] using TyEnv.viewTy_known sourceTyped
      · simp [wholeOwnerReference]
  | checked source index origin =>
      obtain ⟨mutability, element, sourceTyped⟩ := indexChecked_viewTy (origin := origin) produced
      left
      refine ⟨.view mutability element, ?_, ?_⟩
      · simpa [values] using TyEnv.viewTy_known sourceTyped
      · simp [wholeOwnerReference]
  | proven source index =>
      obtain ⟨mutability, element, sourceTyped⟩ := indexProven_viewTy produced
      left
      refine ⟨.view mutability element, ?_, ?_⟩
      · simpa [values] using TyEnv.viewTy_known sourceTyped
      · simp [wholeOwnerReference]
  | view source =>
      cases sourceResult : env.dataTy source with
      | error message => simp [Op.resultTy, sourceResult, bind, Except.bind, tyErr] at produced
      | ok sourcePayload =>
          cases sourcePayload with
          | slice mutability element =>
              left
              refine ⟨.data (.slice mutability element), ?_, ?_⟩
              · simpa [values] using TyEnv.dataTy_known sourceResult
              · simp [wholeOwnerReference]
          | _ => simp [Op.resultTy, sourceResult, bind, Except.bind, tyErr] at produced
  | push source value origin => right; simp [directTouchOperands]
  | snapshot mode source => right; simp [directTouchOperands]

private theorem viewSlice_boundTypes {env : TyEnv} {mutability : Mutability} {source : ValueId}
    {low high : Bnd} {origin : Option OriginId} {resultType : VTy}
    (typed : (Op.viewSlice mutability source low high origin).resultTy env = .ok resultType) :
    env.boundTy low = .ok () ∧ env.boundTy high = .ok () := by
  cases viewResult : env.viewTy source with
  | error message => simp_all [Op.resultTy, viewResult, bind, Except.bind, tyErr]
  | ok pair =>
      cases mutabilityOk : pair.1.atLeast mutability with
      | false => simp_all [Op.resultTy, viewResult, mutabilityOk, bind, Except.bind, tyErr]
      | true =>
          cases lowResult : env.boundTy low with
          | error message => simp_all [Op.resultTy, viewResult, mutabilityOk, lowResult, bind, Except.bind, tyErr]
          | ok _ =>
              cases highResult : env.boundTy high with
              | error message => simp_all [Op.resultTy, viewResult, mutabilityOk, lowResult, highResult, bind, Except.bind, tyErr]
              | ok _ => exact ⟨by simpa using lowResult, by simpa using highResult⟩

private theorem sliceView_dataTy {env : TyEnv} {source : ValueId} {resultType : VTy}
    (typed : (Op.sliceView source).resultTy env = .ok resultType) :
    ∃ mutability element, env.dataTy source = .ok (.slice mutability element) := by
  cases result : env.dataTy source with
  | error message => simp_all [Op.resultTy, result, bind, Except.bind, tyErr]
  | ok dataType =>
      cases dataType with
      | slice mutability element => exact ⟨mutability, element, rfl⟩
      | _ => simp_all [Op.resultTy, result, bind, Except.bind, tyErr]

private theorem push_dataTy {env : TyEnv} {owner value : ValueId}
    {origin : Option OriginId} {resultType : VTy}
    (typed : (Op.push owner value origin).resultTy env = .ok resultType) :
    ∃ mutability payload element,
      env.refTy owner = .ok (mutability, payload) ∧
      payload.ownerElem? = some element ∧ env.dataTy value = .ok element := by
  cases reference : env.refTy owner with
  | error message => simp_all [Op.resultTy, reference, bind, Except.bind, tyErr]
  | ok pair =>
      cases elementRow : pair.2.ownerElem? with
      | none => simp_all [Op.resultTy, reference, elementRow, bind, Except.bind, tyErr]
      | some element =>
          cases elementType : env.dataTy value with
          | error message => simp_all [Op.resultTy, reference, elementRow, elementType, bind, Except.bind, tyErr]
          | ok actual =>
              have same : actual = element := by
                by_cases same : actual = element
                · exact same
                · simp [Op.resultTy, reference, elementRow, elementType, same, bind, Except.bind, tyErr] at typed
              cases pair with
              | mk mutability payload => exact ⟨mutability, payload, element, rfl, elementRow, by simpa [same] using elementType⟩

theorem noncall_wholeOwner_access_direct {module : GIR.Module} {func : Func}
    {types : Array (Option VTy)} {inst : Inst} {source : ValueId} {type : VTy}
    (shapes : ValueTypeShapes types)
    (globals : ∀ (index : Nat) (globalType : Ty) (kind : VarKind),
      (module.tyEnv func).globals[index]? = some (globalType, kind) → globalType.isRefLike = false)
    (fields : ∀ (index : Nat) (descriptor : StructDef),
      (module.tyEnv func).structs[index]? = some descriptor →
      ∀ (fieldIndex : Nat) (field : StructField), descriptor.fields[fieldIndex]? = some field →
        field.ty.flat = true)
    (checked : checkInstTypes func {module.tyEnv func with vals := types} types inst = .ok ())
    (noncall : ∀ (value : ValueId) (fn : FnId) (args : List ValueId) (origin : Option OriginId),
      inst ≠ .def value (.call fn args origin))
    (accessed : source ∈ accessOperands inst)
    (row : types[source]? = some (some type))
    (wholeOwner : wholeOwnerReference type = true) :
    source ∈ directTouchOperands inst := by
  cases inst with
  | «def» value op =>
      let env : TyEnv := {module.tyEnv func with vals := types}
      have native : checkInstTypes func env types (.def value op) = .ok () := checked
      have existsProduced : ∃ resultType, op.resultTy env = .ok resultType := by
        have nativeBind := by simpa only [checkInstTypes] using native
        obtain ⟨resultType, resultOk, _⟩ := GIR.bind_ok nativeBind
        exact ⟨resultType, resultOk⟩
      obtain ⟨resultType, produced⟩ := existsProduced
      have outputRow := checked_definition_result native produced
      have values : env.vals = types := rfl
      have envShapes : ValueTypeShapes env.vals := by simpa [values] using shapes
      have rowInEnv : env.vals[source]? = some (some type) := by simpa [values] using row
      cases op with
      | bin operator width left right origin =>
          have inputs := bin_result_int_inputs produced
          simp [accessOperands, Inst.uses, Op.uses, directTouchOperands] at accessed ⊢
          rcases accessed with leftSource | rightSource
          · subst source
            exact False.elim (not_wholeOwner_of_intTy values rowInEnv wholeOwner inputs.1)
          · subst source
            exact False.elim (not_wholeOwner_of_intTy values rowInEnv wholeOwner inputs.2)
      | un operator width input origin =>
          have inputTyped := unary_result_int_input produced
          simp [accessOperands, Inst.uses, Op.uses, directTouchOperands] at accessed ⊢
          subst source
          exact False.elim (not_wholeOwner_of_intTy values rowInEnv wholeOwner inputTyped)
      | cmp operator width left right =>
          have inputs := cmp_result_int_inputs produced
          simp [accessOperands, Inst.uses, Op.uses, directTouchOperands] at accessed ⊢
          rcases accessed with leftSource | rightSource
          · subst source
            exact False.elim (not_wholeOwner_of_intTy values rowInEnv wholeOwner inputs.1)
          · subst source
            exact False.elim (not_wholeOwner_of_intTy values rowInEnv wholeOwner inputs.2)
      | boolCmp operator left right =>
          have inputs := boolCmp_result_bool_inputs produced
          simp [accessOperands, Inst.uses, Op.uses, directTouchOperands] at accessed ⊢
          rcases accessed with leftSource | rightSource
          · subst source
            exact False.elim (not_wholeOwner_of_boolTy values rowInEnv wholeOwner inputs.1)
          · subst source
            exact False.elim (not_wholeOwner_of_boolTy values rowInEnv wholeOwner inputs.2)
      | boolNot input =>
          have inputTyped := boolNot_result_bool_input produced
          simp [accessOperands, Inst.uses, Op.uses, directTouchOperands] at accessed ⊢
          subst source
          exact False.elim (not_wholeOwner_of_boolTy values rowInEnv wholeOwner inputTyped)
      | conv conversion sourceWidth destWidth input origin =>
          cases inputResult : env.intTy input with
          | error message => simp [Op.resultTy, inputResult, bind, Except.bind] at produced
          | ok actualWidth =>
              have same : actualWidth = sourceWidth := by
                by_cases same : actualWidth = sourceWidth
                · exact same
                · simp [Op.resultTy, inputResult, same, bind, Except.bind, tyErr] at produced
              have inputTyped : env.intTy input = .ok sourceWidth := by simpa [same] using inputResult
              simp [accessOperands, Inst.uses, Op.uses, directTouchOperands] at accessed ⊢
              subst source
              exact False.elim (not_wholeOwner_of_intTy values rowInEnv wholeOwner inputTyped)
      | next width input =>
          cases inputResult : env.intTy input with
          | error message => simp [Op.resultTy, inputResult, bind, Except.bind] at produced
          | ok actualWidth =>
              have same : actualWidth = width := by
                by_cases same : actualWidth = width
                · exact same
                · simp [Op.resultTy, inputResult, same, bind, Except.bind, tyErr] at produced
              have inputTyped : env.intTy input = .ok width := by simpa [same] using inputResult
              simp [accessOperands, Inst.uses, Op.uses, directTouchOperands] at accessed ⊢
              subst source
              exact False.elim (not_wholeOwner_of_intTy values rowInEnv wholeOwner inputTyped)
      | refElem input index =>
          obtain ⟨mutability, element, inputTyped⟩ := refElem_viewTy produced
          simp [accessOperands, Inst.uses, Op.uses, directTouchOperands] at accessed ⊢
          rcases accessed with sourceInput | sourceIndex
          · subst source
            exact False.elim (not_wholeOwner_of_viewTy values rowInEnv wholeOwner inputTyped)
          · subst source
            obtain ⟨width, indexTyped⟩ := refElem_intTy produced
            exact False.elim (not_wholeOwner_of_intTy values rowInEnv wholeOwner indexTyped)
      | refFreeze _ => simp [accessOperands] at accessed
      | ownerBorrow _ => simp [accessOperands] at accessed
      | load owner => simpa [accessOperands, Inst.uses, Op.uses, directTouchOperands] using accessed
      | snapshot mode owner => simpa [accessOperands, Inst.uses, Op.uses, directTouchOperands] using accessed
      | sliceView input =>
          obtain ⟨mutability, element, inputTyped⟩ := sliceView_dataTy produced
          simp [accessOperands, Inst.uses, Op.uses, directTouchOperands] at accessed ⊢
          subst source
          exact False.elim (not_wholeOwner_of_sliceTy values rowInEnv wholeOwner inputTyped)
      | viewLen input =>
          obtain ⟨mutability, element, inputTyped⟩ := viewLen_viewTy produced
          simp [accessOperands, Inst.uses, Op.uses, directTouchOperands] at accessed ⊢
          subst source
          exact False.elim (not_wholeOwner_of_viewTy values rowInEnv wholeOwner inputTyped)
      | viewSlice mutability input low high origin =>
          obtain ⟨sourceMutability, element, inputTyped⟩ := viewSlice_viewTy produced
          obtain ⟨lowTyped, highTyped⟩ := viewSlice_boundTypes produced
          simp [accessOperands, Inst.uses, Op.uses, directTouchOperands] at accessed ⊢
          rcases accessed with sourceInput | sourceBound
          · subst source
            exact False.elim (not_wholeOwner_of_viewTy values rowInEnv wholeOwner inputTyped)
          · rcases sourceBound with sourceLow | sourceHigh
            · cases low with
              | omitted => simp [Bnd.uses] at sourceLow
              | val bound =>
                  simp [Bnd.uses] at sourceLow
                  subst source
                  obtain ⟨width, intTyped⟩ := boundValue_intTy lowTyped
                  exact False.elim (not_wholeOwner_of_intTy values rowInEnv wholeOwner intTyped)
              | fromEnd bound =>
                  simp [Bnd.uses] at sourceLow
                  subst source
                  obtain ⟨width, intTyped⟩ := boundFromEnd_intTy lowTyped
                  exact False.elim (not_wholeOwner_of_intTy values rowInEnv wholeOwner intTyped)
            · cases high with
                | omitted => simp [Bnd.uses] at sourceHigh
                | val bound =>
                    simp [Bnd.uses] at sourceHigh
                    subst source
                    obtain ⟨width, intTyped⟩ := boundValue_intTy highTyped
                    exact False.elim (not_wholeOwner_of_intTy values rowInEnv wholeOwner intTyped)
                | fromEnd bound =>
                    simp [Bnd.uses] at sourceHigh
                    subst source
                    obtain ⟨width, intTyped⟩ := boundFromEnd_intTy highTyped
                    exact False.elim (not_wholeOwner_of_intTy values rowInEnv wholeOwner intTyped)
      | arrayLen owner => simpa [accessOperands, Inst.uses, Op.uses, directTouchOperands] using accessed
      | indexChecked input index origin =>
          obtain ⟨mutability, element, inputTyped⟩ := indexChecked_viewTy produced
          simp [accessOperands, Inst.uses, Op.uses, directTouchOperands] at accessed ⊢
          rcases accessed with sourceInput | sourceIndex
          · subst source
            exact False.elim (not_wholeOwner_of_viewTy values rowInEnv wholeOwner inputTyped)
          · subst source
            obtain ⟨width, indexTyped⟩ := indexChecked_intTy (origin := origin) produced
            exact False.elim (not_wholeOwner_of_intTy values rowInEnv wholeOwner indexTyped)
      | indexProven input index =>
          obtain ⟨mutability, element, inputTyped⟩ := indexProven_viewTy produced
          simp [accessOperands, Inst.uses, Op.uses, directTouchOperands] at accessed ⊢
          rcases accessed with sourceInput | sourceIndex
          · subst source
            exact False.elim (not_wholeOwner_of_viewTy values rowInEnv wholeOwner inputTyped)
          · subst source
            obtain ⟨width, indexTyped⟩ := indexProven_intTy produced
            exact False.elim (not_wholeOwner_of_intTy values rowInEnv wholeOwner indexTyped)
      | push owner element origin =>
          obtain ⟨mutability, payload, elementType, reference, elementOf, elementTyped⟩ := push_dataTy produced
          have flat := ownerElement_flat_of_reference_shape shapes rfl reference elementOf
          simp [accessOperands, Inst.uses, Op.uses, directTouchOperands] at accessed ⊢
          rcases accessed with sourceOwner | sourceElement
          · subst source; simp [directTouchOperands]
          · subst source
            exact False.elim (not_wholeOwner_of_dataTy_flat values rowInEnv wholeOwner elementTyped flat)
      | pop owner origin => simpa [accessOperands, Inst.uses, Op.uses, directTouchOperands] using accessed
      | call fn args origin => exact False.elim (noncall value fn args origin rfl)
      | arrLit type args =>
          cases type with
          | arr element count =>
              obtain ⟨inputs, resultEqual⟩ := arrLit_fixed_inputs produced
              have resultRow : types[value]? = some (some (.data (.arr element count))) := by
                rw [← resultEqual]
                exact outputRow
              have outputShape : DataTypeShape (.arr element count) := envShapes value _ resultRow
              have flat := ownerElement_flat_of_data_shape outputShape rfl
              have elementTyped := inputs source accessed
              simp [accessOperands, Inst.uses, Op.uses, directTouchOperands] at ⊢
              exact False.elim (not_wholeOwner_of_dataTy_flat values rowInEnv wholeOwner elementTyped flat)
          | grow element =>
              obtain ⟨inputs, resultEqual⟩ := arrLit_grow_inputs produced
              have resultRow : types[value]? = some (some (.data (.grow element))) := by
                rw [← resultEqual]
                exact outputRow
              have outputShape : DataTypeShape (.grow element) := envShapes value _ resultRow
              have flat := ownerElement_flat_of_data_shape outputShape rfl
              have elementTyped := inputs source accessed
              simp [accessOperands, Inst.uses, Op.uses, directTouchOperands] at ⊢
              exact False.elim (not_wholeOwner_of_dataTy_flat values rowInEnv wholeOwner elementTyped flat)
          | growshrink element =>
              obtain ⟨inputs, resultEqual⟩ := arrLit_growshrink_inputs produced
              have resultRow : types[value]? = some (some (.data (.growshrink element))) := by
                rw [← resultEqual]
                exact outputRow
              have outputShape : DataTypeShape (.growshrink element) := envShapes value _ resultRow
              have flat := ownerElement_flat_of_data_shape outputShape rfl
              have elementTyped := inputs source accessed
              simp [accessOperands, Inst.uses, Op.uses, directTouchOperands] at ⊢
              exact False.elim (not_wholeOwner_of_dataTy_flat values rowInEnv wholeOwner elementTyped flat)
          | limited element capacity =>
              obtain ⟨inputs, resultEqual⟩ := arrLit_limited_inputs produced
              have resultRow : types[value]? = some (some (.data (.limited element capacity))) := by
                rw [← resultEqual]
                exact outputRow
              have outputShape : DataTypeShape (.limited element capacity) := envShapes value _ resultRow
              have flat := ownerElement_flat_of_data_shape outputShape rfl
              have elementTyped := inputs source accessed
              simp [accessOperands, Inst.uses, Op.uses, directTouchOperands] at ⊢
              exact False.elim (not_wholeOwner_of_dataTy_flat values rowInEnv wholeOwner elementTyped flat)
          | _ => simp_all [Op.resultTy, accessOperands, Inst.uses, Op.uses, directTouchOperands, tyErr]
      | arrFill type element =>
          cases type with
          | arr elementType count =>
              cases dataResult : env.dataTy element with
              | error message => simp [Op.resultTy, dataResult, bind, Except.bind, tyErr] at produced
              | ok actualType =>
                  have same : actualType = elementType := by
                    by_cases same : actualType = elementType
                    · exact same
                    · simp [Op.resultTy, dataResult, same, bind, Except.bind, tyErr] at produced
                  have flat : elementType.flat = true := by
                    have resultEqual : resultType = .data (.arr elementType count) := by
                      simp [Op.resultTy, dataResult, same, bind, Except.bind, pure, Except.pure] at produced
                      exact produced.symm
                    rw [resultEqual] at outputRow
                    have outputShape := envShapes value _ outputRow
                    exact ownerElement_flat_of_data_shape outputShape (by rfl)
                  have elementTyped : env.dataTy element = .ok elementType := by simpa [same] using dataResult
                  simp [accessOperands, Inst.uses, Op.uses, directTouchOperands] at accessed ⊢
                  subst source
                  exact False.elim (not_wholeOwner_of_dataTy_flat values rowInEnv wholeOwner elementTyped flat)
          | _ => simp_all [Op.resultTy, accessOperands, Inst.uses, Op.uses, directTouchOperands, tyErr]
      | structLit type args =>
          cases type with
          | structT id typeFields =>
              simp only [Op.resultTy] at produced
              cases descriptorAt : env.structs[id]? with
              | none => simp [descriptorAt, tyErr] at produced
              | some descriptor =>
                  by_cases payloadValid : (typeFields == TyList.ofList (descriptor.fields.toList.map (·.ty))) = true
                  · by_cases countValid : (args.length == descriptor.fields.size) = true
                    · simp only [descriptorAt, payloadValid, countValid] at produced
                      obtain ⟨_, loopCheck, _⟩ := GIR.bind_ok produced
                      have inputs := dataFieldLoop_typed loopCheck
                      have lengths : args.length = descriptor.fields.toList.length := by
                        simpa using countValid
                      obtain ⟨field, fieldMember, zipped⟩ :=
                        mem_zip_same_left lengths accessed
                      have inputTyped := inputs (source, field) zipped
                      obtain ⟨fieldIndex, fieldAt⟩ :=
                        Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp fieldMember)
                      have descriptorRow : (module.tyEnv func).structs[id]? = some descriptor := by
                        simpa [env] using descriptorAt
                      have flat := fields id descriptor descriptorRow fieldIndex field fieldAt
                      simp [accessOperands, Inst.uses, Op.uses, directTouchOperands] at ⊢
                      exact False.elim (not_wholeOwner_of_dataTy_flat values rowInEnv wholeOwner inputTyped flat)
                    · simp [descriptorAt, payloadValid, countValid, tyErr, bind, Except.bind] at produced
                  · simp [descriptorAt, payloadValid, tyErr, bind, Except.bind] at produced
          | _ => simp_all [Op.resultTy, accessOperands, Inst.uses, Op.uses, directTouchOperands, tyErr]
      | slotAddr _ => simp [accessOperands] at accessed
      | globalAddr _ => simp [accessOperands] at accessed
      | fieldAddr _ _ => simp [accessOperands] at accessed
      | constInt _ _ | constBool _ | constUnit => simp [accessOperands, Inst.uses, Op.uses] at accessed
  | eff effect =>
      let env : TyEnv := {module.tyEnv func with vals := types}
      have native := checked_effect checked
      change checkEffectTypes env effect = .ok () at native
      have values : env.vals = types := rfl
      have rowInEnv : env.vals[source]? = some (some type) := by simpa [values] using row
      cases effect with
      | slotInit slot value origin => simp [accessOperands, Inst.uses, Effect.uses] at accessed
      | store owner value origin => simpa [accessOperands, Inst.uses, Effect.uses, directTouchOperands] using accessed
      | append owner value origin => simpa [accessOperands, Inst.uses, Effect.uses, directTouchOperands] using accessed
      | popN owner count origin =>
          simp [accessOperands, Inst.uses, Effect.uses] at accessed
          rcases accessed with ownerSource | countSource
          · subst source
            simp [directTouchOperands]
          · subst source
            obtain ⟨width, countTyped⟩ := popN_count_intTy native
            exact False.elim (not_wholeOwner_of_intTy values rowInEnv wholeOwner countTyped)
      | resize owner size fill origin =>
          cases fill with
          | none =>
              simp [accessOperands, Inst.uses, Effect.uses] at accessed
              rcases accessed with ownerSource | sizeSource
              · subst source; simp [directTouchOperands]
              · subst source
                obtain ⟨width, sizeTyped⟩ := resize_size_intTy native
                exact False.elim (not_wholeOwner_of_intTy values rowInEnv wholeOwner sizeTyped)
          | some fillValue =>
              simp [accessOperands, Inst.uses, Effect.uses] at accessed
              rcases accessed with ownerSource | sizeSource | fillSource
              · subst source; simp [directTouchOperands]
              · subst source
                obtain ⟨width, sizeTyped⟩ := resize_size_intTy native
                exact False.elim (not_wholeOwner_of_intTy values rowInEnv wholeOwner sizeTyped)
              · subst source
                obtain ⟨element, fillTyped, flat⟩ := resize_fill_dataTy shapes native
                exact False.elim (not_wholeOwner_of_dataTy_flat values rowInEnv wholeOwner fillTyped flat)
      | clear owner origin => simpa [accessOperands, Inst.uses, Effect.uses, directTouchOperands] using accessed
      | replace owner run origin =>
          simp [accessOperands, Inst.uses, Effect.uses] at accessed
          rcases accessed with ownerSource | runSource
          · subst source; simp [directTouchOperands]
          · subst source
            rcases replace_run_typed native with ⟨element, runTyped⟩ | ⟨element, runTyped⟩
            · exact False.elim (not_wholeOwner_of_dataTy values rowInEnv wholeOwner runTyped
                (by simp [wholeOwnerReference]))
            · exact False.elim (not_wholeOwner_of_dataTy values rowInEnv wholeOwner runTyped
                (by simp [wholeOwnerReference]))
      | enter scope => simp [accessOperands, Inst.uses, Effect.uses] at accessed
      | leave scope => simp [accessOperands, Inst.uses, Effect.uses] at accessed
      | print parts origin =>
          simp only [checkEffectTypes] at native
          obtain ⟨_, loopCheck, _⟩ := GIR.bind_ok native
          simp [accessOperands, Inst.uses, Effect.uses] at accessed
          have member : source ∈ parts.flatMap PrintPart.uses := by
            rcases accessed with ⟨part, partMember, sourceMember⟩
            exact List.mem_flatMap.mpr ⟨part, partMember, sourceMember⟩
          rcases printLoop_values_typed loopCheck source member with
            intType | boolType
          · rcases intType with ⟨width, sourceTyped⟩
            exact False.elim (not_wholeOwner_of_dataTy values rowInEnv wholeOwner sourceTyped
              (by simp [wholeOwnerReference]))
          · exact False.elim (not_wholeOwner_of_dataTy values rowInEnv wholeOwner boolType
              (by simp [wholeOwnerReference]))
  | term term =>
      simp [accessOperands, Inst.uses] at accessed

end Goose.Lower.Validation.SourceTouchOperandsTyping
