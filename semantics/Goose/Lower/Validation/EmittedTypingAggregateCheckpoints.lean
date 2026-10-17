import Goose.Lower.Validation.EmittedTypingCheckpoints
import Goose.Lower.Validation.ExpressionTypingAggregateOps

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem TypedValues.emitted_bounds {state : LS} {types : List Ty} {values : List ValueId}
    (typed : TypedValues state types values) : ∀ value ∈ values, value < state.vals.size := by
  induction typed with
  | nil => intro value member; cases member
  | cons head tail inductionHypothesis =>
    intro value member
    rcases List.mem_cons.mp member with rfl | rest
    · exact (Array.getElem?_eq_some_iff.mp head).1
    · exact inductionHypothesis value rest

theorem EmittedBuilder.arrayLiteral {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (type element : Ty) (values : List ValueId)
    (shape : GIR.arrayElem? type = some element) (count : ArrayLiteralCount type values.length)
    (typed : ∀ value ∈ values, before.vals[value]? = some (some (.data element))) :
    EmittedBuilder le initial (Goose.Lower.emitDef (.arrLit type values) le before).2 := by
  apply builder.emitDef (.arrLit type values) (fun _ => ⟨.data type, arrayLiteral_resultTy shape count typed⟩)
  intro active value member
  have actual : value ∈ values := by simpa [Op.uses] using member
  exact (Array.getElem?_eq_some_iff.mp (typed value actual)).1

theorem emitted_checked_structLiteral {env : Core.TEnv} {type : Ty} {descriptor : StructDef}
    {start finish : Nat} (definition : Core.structDef env type start = .ok (descriptor, finish))
    {vars : Array LocalVar} {results : List Ty} {initial before : LS}
    (builder : EmittedBuilder (lowerEnv env.mod vars results) initial before) (values : List ValueId)
    (typed : TypedValues before (descriptor.fields.toList.map (·.ty)) values) :
    EmittedBuilder (lowerEnv env.mod vars results) initial
      (Goose.Lower.emitDef (.structLit type values) (lowerEnv env.mod vars results) before).2 := by
  apply builder.emitDef (.structLit type values) (fun _ => ⟨.data type, structLiteral_resultTy definition typed⟩)
  intro active value member
  exact typed.emitted_bounds value (by simpa [Op.uses] using member)

theorem EmittedBuilder.arrayFill {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (element : Ty) (count : Nat) (value : ValueId)
    (typed : before.vals[value]? = some (some (.data element))) :
    EmittedBuilder le initial (Goose.Lower.emitDef (.arrFill (.arr element count) value) le before).2 := by
  apply builder.emitDef (.arrFill (.arr element count) value)
  · intro active
    exact ⟨.data (.arr element count), by
      simp [Op.resultTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, typed, pure, Except.pure, bind, Except.bind]⟩
  · intro active operand member
    have same : operand = value := by simpa [Op.uses] using member
    subst operand
    exact (Array.getElem?_eq_some_iff.mp typed).1

theorem EmittedBuilder.push {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (owner value : ValueId) (mu : Mutability) (ownerType element : Ty)
    (ownerTyped : before.vals[owner]? = some (some (.data (.ref mu ownerType))))
    (elementType : ownerType.ownerElem? = some element)
    (valueTyped : before.vals[value]? = some (some (.data element))) (origin : Option OriginId) :
    EmittedBuilder le initial (Goose.Lower.emitDef (.push owner value origin) le before).2 := by
  apply builder.emitDef (.push owner value origin)
  · intro active
    exact ⟨.data (.ref .mutable element), by
      simp [Op.resultTy, TyEnv.refTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, ownerTyped, elementType, valueTyped,
        pure, Except.pure, bind, Except.bind]⟩
  · intro active operand member
    have either : operand = owner ∨ operand = value := by simpa [Op.uses] using member
    rcases either with rfl | rfl
    · exact (Array.getElem?_eq_some_iff.mp ownerTyped).1
    · exact (Array.getElem?_eq_some_iff.mp valueTyped).1

theorem EmittedBuilder.pop {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (owner : ValueId) (mu : Mutability) (ownerType element : Ty)
    (ownerTyped : before.vals[owner]? = some (some (.data (.ref mu ownerType))))
    (elementType : ownerType.ownerElem? = some element) (origin : OriginId) :
    EmittedBuilder le initial (Goose.Lower.emitDef (.pop owner (some origin)) le before).2 := by
  apply builder.emitDef (.pop owner (some origin))
  · intro active
    exact ⟨.data element, by
      simp [Op.resultTy, TyEnv.refTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, ownerTyped, elementType,
        pure, Except.pure, bind, Except.bind]⟩
  · intro active operand member
    have same : operand = owner := by simpa [Op.uses] using member
    subst operand
    exact (Array.getElem?_eq_some_iff.mp ownerTyped).1

theorem EmittedBuilder.fieldAddr {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (owner index id : Nat) (fields : TyList) (mu : Mutability)
    (descriptor : StructDef) (field : StructField)
    (ownerTyped : before.vals[owner]? = some (some (.data (.ref mu (.structT id fields)))))
    (table : le.mod.structs[id]? = some descriptor)
    (payload : fields = TyList.ofList (descriptor.fields.toList.map (·.ty)))
    (fieldRow : descriptor.fields[index]? = some field) :
    EmittedBuilder le initial (Goose.Lower.emitDef (.fieldAddr owner index) le before).2 := by
  apply builder.emitDef (.fieldAddr owner index)
  · intro active
    exact ⟨.data (.ref (Mutability.ofKind field.binding) field.ty), by
      simp [Op.resultTy, TyEnv.refTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, ownerTyped,
        table, payload, fieldRow, pure, Except.pure, bind, Except.bind]⟩
  · intro active operand member
    have same : operand = owner := by simpa [Op.uses] using member
    subst operand
    exact (Array.getElem?_eq_some_iff.mp ownerTyped).1

end Goose.Lower.Validation
