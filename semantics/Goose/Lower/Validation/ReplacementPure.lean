import Goose.Lower.Validation.ReplacementClearSpan
import Goose.Evidence.TypingMetadata

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

inductive ScalarOp : Op → Prop
  | constInt (ty value) : ScalarOp (.constInt ty value)
  | constBool (value) : ScalarOp (.constBool value)
  | constUnit : ScalarOp .constUnit
  | bin (operator ty left right origin) : ScalarOp (.bin operator ty left right origin)
  | un (operator ty operand origin) : ScalarOp (.un operator ty operand origin)
  | cmp (operator ty left right) : ScalarOp (.cmp operator ty left right)
  | boolCmp (operator left right) : ScalarOp (.boolCmp operator left right)
  | boolNot (operand) : ScalarOp (.boolNot operand)
  | conv (kind source target operand origin) : ScalarOp (.conv kind source target operand origin)
  | next (ty operand) : ScalarOp (.next ty operand)

theorem scalarOp_reference_free {env : TyEnv} {op : Op} {result : VTy}
    (scalar : ScalarOp op) (typed : op.resultTy env = .ok result) :
    result.refLike = false ∧ ∀ value ∈ op.uses, valRefLike env.vals value = false := by
  cases scalar with
  | constInt ty value =>
    have resultType := (constInt_metadata typed).2
    subst result
    simp [VTy.refLike, Op.uses, Ty.isRefLike]
  | constBool value =>
    have resultType := constBool_metadata typed
    subst result
    simp [VTy.refLike, Op.uses, Ty.isRefLike]
  | constUnit =>
    have resultType := constUnit_metadata typed
    subst result
    simp [VTy.refLike, Op.uses, Ty.isRefLike]
  | bin operator ty left right origin =>
    obtain ⟨leftType, rightType, resultType⟩ := bin_metadata typed
    subst result
    simp_all [VTy.refLike, Op.uses, Ty.isRefLike, valRefLike]
  | un operator ty operand origin =>
    obtain ⟨operandType, resultType⟩ := un_metadata typed
    subst result
    simp_all [VTy.refLike, Op.uses, Ty.isRefLike, valRefLike]
  | cmp operator ty left right =>
    obtain ⟨leftType, rightType, resultType⟩ := cmp_metadata typed
    subst result
    simp_all [VTy.refLike, Op.uses, Ty.isRefLike, valRefLike]
  | boolCmp operator left right =>
    obtain ⟨leftType, rightType, resultType⟩ := boolCmp_metadata typed
    subst result
    simp_all [VTy.refLike, Op.uses, Ty.isRefLike, valRefLike]
  | boolNot operand =>
    obtain ⟨operandType, resultType⟩ := boolNot_metadata typed
    subst result
    simp_all [VTy.refLike, Op.uses, Ty.isRefLike, valRefLike]
  | conv kind source target operand origin =>
    obtain ⟨operandType, resultType⟩ := conv_metadata typed
    subst result
    simp_all [VTy.refLike, Op.uses, Ty.isRefLike, valRefLike]
  | next ty operand =>
    obtain ⟨operandType, resultType⟩ := next_metadata typed
    subst result
    simp_all [VTy.refLike, Op.uses, Ty.isRefLike, valRefLike]

theorem ReplacementInstApart.scalar {module : GIR.Module} {types : Array (Option VTy)}
    {queries : ReplacementQueries} {owner value : ValueId} {op : Op} {result : VTy} {env : TyEnv}
    (scalar : ScalarOp op) (typed : op.resultTy env = .ok result) (values : env.vals = types)
    (recorded : types[value]? = some (some result)) :
    ReplacementInstApart module types queries owner (.def value op) := by
  have referenceFree := scalarOp_reference_free scalar typed
  constructor
  · intro operand member reference
    have operands : emptyFactSourceOperands (.def value op) = op.uses := by cases scalar <;> rfl
    rw [operands] at member
    have absent := referenceFree.2 operand member
    rw [values] at absent
    simp only [reference] at absent
    contradiction
  · intro resultValue operation same reference
    obtain ⟨rfl, rfl⟩ := Inst.def.inj same
    simp only [valRefLike, recorded, referenceFree.1] at reference
    contradiction
  · intro receiver accessed
    cases scalar <;> cases accessed
  · intro resultValue function args origin same
    cases scalar <;> cases same

theorem ReplacementInstApart.literal {module : GIR.Module} {types : Array (Option VTy)}
    {queries : ReplacementQueries} {owner value : ValueId} {ty : Ty} {operands : List ValueId}
    {result : VTy} {env : TyEnv}
    (typed : (Op.arrLit ty operands).resultTy env = .ok result) (values : env.vals = types)
    (recorded : types[value]? = some (some result))
    (flat : ∀ element, arrayElem? ty = some element → element.flat = true) :
    ReplacementInstApart module types queries owner (.def value (.arrLit ty operands)) := by
  obtain ⟨element, shape, operandTypes, _, _, resultType⟩ := arrLit_metadata typed
  have elementNotRef : element.isRefLike = false := by
    have flatElement := flat element shape
    cases element <;> simp_all [Ty.flat, Ty.isRefLike]
  have resultNotRef : ty.isRefLike = false := by
    cases ty <;> simp_all [arrayElem?, Ty.isRefLike]
  constructor
  · intro operand member reference
    have operandMember : operand ∈ operands := member
    have row := operandTypes operand operandMember
    rw [values] at row
    simp [valRefLike, row, VTy.refLike, elementNotRef] at reference
  · intro resultValue op same reference
    obtain ⟨rfl, rfl⟩ := Inst.def.inj same
    simp [valRefLike, recorded, resultType, VTy.refLike, resultNotRef] at reference
  · intro receiver accessed
    cases accessed
  · intro resultValue fn args origin same
    cases same

theorem source_arrLit_element_flat {env : Core.TEnv} {ty result : Ty} {exprs : List Expr}
    {start finish : Nat} (source : Core.tyExpr env (.arrLit ty exprs) start = .ok (result, finish))
    {element : Ty} (shape : arrayElem? ty = some element) : element.flat = true := by
  cases ty with
  | arr el count =>
    simp only [arrayElem?, Option.some.injEq] at shape
    subst element
    simp only [Core.tyExpr] at source
    obtain ⟨_, _, _, source⟩ := (Core.Sound.st_bind_ok _ _ _ _).mp source
    by_cases flat : el.flat = true
    · exact flat
    · simp only [flat, Bool.eq_false_iff.mpr flat, Bool.false_and, ite_false] at source
      obtain ⟨_, _, rejected, _⟩ := (Core.Sound.st_bind_ok _ _ _ _).mp source
      exact (Core.Sound.rej_ok _ _ _ _).mp rejected |>.elim
  | grow el =>
    simp only [arrayElem?, Option.some.injEq] at shape
    subst element
    simp only [Core.tyExpr] at source
    obtain ⟨_, _, _, source⟩ := (Core.Sound.st_bind_ok _ _ _ _).mp source
    by_cases flat : el.flat = true
    · exact flat
    · simp only [flat, Bool.eq_false_iff.mpr flat, Bool.false_and, ite_false] at source
      obtain ⟨_, _, rejected, _⟩ := (Core.Sound.st_bind_ok _ _ _ _).mp source
      exact (Core.Sound.rej_ok _ _ _ _).mp rejected |>.elim
  | growshrink el =>
    simp only [arrayElem?, Option.some.injEq] at shape
    subst element
    simp only [Core.tyExpr] at source
    obtain ⟨_, _, _, source⟩ := (Core.Sound.st_bind_ok _ _ _ _).mp source
    by_cases flat : el.flat = true
    · exact flat
    · simp only [flat, Bool.eq_false_iff.mpr flat, Bool.false_and, ite_false] at source
      obtain ⟨_, _, rejected, _⟩ := (Core.Sound.st_bind_ok _ _ _ _).mp source
      exact (Core.Sound.rej_ok _ _ _ _).mp rejected |>.elim
  | limited el capacity =>
    simp only [arrayElem?, Option.some.injEq] at shape
    subst element
    simp only [Core.tyExpr] at source
    obtain ⟨_, _, _, source⟩ := (Core.Sound.st_bind_ok _ _ _ _).mp source
    by_cases flat : el.flat = true
    · exact flat
    · simp only [flat, Bool.eq_false_iff.mpr flat, Bool.false_and, ite_false] at source
      obtain ⟨_, _, rejected, _⟩ := (Core.Sound.st_bind_ok _ _ _ _).mp source
      exact (Core.Sound.rej_ok _ _ _ _).mp rejected |>.elim
  | _ => simp [arrayElem?] at shape

end Goose.Lower.Validation
