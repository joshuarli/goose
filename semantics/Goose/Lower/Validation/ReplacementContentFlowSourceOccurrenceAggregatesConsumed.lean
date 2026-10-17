import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceScalarsConsumed
import Goose.Lower.Validation.ExpressionTypingAggregateOps

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

theorem sourceArrayElement_flat {env : TEnv} {arrayType resultType element : Ty}
    {expressions : List Expr} {start finish : Nat}
    (source : Core.tyExpr env (.arrLit arrayType expressions) start = .ok (resultType, finish))
    (shape : GIR.arrayElem? arrayType = some element) : element.flat = true := by
  simp only [Core.tyExpr] at source
  obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  cases arrayType <;> simp only [GIR.arrayElem?] at shape
  all_goals try contradiction
  all_goals cases shape
  all_goals
    by_cases flat : element.flat = true
    · exact flat
    · simp [flat, chk] at source

theorem sourceFillElement_flat {env : TEnv} {element resultType : Ty} {size : Nat}
    {expression : Expr} {start finish : Nat}
    (source : Core.tyExpr env (.fill (.arr element size) expression) start = .ok (resultType, finish)) :
    element.flat = true := by
  simp only [Core.tyExpr] at source
  obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  by_cases flat : element.flat = true
  · exact flat
  · simp [flat, chk] at source

theorem sourceStructFields_flat {env : TEnv} {type : Ty} {start finish : Nat} {descriptor : Core.StructDef}
    (source : Core.structDef env type start = .ok (descriptor, finish)) :
    ∀ fieldType ∈ descriptor.fields.toList.map (·.ty), fieldType.flat = true := by
  obtain ⟨sid, fields, rfl, flat, canonical, found, _⟩ := structDef_ok _ _ _ _ _ source
  simp only [Module.structType?, found, Option.map_some, Option.some.injEq, Ty.structT.injEq] at canonical
  obtain ⟨_, rfl⟩ := canonical
  intro fieldType member
  obtain ⟨index, row⟩ := List.mem_iff_getElem?.mp member
  exact tyList_flat_get _ flat index fieldType (by simpa only [tyList_toList_ofList] using row)

theorem typedValues_no_reference {state : LS} {types : Array (Option VTy)}
    {expected : List Ty} {values : List ValueId}
    (typed : TypedValues state expected values) (native : NativeRows types state)
    (flat : ∀ type ∈ expected, type.flat = true) :
    ∀ value ∈ values, ∀ mutability payload,
      types[value]? ≠ some (some (.data (.ref mutability payload))) := by
  induction typed with
  | nil => simp
  | @cons type value rest remaining head tail ih =>
    intro candidate member mutability payload
    rcases List.mem_cons.mp member with rfl | member
    · exact nativeFlat_not_reference (native _ _ head) (flat _ (by simp)) mutability payload
    · exact ih (fun type member => flat type (by simp [member])) candidate member mutability payload

#print axioms sourceArrayElement_flat
#print axioms sourceFillElement_flat
#print axioms sourceStructFields_flat
#print axioms typedValues_no_reference

end Goose.Lower.Validation.ReplacementContentFlowSource
