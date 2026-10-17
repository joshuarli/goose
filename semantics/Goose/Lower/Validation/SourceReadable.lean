import Goose.Lower.Validation.SourceReadableEnvironment
import Goose.Lower.Validation.ExpressionTypingSliceOps
import Goose.Lower.Validation.ExpressionTypingContentsChildren

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound

private theorem paramOk_refTarget {type : Ty} (target : type.refTarget = true) : type.paramOk = true := by
  cases type <;> simp_all [Ty.refTarget, Ty.paramOk, Ty.storable, Ty.isRefSlice]

private theorem paramOk_owner_element {type element : Ty}
    (allowed : type.paramOk = true) (owner : type.ownerElem? = some element) : element.flat = true := by
  cases type <;> simp_all [Ty.paramOk, Ty.storable, Ty.isRefSlice, Ty.ownerElem?]

private theorem flat_paramOk {type : Ty} (flat : type.flat = true) : type.paramOk = true :=
  paramOk_refTarget (flat_refTarget flat)

mutual

theorem source_expression_refLike_readable (expression : Expr)
    {env : Core.TEnv} (checked : SourceReadableEnvironment env) {type : Ty} {start finish : Nat}
    (source : Core.tyExpr env expression start = .ok (type, finish))
    (reference : type.isRefLike = true) : type.readable = true := by
  cases expression with
  | lit integer number =>
    by_cases range : integer.inRange number
    · simp only [Core.tyExpr, range, ite_true] at source
      have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
      dsimp only at shape
      rw [shape] at reference
      cases reference
    · simp [Core.tyExpr, range, rej_ok] at source
  | bool value =>
    have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
    dsimp only at shape
    rw [shape] at reference
    cases reference
  | read place =>
    simp only [Core.tyExpr] at source
    obtain ⟨info, next, placeSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    by_cases readable : info.ty.readable = true
    · simp only [readable, ite_true] at source
      have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
      dsimp only at shape
      rw [shape]
      exact readable
    · simp [readable, rej_ok] at source
  | ref mutability place =>
    have original := source
    obtain ⟨info, next, placeSource, shape, _⟩ := tyExpr_ref_place original
    rw [shape]
    change info.ty.refTarget = true
    simp only [Core.tyExpr] at source
    obtain ⟨actualInfo, actualNext, child, source⟩ := (st_bind_ok _ _ _ _).mp source
    rw [placeSource] at child
    cases Except.ok.inj child
    obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    by_cases target : info.ty.refTarget = true
    · exact target
    · simp [target, chk] at source
  | slice mutability view low high origin =>
    obtain ⟨element, writable, viewStart, viewFinish, lowFinish, highFinish,
      viewSource, lowSource, highSource, shape⟩ := tyExpr_slice_children source
    rw [shape]
    exact source_view_element_flat view checked viewSource
  | len view =>
    simp only [Core.tyExpr] at source
    obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
    dsimp only at shape
    rw [shape] at reference
    cases reference
  | un operation child origin =>
    obtain ⟨_, _, _, _, shape, _⟩ := tyExpr_un_child source
    rw [shape] at reference
    cases reference
  | bin operation left right origin =>
    obtain ⟨_, _, _, _, _, _, _, shape⟩ := tyExpr_bin_children source
    rw [shape] at reference
    cases reference
  | not child =>
    obtain ⟨_, _, shape⟩ := tyExpr_not_child source
    rw [shape] at reference
    cases reference
  | conv kind target child origin =>
    obtain ⟨_, _, _, _, _, _, shape, _⟩ := tyExpr_conversion_child source
    rw [shape] at reference
    cases reference
  | cmp operation left right =>
    obtain ⟨_, _, _, _, _, _, shape, _⟩ := tyExpr_comparison_children source
    rw [shape] at reference
    cases reference
  | and left right | or left right =>
    simp only [Core.tyExpr] at source
    obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
    dsimp only at shape
    rw [shape] at reference
    cases reference
  | push owner child origin =>
    obtain ⟨info, element, ownerStart, ownerFinish, childStart, childFinish,
      ownerSource, ownerElement, childSource, shape⟩ := tyExpr_push_children source
    rw [shape]
    exact flat_refTarget (paramOk_owner_element
      (source_place_paramOk owner checked ownerSource) ownerElement)
  | pop owner origin =>
    obtain ⟨info, ownerStart, ownerFinish, ownerSource, ownerElement⟩ := tyExpr_pop_owner source
    have flat := paramOk_owner_element (source_place_paramOk owner checked ownerSource) ownerElement
    cases type <;> simp_all [Ty.flat, Ty.isRefLike, Ty.readable]
  | arrLit arrayType children =>
    obtain ⟨shape, element, childStart, childFinish, arrayShape, _, _⟩ := tyExpr_arrayLiteral_children source
    rw [shape] at reference
    cases arrayType <;> simp_all [GIR.arrayElem?, Ty.isRefLike]
  | fill arrayType child =>
    obtain ⟨shape, element, size, childStart, childFinish, arrayShape, _⟩ := tyExpr_fill_child source
    rw [shape, arrayShape] at reference
    cases reference
  | structLit structType children =>
    obtain ⟨shape, descriptor, definitionFinish, childStart, childFinish, definition, _⟩ :=
      tyExpr_structLiteral_children source
    obtain ⟨id, fields, ownerShape, _, _, _, _⟩ := structDef_ok _ _ _ _ _ definition
    rw [shape, ownerShape] at reference
    cases reference
  | call context arguments origin =>
    obtain ⟨ctx, callee, _, _, _, contextRow, calleeRow, _, _, resultSource⟩ := tyExpr_call_tables source
    cases results : callee.results.toList with
    | nil =>
      simp only [Core.callResultTy, results] at resultSource
      have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp resultSource)
      dsimp only at shape
      rw [shape] at reference
      cases reference
    | cons result rest =>
      cases rest with
      | nil =>
        simp only [Core.callResultTy, results] at resultSource
        have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp resultSource)
        dsimp only at shape
        rw [shape]
        exact checked.result_readable calleeRow (by rw [results]; simp)
      | cons _ _ => simp [Core.callResultTy, results, rej_ok] at resultSource
  | blockE body => exact source_block_refLike_readable body checked.exprEnv source reference
  | ifE condition thenBody elseBody =>
    simp only [Core.tyExpr] at source
    obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨thenType, _, thenSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨elseType, elseFinish, elseSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    by_cases equal : (thenType == elseType) = true
    · simp only [equal, ite_true] at source
      have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
      dsimp only at shape
      rw [shape] at reference ⊢
      exact source_block_refLike_readable thenBody checked.exprEnv thenSource reference
    · simp only [equal] at source
      change ((rej .type "the branches of `if` have different types" : Core.T Unit) >>=
        fun _ => pure thenType) elseFinish = .ok (type, finish) at source
      obtain ⟨_, _, rejected, _⟩ := (st_bind_ok _ _ _ _).mp source
      exact (rej_ok _ _ _ _).mp rejected |>.elim

theorem source_place_paramOk (place : Place)
    {env : Core.TEnv} (checked : SourceReadableEnvironment env) {info : PlaceInfo} {start finish : Nat}
    (source : Core.tyPlace env place start = .ok (info, finish)) : info.ty.paramOk = true := by
  cases place with
  | var index =>
    simp only [Core.tyPlace] at source
    obtain ⟨localVar, next, lookup, source⟩ := (st_bind_ok _ _ _ _).mp source
    have row := (varOf_ok _ _ _ _).mp lookup
    have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
    dsimp only at shape
    rw [shape]
    exact checked.variables index localVar row.2.1
  | global index =>
    by_cases available : index < env.globalLimit
    · cases row : env.mod.globals[index]? with
      | none => simp [Core.tyPlace, available, row, rej_ok] at source
      | some globalVar =>
        simp only [Core.tyPlace, available, row, ite_true] at source
        have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
        dsimp only at shape
        rw [shape]
        exact paramOk_of_storable (checked.global_storable row)
    · simp [Core.tyPlace, available, rej_ok] at source
  | deref expression =>
    cases special : Core.sliceRefTy env expression with
    | none =>
      obtain ⟨mutability, childFinish, childSource⟩ := tyPlace_deref_child special source
      have readable := source_expression_refLike_readable expression checked childSource rfl
      exact paramOk_refTarget readable
    | some specialType =>
      have reference := sliceRefTy_isRefSlice special
      simp only [Core.tyPlace, special] at source
      obtain ⟨actual, next, input, source⟩ := (st_bind_ok _ _ _ _).mp source
      have inputShape := congrArg Prod.fst ((st_pure_ok _ _ _).mp input)
      dsimp only at inputShape
      subst actual
      cases specialType with
      | ref mutability target =>
        have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
        dsimp only at shape
        rw [shape]
        cases target <;> simp_all [Ty.isRefSlice, Ty.paramOk, Ty.storable]
      | _ => simp [Ty.isRefSlice] at reference
  | elem view index origin =>
    obtain ⟨viewStart, viewFinish, indexFinish, writable, integer, viewSource, indexSource⟩ :=
      tyPlace_elem_children source
    exact flat_paramOk (source_view_element_flat view checked viewSource)
  | field owner index =>
    simp only [Core.tyPlace] at source
    obtain ⟨ownerInfo, ownerFinish, ownerSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨field, fieldFinish, fieldSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
    dsimp only at shape
    rw [shape]
    obtain ⟨id, fields, ownerShape, flat, row, _⟩ := structField_ok _ _ _ _ _ _ fieldSource
    exact flat_paramOk (tyList_flat_get fields (by simpa [ownerShape, Ty.flat] using flat) index field.ty row)

theorem source_view_element_flat (view : View)
    {env : Core.TEnv} (checked : SourceReadableEnvironment env) {element : Ty} {writable : Bool}
    {start finish : Nat}
    (source : Core.tyView env view start = .ok ((element, writable), finish)) : element.flat = true := by
  cases view with
  | of place =>
    simp only [Core.tyView] at source
    obtain ⟨info, next, placeSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    have allowed := source_place_paramOk place checked placeSource
    cases type : info.ty <;> simp only [type] at source
    all_goals try exact (rej_ok _ _ _ _).mp source |>.elim
    all_goals
      have shape := congrArg (fun pair => pair.1.1) ((st_pure_ok _ _ _).mp source)
      dsimp only at shape
      rw [shape]
      simpa only [type, Ty.paramOk, Ty.storable, Ty.isRefSlice, Bool.or_false] using allowed
  | val expression =>
    simp only [Core.tyView] at source
    obtain ⟨type, next, childSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    cases type with
    | slice mutability target =>
      have shape := congrArg (fun pair => pair.1.1) ((st_pure_ok _ _ _).mp source)
      dsimp only at shape
      rw [shape]
      exact source_expression_refLike_readable expression checked childSource rfl
    | _ => exact (rej_ok _ _ _ _).mp source |>.elim

theorem source_block_refLike_readable (body : Core.Block)
    {env : Core.TEnv} (checked : SourceReadableEnvironment env) {pre : List (VarId × Ty)}
    {type : Ty} {start finish : Nat}
    (source : Core.tyBlock env pre body start = .ok (type, finish))
    (reference : type.isRefLike = true) : type.readable = true := by
  cases body with
  | mk scope statements expression =>
    unfold Core.tyBlock at source
    by_cases nested : scope ∈ env.scopes
    · simp [nested, chk] at source
    · simp only [List.contains_iff_mem, nested, ite_false] at source
      obtain ⟨declared, declaredFinish, declaration, source⟩ := (st_bind_ok _ _ _ _).mp source
      obtain ⟨finalEnv, valueStart, statementsTyped, source⟩ := (st_bind_ok _ _ _ _).mp source
      have declarationTables := declarePre_tables pre declaration
      have declaredChecked := checked.tables declarationTables.1 declarationTables.2.1
      have finalTables := tyStmts_tables statements statementsTyped
      have finalChecked := declaredChecked.tables finalTables.1 finalTables.2.1
      cases expression with
      | none =>
        have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
        dsimp only at shape
        rw [shape] at reference
        cases reference
      | some expression => exact source_expression_refLike_readable expression finalChecked source reference

end

theorem source_passable_expression_readable (expression : Expr)
    {env : Core.TEnv} (checked : SourceReadableEnvironment env) {actual expected : Ty}
    {start finish : Nat} (source : Core.tyExpr env expression start = .ok (actual, finish))
    (passable : actual.passableTo expected = true) (reference : expected.isRefLike = true) :
    expected.readable = true := by
  apply source_passable_readable passable
  apply source_expression_refLike_readable expression checked source
  rw [source_passable_refLike_eq passable]
  exact reference

theorem source_expression_refLike_readable_of_implementation (expression : Expr)
    {env : Core.TEnv} {index : ImplId} {impl : Impl}
    (accepted : Core.validate env.mod = .ok ()) (lookup : env.mod.impls[index]? = some impl)
    (variables : env.vars = impl.vars) {type : Ty} {start finish : Nat}
    (source : Core.tyExpr env expression start = .ok (type, finish))
    (reference : type.isRefLike = true) : type.readable = true :=
  source_expression_refLike_readable expression
    (SourceReadableEnvironment.implementation accepted lookup variables) source reference

#print axioms source_expression_refLike_readable
#print axioms source_place_paramOk
#print axioms source_view_element_flat
#print axioms source_block_refLike_readable
#print axioms source_passable_expression_readable

end Goose.Lower.Validation
