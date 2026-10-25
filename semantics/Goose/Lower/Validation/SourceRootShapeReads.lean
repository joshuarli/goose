import Goose.Lower.Validation.SourceReadable

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound

structure SourceRootTables (source : TEnv) (replay : PEnv) : Prop where
  moduleEq : replay.mod = source.mod
  variablesEq : replay.impl.vars = source.vars

theorem SourceRootTables.exprEnv {source : TEnv} {replay : PEnv}
    (tables : SourceRootTables source replay) : SourceRootTables (Core.exprEnv source) replay :=
  ⟨tables.moduleEq, tables.variablesEq⟩

private theorem variable_place_type {env : TEnv} {index : VarId} {info : PlaceInfo}
    {start finish : Nat} (source : Core.tyPlace env (.var index) start = .ok (info, finish))
    {localVar : LocalVar} (row : env.vars[index]? = some localVar) : info.ty = localVar.ty := by
  simp only [Core.tyPlace] at source
  obtain ⟨found, next, lookup, source⟩ := (st_bind_ok _ _ _ _).mp source
  have foundRow := (varOf_ok _ _ _ _).mp lookup |>.2.1
  rw [row] at foundRow
  cases Option.some.inj foundRow
  have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
  dsimp only at shape
  rw [shape]

private theorem refSlice_deref_refLike {env : TEnv} {index : VarId} {info : PlaceInfo}
    {localVar : LocalVar} {start finish : Nat}
    (row : env.vars[index]? = some localVar) (reference : localVar.ty.isRefSlice = true)
    (source : Core.tyPlace env (.deref (.read (.var index))) start = .ok (info, finish)) :
    info.ty.isRefLike = true := by
  by_cases visible : index ∈ env.visible
  · have special : Core.sliceRefTy env (.read (.var index)) = some localVar.ty := by
      simp [Core.sliceRefTy, visible, row, reference]
    simp only [Core.tyPlace, special] at source
    obtain ⟨type, next, input, source⟩ := (st_bind_ok _ _ _ _).mp source
    have inputShape := congrArg Prod.fst ((st_pure_ok _ _ _).mp input)
    dsimp only at inputShape
    subst type
    cases typeShape : localVar.ty with
    | ref mutability target =>
      cases target <;> simp only [typeShape, Ty.isRefSlice] at reference
      all_goals try cases reference
      simp only [typeShape] at source
      have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
      dsimp only at shape
      rw [shape]
      rfl
    | _ => simp [typeShape, Ty.isRefSlice] at reference
  · simp [Core.tyPlace, Core.tyExpr, Core.sliceRefTy, Core.varOf, visible, chk, rej_ok] at source

theorem source_readRoots_nonref_empty {env : TEnv} {penv : PEnv}
    (tables : SourceRootTables env penv) {place : Place} {info : PlaceInfo} {start finish : Nat}
    (source : Core.tyPlace env place start = .ok (info, finish))
    (nonref : info.ty.isRefLike = false) {before after : RState} {roots : List RootRef}
    (replayed : Core.readRoots penv place before = .ok (roots, after)) : roots = [] := by
  have shape := (readRoots_ok penv place before (roots, after) replayed).2
  rcases shape with ⟨index, localVar, rfl, row, reference, _⟩ | ⟨index, rfl, reference, _⟩ | empty
  · rw [tables.variablesEq] at row
    have type := variable_place_type source row
    rw [type, reference] at nonref
    cases nonref
  · cases row : penv.impl.vars[index]? with
    | none => simp [PEnv.isRefSliceVar, row] at reference
    | some localVar =>
      have variableReference : localVar.ty.isRefSlice = true := by
        simpa only [PEnv.isRefSliceVar, row] using reference
      rw [tables.variablesEq] at row
      have actual := refSlice_deref_refLike row variableReference source
      rw [actual] at nonref
      cases nonref
  · exact empty.1

#print axioms source_readRoots_nonref_empty

end Goose.Lower.Validation
