import Goose.Lower.Validation.SourceEnvironment
import Goose.Lower.Validation.BuilderTyping

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem flat_referenceWritable {info : PlaceInfo} (flat : info.ty.flat = true)
    (profile : ArtifactProfile) : info.referenceWritable profile = info.bindingWritable := by
  cases ty : info.ty <;> simp [PlaceInfo.referenceWritable, ty, Ty.flat] at flat ⊢

theorem structDef_profile {env : Core.TEnv} {ty : Ty} {descriptor : StructDef}
    {start finish : Nat} (typed : Core.structDef env ty start = .ok (descriptor, finish)) :
    env.mod.profile = .shrink := by
  by_cases profile : env.mod.profile = .shrink
  · exact profile
  · simp [Core.structDef, profile, chk] at typed

theorem tyPlace_field_profile {env : Core.TEnv} {owner : Place} {index : Nat}
    {info : PlaceInfo} {start finish : Nat}
    (typed : Core.tyPlace env (.field owner index) start = .ok (info, finish)) :
    env.mod.profile = .shrink := by
  simp only [Core.tyPlace] at typed
  obtain ⟨_, _, _, typed⟩ := (st_bind_ok _ _ _ _).mp typed
  obtain ⟨_, _, field, _⟩ := (st_bind_ok _ _ _ _).mp typed
  simp only [Core.structField] at field
  obtain ⟨_, _, definition, _⟩ := (st_bind_ok _ _ _ _).mp field
  exact structDef_profile definition

theorem tyExpr_structLit_profile {env : Core.TEnv} {ty result : Ty} {exprs : List Expr}
    {start finish : Nat} (typed : Core.tyExpr env (.structLit ty exprs) start = .ok (result, finish)) :
    env.mod.profile = .shrink := by
  simp only [Core.tyExpr] at typed
  obtain ⟨_, _, definition, _⟩ := (st_bind_ok _ _ _ _).mp typed
  exact structDef_profile definition

theorem structField_descriptor {env : Core.TEnv} {ty : Ty} {index start finish : Nat}
    {field : StructField} (typed : Core.structField env ty index start = .ok (field, finish)) :
    ∃ id fields descriptor, ty = .structT id fields ∧ env.mod.structs[id]? = some descriptor ∧
      fields = TyList.ofList (descriptor.fields.toList.map (·.ty)) ∧ descriptor.fields[index]? = some field := by
  simp only [Core.structField] at typed
  obtain ⟨descriptor, next, definition, fieldTyped⟩ := (st_bind_ok _ _ _ _).mp typed
  obtain ⟨id, fields, shape, _, nominal, lookup, _⟩ := structDef_ok _ _ _ _ _ definition
  cases row : descriptor.fields[index]? with
  | none => simp [row, chk] at fieldTyped
  | some found =>
    simp only [row] at fieldTyped
    have pair := (st_pure_ok _ _ _).mp fieldTyped
    have same : field = found := congrArg Prod.fst pair
    subst found
    simp only [Core.Module.structType?, lookup, Option.map_some, shape,
      Option.some.injEq, Ty.structT.injEq] at nominal
    exact ⟨id, fields, descriptor, shape, lookup, nominal.2.symm, row⟩

theorem lowerPlace_field_typed_of_owner {env : Core.TEnv} {owner : Place} {index : Nat}
    {ownerInfo info : PlaceInfo} {start ownerFinish finish : Nat}
    (ownerSource : Core.tyPlace env owner start = .ok (ownerInfo, ownerFinish))
    (source : Core.tyPlace env (.field owner index) start = .ok (info, finish))
    {vars : Array LocalVar} {results : List Ty} {before mid : LS} {value : ValueId}
    {mu : Mutability} {block : BlockId}
    (ownerRun : lowerPlace owner (lowerEnv env.mod vars results) before = (value, mid))
    (ownerTyped : mid.vals[value]? = some (some (.data (.ref mu ownerInfo.ty))))
    (live : mid.cur = some block) :
    let (result, after) := lowerPlace (.field owner index) (lowerEnv env.mod vars results) before
    ∃ resultMu, after.cur = mid.cur ∧ after.vals[result]? = some (some (.data (.ref resultMu info.ty))) := by
  simp only [Core.tyPlace] at source
  obtain ⟨sourceOwner, next, child, source⟩ := (st_bind_ok _ _ _ _).mp source
  rw [ownerSource] at child
  cases Except.ok.inj child
  obtain ⟨field, fieldFinish, fieldTyped, source⟩ := (st_bind_ok _ _ _ _).mp source
  have pair := (st_pure_ok _ _ _).mp source
  have referent : info.ty = field.ty := congrArg (fun pair => pair.1.ty) pair
  obtain ⟨id, fields, descriptor, shape, descriptorLookup, nominal, fieldLookup⟩ :=
    structField_descriptor fieldTyped
  have operation : (Op.fieldAddr value index).resultTy (tyEnv (lowerEnv env.mod vars results) mid) =
      .ok (.data (.ref (Mutability.ofKind field.binding) info.ty)) := by
    simp [Op.resultTy, TyEnv.refTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, lowerEnv,
      ownerTyped, shape, descriptorLookup, nominal, fieldLookup, referent,
      pure, Except.pure, bind, Except.bind]
  simp only [lowerPlace, bind_run, ownerRun]
  have emitted := emitDef_recorded live operation
  exact ⟨_, emitted.2.1, emitted.2.2.1⟩

theorem lowerPlace_field_variable_exact {env : Core.TEnv} {varId : VarId} {index : Nat}
    {info : PlaceInfo} {start finish : Nat}
    (source : Core.tyPlace env (.field (.var varId) index) start = .ok (info, finish))
    (results : List Ty) (before : LS) {block : BlockId} (live : before.cur = some block) :
    let (value, after) := lowerPlace (.field (.var varId) index) (lowerEnv env.mod env.vars results) before
    ∃ mu, after.cur = before.cur ∧ after.vals[value]? = some (some (.data (.ref mu info.ty))) := by
  have children := source
  simp only [Core.tyPlace] at children
  obtain ⟨ownerInfo, ownerFinish, ownerSource, _⟩ := (st_bind_ok _ _ _ _).mp children
  cases ownerRun : lowerPlace (.var varId) (lowerEnv env.mod env.vars results) before with
  | mk ownerValue middle =>
    have owner := lowerPlace_var_exact ownerSource results before live
    rw [ownerRun] at owner
    dsimp only at owner
    have field := lowerPlace_field_typed_of_owner (env := env) (owner := .var varId) (start := start) ownerSource source ownerRun
      (by simpa only [referenceType] using owner.2) (owner.1.trans live)
    simpa only [owner.1] using field

theorem lowerPlace_field_global_exact {env : Core.TEnv} {global : GlobalId} {index : Nat}
    {info : PlaceInfo} {start finish : Nat}
    (source : Core.tyPlace env (.field (.global global) index) start = .ok (info, finish))
    (vars : Array LocalVar) (results : List Ty) (before : LS)
    {block : BlockId} (live : before.cur = some block) :
    let (value, after) := lowerPlace (.field (.global global) index) (lowerEnv env.mod vars results) before
    ∃ mu, after.cur = before.cur ∧ after.vals[value]? = some (some (.data (.ref mu info.ty))) := by
  have children := source
  simp only [Core.tyPlace] at children
  obtain ⟨ownerInfo, ownerFinish, ownerSource, _⟩ := (st_bind_ok _ _ _ _).mp children
  cases ownerRun : lowerPlace (.global global) (lowerEnv env.mod vars results) before with
  | mk ownerValue middle =>
    have owner := lowerPlace_global_exact ownerSource vars results before live
    rw [ownerRun] at owner
    dsimp only at owner
    have field := lowerPlace_field_typed_of_owner (env := env) (owner := .global global) (start := start) ownerSource source ownerRun
      (by simpa only [referenceType] using owner.2) (owner.1.trans live)
    simpa only [owner.1] using field

end Goose.Lower.Validation
