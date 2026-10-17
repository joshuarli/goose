import Goose.Lower.Validation.ValueTypes
import Goose.Lower.Validation.InterfaceTypes
import Goose.Lower.Validation.ExpressionTypingBorrowOps

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

def referenceType (info : PlaceInfo) (profile : ArtifactProfile) : VTy :=
  .data (.ref (if info.referenceWritable profile then .mutable else .readOnly) info.ty)

theorem lowerPlace_var_exact {env : Core.TEnv} {varId : VarId} {info : PlaceInfo}
    {start finish : Nat} (source : Core.tyPlace env (.var varId) start = .ok (info, finish))
    (results : List Ty) (before : LS) {block : BlockId} (live : before.cur = some block) :
    let (value, after) := lowerPlace (.var varId) (lowerEnv env.mod env.vars results) before
    after.cur = before.cur ∧ after.vals[value]? = some (some (referenceType info env.mod.profile)) := by
  simp only [Core.tyPlace] at source
  obtain ⟨localVar, next, lookup, shape⟩ := (st_bind_ok _ _ _ _).mp source
  have row := (varOf_ok _ _ _ _).mp lookup
  have pair := (st_pure_ok _ _ _).mp shape
  have equality : info = ⟨localVar.ty, localVar.kind == .mutable, true⟩ := congrArg Prod.fst pair
  subst info
  have slotRow : (lowerEnv env.mod env.vars results).slots[varId]? =
      some ⟨localVar.ty, localVar.kind, localVar.scope, varId⟩ := by
    simp [lowerEnv, Array.getElem?_mapIdx, row.2.1]
  have address : (Op.slotAddr varId).resultTy (tyEnv (lowerEnv env.mod env.vars results) before) =
      .ok (referenceType ⟨localVar.ty, localVar.kind == .mutable, true⟩ env.mod.profile) := by
    simp only [Op.resultTy, tyEnv, slotRow, referenceType]
    dsimp only [lowerEnv]
    cases localVar.ty <;> cases localVar.kind <;> cases env.mod.profile <;> rfl
  have emitted := emitDef_recorded live address
  exact ⟨emitted.2.1, emitted.2.2.1⟩

theorem lowerPlace_global_exact {env : Core.TEnv} {global : GlobalId} {info : PlaceInfo}
    {start finish : Nat} (source : Core.tyPlace env (.global global) start = .ok (info, finish))
    (vars : Array LocalVar) (results : List Ty) (before : LS)
    {block : BlockId} (live : before.cur = some block) :
    let (value, after) := lowerPlace (.global global) (lowerEnv env.mod vars results) before
    after.cur = before.cur ∧ after.vals[value]? = some (some (referenceType info env.mod.profile)) := by
  by_cases available : global < env.globalLimit
  · cases globalRow : env.mod.globals[global]? with
    | none =>
      simp only [Core.tyPlace, available, globalRow, ite_true] at source
      change Except.error _ = Except.ok _ at source
      cases source
    | some globalVar =>
      simp only [Core.tyPlace, available, globalRow, ite_true] at source
      have pair := (st_pure_ok _ _ _).mp source
      have equality : info = ⟨globalVar.ty, globalVar.kind == .mutable, true⟩ := congrArg Prod.fst pair
      subst info
      have address : (Op.globalAddr global).resultTy (tyEnv (lowerEnv env.mod vars results) before) =
          .ok (referenceType ⟨globalVar.ty, globalVar.kind == .mutable, true⟩ env.mod.profile) := by
        simp only [Op.resultTy, tyEnv, lowerEnv, Array.getElem?_map, globalRow,
          Option.map_some, referenceType]
        cases globalVar.ty <;> cases globalVar.kind <;> cases env.mod.profile <;> rfl
      have emitted := emitDef_recorded live address
      exact ⟨emitted.2.1, emitted.2.2.1⟩
  · simp only [Core.tyPlace, available, ite_false] at source
    change Except.error _ = Except.ok _ at source
    cases source

theorem tyExpr_ref_place {env : Core.TEnv} {place : Place} {mu : Mutability} {ty : Ty}
    {start finish : Nat} (source : Core.tyExpr env (.ref mu place) start = .ok (ty, finish)) :
    ∃ info next, Core.tyPlace env place start = .ok (info, next) ∧ ty = .ref mu info.ty ∧
      (if info.referenceWritable env.mod.profile then Mutability.mutable else .readOnly).atLeast mu = true := by
  simp only [Core.tyExpr] at source
  obtain ⟨info, next, placeTyped, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, mid, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  have target : info.ty.refTarget = true := by
    by_cases target : info.ty.refTarget = true
    · exact target
    · simp [target, chk] at source
  simp only [target, ite_true] at source
  cases mu with
  | readOnly =>
    have pair : (ty, finish) = (.ref .readOnly info.ty, mid) := by
      simpa [chk] using source
    refine ⟨info, next, placeTyped, congrArg Prod.fst pair, ?_⟩
    cases info.referenceWritable env.mod.profile <;> rfl
  | mutable =>
    have writeBind : (requireWrite "a mutable reference" (info.referenceWritable env.mod.profile) >>=
        fun _ => pure (.ref .mutable info.ty)) mid = .ok (ty, finish) := by
      simpa [Functor.map, StateT.map] using source
    obtain ⟨writeResult, afterWrite, writable, result⟩ := (st_bind_ok _ _ _ _).mp writeBind
    have permission := (requireWrite_ok _ _ _ _).mp writable
    have pair := (st_pure_ok _ _ _).mp result
    refine ⟨info, next, placeTyped, congrArg Prod.fst pair, ?_⟩
    simp [permission.1, Mutability.atLeast]

theorem lowerExpr_ref_var_exact {env : Core.TEnv} {varId : VarId} {mu : Mutability} {ty : Ty}
    {start finish : Nat} (source : Core.tyExpr env (.ref mu (.var varId)) start = .ok (ty, finish))
    (results : List Ty) (before : LS) {block : BlockId} (live : before.cur = some block) :
    let (value, after) := lowerExpr (.ref mu (.var varId)) (lowerEnv env.mod env.vars results) before
    after.cur = before.cur ∧ after.vals[value]? = some (some (.data ty)) := by
  obtain ⟨info, next, placeTyped, shape, permission⟩ := tyExpr_ref_place source
  subst ty
  cases placeRun : lowerPlace (.var varId) (lowerEnv env.mod env.vars results) before with
  | mk value mid =>
    have place := lowerPlace_var_exact placeTyped results before live
    rw [placeRun] at place
    dsimp only at place
    have midLive : mid.cur = some block := place.1.trans live
    have frozen := borrowTo_typed (le := lowerEnv env.mod env.vars results) (by simpa only [referenceType] using place.2) permission midLive
    simpa only [lowerExpr, bind_run, placeRun, place.1] using frozen

theorem lowerExpr_ref_global_exact {env : Core.TEnv} {global : GlobalId} {mu : Mutability} {ty : Ty}
    {start finish : Nat} (source : Core.tyExpr env (.ref mu (.global global)) start = .ok (ty, finish))
    (vars : Array LocalVar) (results : List Ty) (before : LS)
    {block : BlockId} (live : before.cur = some block) :
    let (value, after) := lowerExpr (.ref mu (.global global)) (lowerEnv env.mod vars results) before
    after.cur = before.cur ∧ after.vals[value]? = some (some (.data ty)) := by
  obtain ⟨info, next, placeTyped, shape, permission⟩ := tyExpr_ref_place source
  subst ty
  cases placeRun : lowerPlace (.global global) (lowerEnv env.mod vars results) before with
  | mk value mid =>
    have place := lowerPlace_global_exact placeTyped vars results before live
    rw [placeRun] at place
    dsimp only at place
    have midLive : mid.cur = some block := place.1.trans live
    have frozen := borrowTo_typed (le := lowerEnv env.mod vars results) (by simpa only [referenceType] using place.2) permission midLive
    simpa only [lowerExpr, bind_run, placeRun, place.1] using frozen

theorem tyExpr_read_place {env : Core.TEnv} {place : Place} {ty : Ty} {start finish : Nat}
    (source : Core.tyExpr env (.read place) start = .ok (ty, finish)) :
    ∃ info next, Core.tyPlace env place start = .ok (info, next) ∧ ty = info.ty := by
  simp only [Core.tyExpr] at source
  obtain ⟨info, next, placeTyped, source⟩ := (st_bind_ok _ _ _ _).mp source
  by_cases readable : info.ty.readable = true
  · simp only [readable, ite_true] at source
    have pair := (st_pure_ok _ _ _).mp source
    exact ⟨info, next, placeTyped, congrArg Prod.fst pair⟩
  · simp [readable, chk] at source

theorem lowerExpr_read_var_exact {env : Core.TEnv} {varId : VarId} {ty : Ty}
    {start finish : Nat} (source : Core.tyExpr env (.read (.var varId)) start = .ok (ty, finish))
    (results : List Ty) (before : LS) {block : BlockId} (live : before.cur = some block) :
    let (value, after) := lowerExpr (.read (.var varId)) (lowerEnv env.mod env.vars results) before
    after.cur = before.cur ∧ after.vals[value]? = some (some (.data ty)) := by
  obtain ⟨info, next, placeTyped, shape⟩ := tyExpr_read_place source
  subst ty
  cases placeRun : lowerPlace (.var varId) (lowerEnv env.mod env.vars results) before with
  | mk value mid =>
    have place := lowerPlace_var_exact placeTyped results before live
    rw [placeRun] at place
    dsimp only at place
    have loaded := lowerExpr_read_typed_of_place placeRun
      (by simpa only [referenceType] using place.2) (place.1.trans live)
    simpa only [place.1] using loaded

theorem lowerExpr_read_global_exact {env : Core.TEnv} {global : GlobalId} {ty : Ty}
    {start finish : Nat} (source : Core.tyExpr env (.read (.global global)) start = .ok (ty, finish))
    (vars : Array LocalVar) (results : List Ty) (before : LS)
    {block : BlockId} (live : before.cur = some block) :
    let (value, after) := lowerExpr (.read (.global global)) (lowerEnv env.mod vars results) before
    after.cur = before.cur ∧ after.vals[value]? = some (some (.data ty)) := by
  obtain ⟨info, next, placeTyped, shape⟩ := tyExpr_read_place source
  subst ty
  cases placeRun : lowerPlace (.global global) (lowerEnv env.mod vars results) before with
  | mk value mid =>
    have place := lowerPlace_global_exact placeTyped vars results before live
    rw [placeRun] at place
    dsimp only at place
    have loaded := lowerExpr_read_typed_of_place placeRun
      (by simpa only [referenceType] using place.2) (place.1.trans live)
    simpa only [place.1] using loaded

end Goose.Lower.Validation
