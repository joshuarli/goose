import Goose.Lower.Validation.StorageSourceActions
import Goose.Lower.Validation.ExpressionTypingScalarOps

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

structure StorageSourceOutputs (env : Core.TEnv) (results : List Ty) : Prop where
  place : ∀ (place : Place) {info : PlaceInfo} {start finish : Nat},
    Core.tyPlace env place start = .ok (info, finish) →
    ∀ {before after : LS} {value : ValueId}, GeneratedBuilderState before →
    lowerPlace place (lowerEnv env.mod env.vars results) before = (value, after) →
    after.cur.isSome = true → ∃ mu, after.vals[value]? = some (some (.data (.ref mu info.ty)))
  view : ∀ (view : View) {element : Ty} {writable : Bool} {start finish : Nat},
    Core.tyView env view start = .ok ((element, writable), finish) →
    ∀ {before after : LS} {value : ValueId}, GeneratedBuilderState before →
    lowerView view (lowerEnv env.mod env.vars results) before = (value, after) →
    after.cur.isSome = true → ∃ mu, after.vals[value]? = some (some (.view mu element))
  writablePlace : ∀ (place : Place) {info : PlaceInfo} {start finish : Nat},
    Core.tyPlace env place start = .ok (info, finish) → info.referenceWritable env.mod.profile = true →
    ∀ {before after : LS} {value : ValueId}, GeneratedBuilderState before →
    lowerPlace place (lowerEnv env.mod env.vars results) before = (value, after) →
    after.cur.isSome = true → after.vals[value]? = some (some (.data (.ref .mutable info.ty)))

def StoragePlaceChild (env : Core.TEnv) (results : List Ty) (place : Place) : Prop :=
  ∀ {info : PlaceInfo} {start finish : Nat}, Core.tyPlace env place start = .ok (info, finish) →
    ∀ {before : LS}, GeneratedBuilderState before →
      StorageAt (lowerEnv env.mod env.vars results) before (lowerPlace place)

def StorageExprChild (env : Core.TEnv) (results : List Ty) (expr : Expr) : Prop :=
  ∀ {type : Ty} {start finish : Nat}, Core.tyExpr env expr start = .ok (type, finish) →
    ∀ {before : LS}, GeneratedBuilderState before →
      StorageAt (lowerEnv env.mod env.vars results) before (lowerExpr expr)

def StorageViewChild (env : Core.TEnv) (results : List Ty) (view : View) : Prop :=
  ∀ {element : Ty} {writable : Bool} {start finish : Nat},
    Core.tyView env view start = .ok ((element, writable), finish) →
    ∀ {before : LS}, GeneratedBuilderState before →
      StorageAt (lowerEnv env.mod env.vars results) before (lowerView view)

theorem readable_referenceWritable {info : PlaceInfo} (readable : info.ty.readable = true)
    (profile : ArtifactProfile) : info.referenceWritable profile = info.bindingWritable := by
  cases shape : info.ty <;> simp [PlaceInfo.referenceWritable, shape, Ty.readable, Ty.flat] at readable ⊢

theorem tyExpr_pop_storage_profile {env : Core.TEnv} {owner : Place} {origin : OriginId}
    {type : Ty} {start finish : Nat}
    (source : Core.tyExpr env (.pop owner origin) start = .ok (type, finish)) : env.mod.profile = .shrink := by
  simp only [Core.tyExpr] at source
  obtain ⟨_, _, required, _⟩ := (st_bind_ok _ _ _ _).mp source
  unfold requireShrink at required
  inv at required
  exact eq_of_beq required.1

theorem storage_read_source {env : Core.TEnv} {results : List Ty}
    (outputs : StorageSourceOutputs env results) {place : Place} {type : Ty} {start finish : Nat}
    (source : Core.tyExpr env (.read place) start = .ok (type, finish))
    (child : StoragePlaceChild env results place) {before : LS} (generated : GeneratedBuilderState before) :
    StorageAt (lowerEnv env.mod env.vars results) before (lowerExpr (.read place)) := by
  obtain ⟨info, next, placeSource, shape, readable⟩ := tyExpr_read_storage source
  change StorageAt _ _ (lowerPlace place >>= fun address => emitDef (.load address))
  apply (child placeSource generated).bind
  apply StorageAt.emitDef
  intro active value
  obtain ⟨mu, row⟩ := outputs.place place placeSource generated rfl active
  exact ⟨mu, info.ty, row, Or.inl readable⟩

theorem storage_pop_source {env : Core.TEnv} {results : List Ty}
    (outputs : StorageSourceOutputs env results) {owner : Place} {origin : OriginId} {type : Ty} {start finish : Nat}
    (source : Core.tyExpr env (.pop owner origin) start = .ok (type, finish))
    (child : StoragePlaceChild env results owner) {before : LS} (generated : GeneratedBuilderState before) :
    StorageAt (lowerEnv env.mod env.vars results) before (lowerExpr (.pop owner origin)) := by
  obtain ⟨info, ownerStart, ownerFinish, placeSource, element⟩ := tyExpr_pop_owner source
  change StorageAt _ _ (lowerPlace owner >>= fun address => emitDef (.pop address (some origin)))
  apply (child placeSource generated).bind
  apply StorageAt.emitDef
  intro active value
  obtain ⟨mu, row⟩ := outputs.place owner placeSource generated rfl active
  exact ⟨mu, info.ty, row, Or.inr ⟨tyExpr_pop_storage_profile source, by simp [element]⟩⟩

theorem storage_push_source {env : Core.TEnv} {results : List Ty}
    (outputs : StorageSourceOutputs env results) {owner : Place} {expr : Expr} {origin : Option OriginId}
    {type : Ty} {start finish : Nat}
    (source : Core.tyExpr env (.push owner expr origin) start = .ok (type, finish))
    (placeChild : StoragePlaceChild env results owner) (exprChild : StorageExprChild env results expr)
    {before : LS} (generated : GeneratedBuilderState before) :
    StorageAt (lowerEnv env.mod env.vars results) before (lowerExpr (.push owner expr origin)) := by
  obtain ⟨info, element, ownerStart, ownerFinish, childStart, childFinish,
    ownerSource, shape, childSource, _⟩ := tyExpr_push_children source
  let ownerValue := lowerPlace owner (lowerEnv env.mod env.vars results) before
  have ownerGenerated := generated.lowerPlace owner (show lowerPlace owner _ before = ownerValue from rfl)
  change StorageAt _ _ (lowerPlace owner >>= fun address => do
    let value ← lowerExpr expr
    emitDef (.push address value origin))
  apply (placeChild ownerSource generated).bind
  apply (exprChild childSource ownerGenerated).bind
  apply StorageAt.emitDef
  intro active result
  have ownerLive := (dead_lowerExpr expr).live_before rfl active
  obtain ⟨mu, row⟩ := outputs.place owner ownerSource generated rfl ownerLive
  exact ⟨mu, info.ty, types_lowerExpr expr _ ownerValue.2 _ _ rfl _ _ row, Or.inr (by simp [shape])⟩

#print axioms storage_read_source
#print axioms storage_push_source
#print axioms storage_pop_source

end Goose.Lower.Validation
