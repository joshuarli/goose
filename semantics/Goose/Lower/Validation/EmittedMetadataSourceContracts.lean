import Goose.Lower.Validation.EmittedMetadataBuilder
import Goose.Lower.Validation.EmittedTypingLoops
import Goose.Lower.GeneratedBuilder

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def EmittedMetadataResultTypes (env : Core.TEnv) (results : List Ty) : Prop :=
  ∀ impl, env.impl = some impl → impl.results.toList = results

def EmittedPreTyped (le : LEnv) (state : LS) (pre : List (SlotId × ValueId × OriginId)) : Prop :=
  ∀ slot value origin, (slot, value, origin) ∈ pre →
    ∃ descriptor, le.slots[slot]? = some descriptor ∧ state.vals[value]? = some (some (.data descriptor.ty))

theorem EmittedPreTyped.retained {le : LEnv} {before after : LS} {pre : List (SlotId × ValueId × OriginId)}
    (typed : EmittedPreTyped le before pre) (preserved : TypePrefix before after) :
    EmittedPreTyped le after pre := by
  intro slot value origin member
  obtain ⟨descriptor, slotAt, valueAt⟩ := typed slot value origin member
  exact ⟨descriptor, slotAt, preserved _ _ valueAt⟩

def EmittedMetadataRun (le : LEnv) (loop : Option LoopCtx) (action : B α) : Prop :=
  ∀ before result after, GeneratedBuilderState before → LoopBuilderTargets loop before →
    EmittedLoopTypes loop before → action le before = (result, after) →
    EmittedMetadata le before → EmittedMetadata le after

def EmittedMetadataSourceExpression (env : Core.TEnv) (results : List Ty) (expr : Expr) : Prop :=
  EmittedMetadataResultTypes env results →
  ∀ {type : Ty} {start finish : Nat}, Core.tyExpr env expr start = .ok (type, finish) →
    EmittedMetadataRun (lowerEnv env.mod env.vars results) none (lowerExpr expr)

def EmittedMetadataSourcePlace (env : Core.TEnv) (results : List Ty) (place : Place) : Prop :=
  EmittedMetadataResultTypes env results →
  ∀ {info : PlaceInfo} {start finish : Nat}, Core.tyPlace env place start = .ok (info, finish) →
    EmittedMetadataRun (lowerEnv env.mod env.vars results) none (lowerPlace place)

def EmittedMetadataSourceView (env : Core.TEnv) (results : List Ty) (view : View) : Prop :=
  EmittedMetadataResultTypes env results →
  ∀ {element : Ty} {writable : Bool} {start finish : Nat},
    Core.tyView env view start = .ok ((element, writable), finish) →
    EmittedMetadataRun (lowerEnv env.mod env.vars results) none (lowerView view)

def EmittedMetadataSourceStatement (env : Core.TEnv) (results : List Ty) (scope : ScopeId) (stmt : Stmt) : Prop :=
  EmittedMetadataResultTypes env results →
  ∀ {output : Core.TEnv} {start finish : Nat}, Core.tyStmt env scope stmt start = .ok (output, finish) →
    ∀ loop, EmittedMetadataRun (lowerEnv env.mod env.vars results) loop (lowerStmt loop stmt)

def EmittedMetadataSourceBlock (env : Core.TEnv) (results : List Ty) (body : Core.Block) : Prop :=
  EmittedMetadataResultTypes env results →
  ∀ {sourcePre : List (VarId × Ty)} {type : Ty} {start finish : Nat},
    Core.tyBlock env sourcePre body start = .ok (type, finish) →
    ∀ loop pre want before result after, GeneratedBuilderState before → LoopBuilderTargets loop before →
      EmittedLoopTypes loop before → EmittedPreTyped (lowerEnv env.mod env.vars results) before pre →
      lowerBlock loop pre want body (lowerEnv env.mod env.vars results) before = (result, after) →
      EmittedMetadata (lowerEnv env.mod env.vars results) before →
      EmittedMetadata (lowerEnv env.mod env.vars results) after

end Goose.Lower.Validation
