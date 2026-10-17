import Goose.Lower.Validation.PermissionSourceInductionCollections
import Goose.Lower.Validation.PermissionPreservationSourceTables

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def PermissionSourceStatement (env : Core.TEnv) (func : Func) (results : List Ty)
    (scope : ScopeId) (stmt : Stmt) : Prop :=
  PermissionSourceTables env results func →
    ∀ {output : Core.TEnv} {start finish : Nat}, Core.tyStmt env scope stmt start = .ok (output, finish) →
      ∀ {first : Nat} {loop : Option LoopCtx} {before after : LS} {result : Unit},
        GeneratedBuilderState before → LoopBuilderFrames loop before → first ≤ before.vals.size →
        lowerStmt loop stmt (lowerEnv env.mod env.vars results) before = (result, after) →
        NewPermissionInstructions (lower env.mod) func (lowerEnv env.mod env.vars results) first before after

def PermissionSourceBlock (env : Core.TEnv) (func : Func) (results : List Ty) (body : Core.Block) : Prop :=
  PermissionSourceTables env results func →
    ∀ {sourcePre : List (VarId × Ty)} {type : Ty} {start finish : Nat},
      Core.tyBlock env sourcePre body start = .ok (type, finish) →
      ∀ {first : Nat} {loop : Option LoopCtx} {pre : List (SlotId × ValueId × OriginId)} {want : Bool}
        {before after : LS} {result : ValueId},
        GeneratedBuilderState before → LoopBuilderFrames loop before → first ≤ before.vals.size →
        (∀ entry ∈ pre, ∀ descriptor, func.slots[entry.1]? = some descriptor →
          PermissionTransfer (lower env.mod).profile
            (FreshWritableEvidence (lowerEnv env.mod env.vars results) first before)
            (FreshContentsEvidence (lowerEnv env.mod env.vars results) first before) entry.2.1 descriptor.ty) →
        lowerBlock loop pre want body (lowerEnv env.mod env.vars results) before = (result, after) →
        NewPermissionInstructions (lower env.mod) func (lowerEnv env.mod env.vars results) first before after

end Goose.Lower.Validation
