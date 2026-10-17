import Goose.Lower.Validation.PermissionSourceInductionControlStatements
import Goose.Lower.Validation.PermissionInstructionControlWhile
import Goose.Lower.Validation.PermissionInstructionControlRangeStatement

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem permission_source_while {env : Core.TEnv} {func : Func} {results : List Ty}
    (scope : ScopeId) (condition : Expr) (body : Core.Block) (origin : OriginId)
    (conditionChild : PermissionStorageExprChild env func results condition)
    (bodyChild : ∀ env, PermissionSourceBlock env func results body) :
    PermissionSourceStatement env func results scope (.while condition body origin) := by
  intro tables output start finish source first loop before after result generated frames floor run
  obtain ⟨conditionFinish,bodyType,conditionSource,bodySource,_⟩ := tyStmt_while_children source
  apply lowerStmt_while_newPermissionInstructions run floor generated frames
  · intro input output value lowered generated frames floor
    exact (conditionChild conditionSource generated lowered).weaken floor
  · intro header depth exit input output value lowered generated frames floor
    exact bodyChild {env with loops := env.loops + 1} (tables.retained rfl rfl) bodySource
      generated frames floor (by intro entry member; cases member) lowered

theorem permission_source_forRange {env : Core.TEnv} {func : Func} {results : List Ty}
    (scope : ScopeId) (slot : VarId) (lo hi : Expr) (body : Core.Block) (origin : OriginId)
    (lowChild : PermissionStorageExprChild env func results lo)
    (highChild : PermissionStorageExprChild env func results hi)
    (bodyChild : ∀ env, PermissionSourceBlock env func results body) :
    PermissionSourceStatement env func results scope (.forRange slot lo hi body origin) := by
  intro tables output start finish source first loop before after result generated frames floor run
  obtain ⟨localVar,integer,lowerStart,lowerFinish,upperFinish,bodyType,
    declared,lowSource,highSource,binderType,bodySource,_⟩ := tyStmt_forRange_children source
  apply forRange_newPermissionInstructions generated floor
  · intro input value output generated floor lowered
    exact (lowChild lowSource generated lowered).weaken floor
  · intro input value output generated floor lowered
    exact (highChild highSource generated lowered).weaken floor
  · intro hint header counter depth exit input value output generated live frames floor lowered
    have transfer : ∀ entry ∈ [(slot,counter,origin)], ∀ descriptor,
        func.slots[entry.1]? = some descriptor → PermissionTransfer (lower env.mod).profile
          (FreshWritableEvidence (lowerEnv env.mod env.vars results) first input)
          (FreshContentsEvidence (lowerEnv env.mod env.vars results) first input) entry.2.1 descriptor.ty := by
      intro entry member descriptor row
      cases List.mem_singleton.mp member
      have localAt := (declare_ok _ _ _ _ _ declared).2.1
      have slotAt : (lowerEnv env.mod env.vars results).slots[slot]? =
          some ⟨localVar.ty,localVar.kind,localVar.scope,slot⟩ := by
        simp [lowerEnv,Array.getElem?_mapIdx,localAt]
      rw [tables.slots,slotAt] at row
      cases Option.some.inj row
      simp only [binderType,PermissionTransfer]
    exact bodyChild {env with loops := env.loops + 1,visible := slot :: env.visible}
      (tables.retained rfl rfl) bodySource generated frames floor transfer lowered
  · exact run

#print axioms permission_source_while
#print axioms permission_source_forRange

end Goose.Lower.Validation
