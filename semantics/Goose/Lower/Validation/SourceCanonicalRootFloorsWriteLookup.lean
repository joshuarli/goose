import Goose.Lower.Validation.SourceCanonicalRootFloorsWriteKeys

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core

theorem applySourceRootWrites_cons (entry : SourceRootWrite) (rest : List SourceRootWrite)
    (table : SourceRootTable) :
    applySourceRootWrites (entry :: rest) table = applySourceRootWrites rest
      (if entry.1 < table.size then table.set! entry.1 (some entry.2) else table) := rfl

theorem applySourceRootWrites_size (writes : List SourceRootWrite) (table : SourceRootTable) :
    (applySourceRootWrites writes table).size = table.size := by
  induction writes generalizing table with
  | nil => rfl
  | cons entry rest ih =>
    rw [applySourceRootWrites_cons, ih]
    split <;> simp

theorem applySourceRootWrites_outside (writes : List SourceRootWrite) (table : SourceRootTable)
    (index : Nat) (outside : index ∉ writes.map Prod.fst) :
    (applySourceRootWrites writes table)[index]? = table[index]? := by
  induction writes generalizing table with
  | nil => rfl
  | cons entry rest ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at outside
    rw [applySourceRootWrites_cons, ih _ outside.2]
    split <;> simp [Ne.symm outside.1]

theorem applySourceRootWrites_lookup (writes : List SourceRootWrite) (table : SourceRootTable)
    (entry : SourceRootWrite) (unique : (writes.map Prod.fst).Nodup)
    (member : entry ∈ writes) (bounded : entry.1 < table.size) :
    (applySourceRootWrites writes table)[entry.1]? = some (some entry.2) := by
  induction writes generalizing table with
  | nil => cases member
  | cons first rest ih =>
    simp only [List.map_cons, List.nodup_cons] at unique
    rcases List.mem_cons.mp member with same | member
    · subst first
      rw [applySourceRootWrites_cons, applySourceRootWrites_outside rest _ entry.1 unique.1]
      simp [bounded]
    · rw [applySourceRootWrites_cons]
      apply ih _ unique.2 member
      split <;> simpa using bounded

theorem sourceNodeRootTable_writes (env : PEnv) (node : DemandNode) :
    sourceNodeRootTable env node = applySourceRootWrites (sourceNodeRootWrites env node)
      (Array.replicate (sourceNodeScopeKeys node).length none) := by
  cases node <;>
    simp only [sourceNodeRootTable, sourceNodeRootWrites, sourceNodeScopeKeys,
      collectSourceExprRoots_writes, collectSourcePlaceRoots_writes,
      collectSourceViewRoots_writes, collectSourceBoundRoots_writes,
      collectSourceStmtRoots_writes, collectSourceBlockRoots_writes,
      scopeParents, Array.size_map, List.size_toArray, List.length_map]

def SourceRootScopeValid (node : DemandNode) : Prop :=
  (sourceNodeScopeKeys node).Nodup ∧
    ∀ scope ∈ sourceNodeScopeKeys node, scope < (sourceNodeScopeKeys node).length

theorem sourceRootScopeValid_block {module : Core.Module} {impl : Impl}
    (checked : checkImpl module impl = .ok ()) : SourceRootScopeValid (.block impl.body) := by
  have ordered := checkImpl_scopeOrder checked
  refine ⟨scopeOrder_keys_nodup ordered, ?_⟩
  intro scope member
  simpa [sourceNodeScopeKeys, scopeParents] using scopeOrder_key_bound ordered member

theorem sourceRootScopeValid_global {module : Core.Module} {index : GlobalId} {global : Core.Global}
    (checked : checkGlobal module index global = .ok ()) :
    SourceRootScopeValid (.expression global.init) := by
  have ordered := checkGlobal_scopeOrder checked
  refine ⟨scopeOrder_keys_nodup ordered, ?_⟩
  intro scope member
  simpa [sourceNodeScopeKeys, scopeParents] using scopeOrder_key_bound ordered member

theorem sourceNodeRootTable_write_lookup (env : PEnv) (node : DemandNode)
    (unique : (sourceNodeScopeKeys node).Nodup)
    (bounded : ∀ scope ∈ sourceNodeScopeKeys node, scope < (sourceNodeScopeKeys node).length)
    (entry : SourceRootWrite) (member : entry ∈ sourceNodeRootWrites env node) :
    (sourceNodeRootTable env node)[entry.1]? = some (some entry.2) := by
  rw [sourceNodeRootTable_writes]
  apply applySourceRootWrites_lookup _ _ entry (sourceNodeRootWrites_nodup env node unique) member
  simpa using bounded entry.1 (sourceNodeRootWrites_scope env node entry member)

end Goose.Lower.Validation.SourceCanonicalRootFloors
