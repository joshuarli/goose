import Goose.Lower.Validation.SourceStatementTyping
import Goose.Lower.Validation.SourceEnvironment

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

def StorageWalkVisible (env : Core.TEnv) (stack : List ScopeId) : Prop :=
  ∀ index localVar, index ∈ env.visible → env.vars[index]? = some localVar → localVar.scope ∈ stack

theorem StorageWalkVisible.mono {env : Core.TEnv} {before after : List ScopeId}
    (visible : StorageWalkVisible env before) (subset : ∀ scope ∈ before, scope ∈ after) :
    StorageWalkVisible env after := by
  intro index localVar member row
  exact subset _ (visible index localVar member row)

theorem StorageWalkVisible.retained {env after : Core.TEnv} {stack : List ScopeId}
    (visible : StorageWalkVisible env stack) (variables : after.vars = env.vars)
    (members : ∀ index ∈ after.visible, index ∈ env.visible) : StorageWalkVisible after stack := by
  intro index localVar member row
  rw [variables] at row
  exact visible index localVar (members index member) row

theorem StorageWalkVisible.add {env : Core.TEnv} {stack : List ScopeId} {index : VarId}
    (visible : StorageWalkVisible env stack)
    (active : ∀ localVar, env.vars[index]? = some localVar → localVar.scope ∈ stack) :
    StorageWalkVisible {env with visible := index :: env.visible} stack := by
  intro found localVar member row
  rcases List.mem_cons.mp member with same | member
  · subst found
    exact active localVar row
  · exact visible found localVar member row

theorem StorageWalkVisible.varOf {env : Core.TEnv} {stack : List ScopeId}
    (visible : StorageWalkVisible env stack) {index : VarId} {localVar : LocalVar} {start finish : Nat}
    (source : Core.varOf env index start = .ok (localVar, finish)) : localVar.scope ∈ stack := by
  have facts := (varOf_ok _ _ _ _).mp source
  exact visible index localVar facts.1 facts.2.1

theorem StorageWalkVisible.declare {env : Core.TEnv} {stack : List ScopeId}
    (visible : StorageWalkVisible env stack) {index : VarId} {localVar : LocalVar} {scope start finish : Nat}
    (active : scope ∈ stack) (source : Core.declare env index scope start = .ok (localVar, finish)) :
    StorageWalkVisible {env with visible := index :: env.visible} stack := by
  have facts := declare_ok _ _ _ _ _ source
  apply visible.add
  intro actual row
  have same : actual = localVar := Option.some.inj (row.symm.trans facts.2.1)
  subst actual
  have declaredScope : localVar.scope = scope := facts.2.2.1
  rw [declaredScope]
  exact active

theorem StorageWalkVisible.declarePre {env after : Core.TEnv} {stack : List ScopeId}
    (visible : StorageWalkVisible env stack) {pre : List (VarId × Ty)} {scope start finish : Nat}
    (active : scope ∈ stack) (source : Core.declarePre env scope pre start = .ok (after, finish)) :
    StorageWalkVisible after stack := by
  induction pre generalizing env start with
  | nil =>
    obtain ⟨rfl, rfl⟩ := (st_pure_ok _ _ _).mp source
    exact visible
  | cons binding rest ih =>
    obtain ⟨index, type⟩ := binding
    obtain ⟨localVar, next, declared, sameType, remaining⟩ := declarePre_cons_children source
    exact ih (visible.declare active declared) remaining

theorem StorageWalkVisible.tyStmt {env after : Core.TEnv} {stack : List ScopeId}
    (visible : StorageWalkVisible env stack) {stmt : Stmt} {scope start finish : Nat}
    (active : scope ∈ stack) (source : Core.tyStmt env scope stmt start = .ok (after, finish)) :
    StorageWalkVisible after stack := by
  cases stmt
  case letS index expr origin =>
    obtain ⟨localVar, type, next, declared, child, passing, rfl⟩ := tyStmt_let_children source
    exact visible.declare active declared
  case' resize owner count fill origin => cases fill
  case' ifS condition yes no origin => cases no
  case' ret value origin => cases value
  all_goals
    have tables := tyStmt_tables _ source
    apply visible.retained tables.2.1
    intro index member
    simp only [Core.tyStmt] at source
    repeat' first
    | (subst after; exact member)
    | contradiction
    | (simp only [chk, false_and, and_false, exists_false, exists_const, or_false, false_or,
        true_and, Prod.mk.injEq, Prod.exists, and_assoc, exists_eq_left, exists_and_left] at source)
    | (guard_hyp source : _ ∧ _; obtain ⟨fact, source⟩ := source)
    | (guard_hyp source : ∃ _, _; obtain ⟨value, source⟩ := source)
    | (guard_hyp source : _ ∨ _; rcases source with source | source)
    | (split at source)

theorem StorageWalkVisible.tyStmts {env after : Core.TEnv} {stack : List ScopeId}
    (visible : StorageWalkVisible env stack) {stmts : List Stmt} {scope start finish : Nat}
    (active : scope ∈ stack) (source : Core.tyStmts env scope stmts start = .ok (after, finish)) :
    StorageWalkVisible after stack := by
  induction stmts generalizing env start with
  | nil =>
    obtain ⟨rfl, rfl⟩ := (st_pure_ok _ _ _).mp source
    exact visible
  | cons stmt rest ih =>
    obtain ⟨middle, next, head, tail⟩ := tyStmts_cons_children source
    exact ih (visible.tyStmt active head) tail

theorem storageWalk_visible_slot {env : Core.TEnv} {stack : List ScopeId}
    (visible : StorageWalkVisible env stack) {index : VarId} (member : index ∈ env.visible)
    (results : List Ty) {descriptor : Slot}
    (row : (lowerEnv env.mod env.vars results).slots[index]? = some descriptor) : descriptor.scope ∈ stack := by
  cases localAt : env.vars[index]? with
  | none => simp [lowerEnv, Array.getElem?_mapIdx, localAt] at row
  | some localVar =>
    have descriptorEq : (⟨localVar.ty, localVar.kind, localVar.scope, index⟩ : Slot) = descriptor := by
      simpa [lowerEnv, Array.getElem?_mapIdx, localAt] using row
    rw [← descriptorEq]
    exact visible index localVar member localAt

theorem storageWalk_declared_slot {env : Core.TEnv} {stack : List ScopeId}
    {index : VarId} {localVar : LocalVar} {scope start finish : Nat} (active : scope ∈ stack)
    (source : Core.declare env index scope start = .ok (localVar, finish)) (results : List Ty)
    {descriptor : Slot} (row : (lowerEnv env.mod env.vars results).slots[index]? = some descriptor) :
    descriptor.scope ∈ stack := by
  have facts := declare_ok _ _ _ _ _ source
  have localAt : env.vars[index]? = some localVar := facts.2.1
  have descriptorEq : (⟨localVar.ty, localVar.kind, localVar.scope, index⟩ : Slot) = descriptor := by
    simpa [lowerEnv, Array.getElem?_mapIdx, localAt] using row
  rw [← descriptorEq]
  have scopeEq : localVar.scope = scope := facts.2.2.1
  simpa only [scopeEq] using active

theorem storageWalk_sliceRef_visible {env : Core.TEnv} {index : VarId} {type : Ty}
    (source : Core.sliceRefTy env (.read (.var index)) = some type) : index ∈ env.visible := by
  by_cases member : index ∈ env.visible
  · exact member
  · simp [Core.sliceRefTy, member] at source

#print axioms StorageWalkVisible.varOf
#print axioms StorageWalkVisible.declarePre
#print axioms StorageWalkVisible.tyStmt
#print axioms StorageWalkVisible.tyStmts

end Goose.Lower.Validation
