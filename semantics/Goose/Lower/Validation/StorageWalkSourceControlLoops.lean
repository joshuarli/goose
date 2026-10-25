import Goose.Lower.Validation.StorageWalkControlBase
import Goose.Lower.Validation.StorageWalkSourceCollections
import Goose.Lower.Validation.StorageWalkControlWhile
import Goose.Lower.Validation.StorageWalkControlRange
import Goose.Lower.Validation.StorageWalkControlEach

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem storageWalk_source_while {env : Core.TEnv} {results : List Ty} {stack : List ScopeId}
    (scope : ScopeId) (condition : Expr) (body : Core.Block) (origin : OriginId)
    (conditionChild : StorageWalkSourceExpression env results stack condition)
    (bodyChild : ∀ env, StorageWalkSourceBlock env results stack body) :
    StorageWalkSourceStatement env results stack scope (.while condition body origin) := by
  intro output start finish source visible active loop
  obtain ⟨conditionFinish, bodyType, conditionSource, bodySource, _⟩ := tyStmt_while_children source
  exact StorageWalkAction.whileHeader (conditionChild conditionSource visible none)
    (fun header depth target => lowerBlock (some ⟨depth, target, .jump header⟩) [] false body)
    (fun header depth target => storageWalk_source_emptyBlock
      (bodyChild {env with loops := env.loops + 1}) bodySource visible (some ⟨depth, target, .jump header⟩) false)

theorem storageWalk_source_forRange {env : Core.TEnv} {results : List Ty} {stack : List ScopeId}
    (scope : ScopeId) (slot : VarId) (lo hi : Expr) (body : Core.Block) (origin : OriginId)
    (lowChild : StorageWalkSourceExpression env results stack lo) (highChild : StorageWalkSourceExpression env results stack hi)
    (bodyChild : ∀ env, StorageWalkSourceBlock env results stack body) :
    StorageWalkSourceStatement env results stack scope (.forRange slot lo hi body origin) := by
  intro output start finish source visible active loop
  obtain ⟨localVar, integer, lowerStart, lowerFinish, upperFinish, bodyType,
    declared, lowSource, highSource, binderType, bodySource, _⟩ := tyStmt_forRange_children source
  have insideVisible := (visible.mono (fun id member => List.mem_cons_of_mem body.scope member)).declare (by simp) declared
  exact (lowChild lowSource visible loop).bind fun lowerValue =>
    (highChild highSource visible loop).bind fun upperValue =>
      StorageWalkAction.whenLive () fun _ => (StorageWalkAction.intTyOf _ stack loop lowerValue).bind fun hint =>
        StorageWalkAction.rangeHeader hint lowerValue upperValue
          (fun header counter depth target => lowerBlock (some ⟨depth, target, .next header hint counter⟩)
            [(slot, counter, origin)] false body)
          (fun header counter depth target => bodyChild
            {env with loops := env.loops + 1, visible := slot :: env.visible} bodySource insideVisible
            (some ⟨depth, target, .next header hint counter⟩) [(slot, counter, origin)] false (by
              intro entry member
              cases List.mem_singleton.mp member
              intro descriptor row
              exact storageWalk_declared_slot (by simp) declared results row))

theorem storageWalk_source_forEach {env : Core.TEnv} {results : List Ty} {stack : List ScopeId}
    (scope : ScopeId) (slot : VarId) (index : Option VarId) (view : View) (byRef : Bool)
    (body : Core.Block) (origin : OriginId)
    (sourceChild : StorageWalkSourceEachSource env results stack view)
    (bodyChild : ∀ env, StorageWalkSourceBlock env results stack body) :
    StorageWalkSourceStatement env results stack scope (.forEach slot index view byRef body origin) := by
  cases index with
  | none =>
    intro output start finish source visible active loop
    obtain ⟨localVar, element, writable, indexStart, viewStart, viewFinish, bodyType,
      declared, indexChecked, viewSource, binding, bodySource, _⟩ := tyStmt_forEach_children source
    have nestedVisible := visible.mono (fun id member => List.mem_cons_of_mem body.scope member)
    have indexedVisible := nestedVisible.prepend (none : Option VarId).toList (by
      intro variableId member localVar row
      rw [storageWalk_declared_index_scope indexChecked variableId member localVar row]
      exact List.mem_cons_self)
    have insideVisible := indexedVisible.declare (by simp) declared
    have preActive (value counter : ValueId) :
        ∀ entry ∈ ((slot, value, origin) :: (none : Option VarId).toList.map (fun id => (id, counter, origin))),
          StorageSlotVisible (lowerEnv env.mod env.vars results).slots (body.scope :: stack) entry.1 := by
      intro entry member
      rcases List.mem_cons.mp member with same | member
      · cases same
        intro descriptor row
        exact storageWalk_declared_slot (by simp) declared results row
      · obtain ⟨id, idMember, same⟩ := List.mem_map.mp member
        subst entry
        intro descriptor row
        cases localAt : env.vars[id]? with
        | none => simp [lowerEnv, Array.getElem?_mapIdx, localAt] at row
        | some indexVar =>
          have descriptorEq : (⟨indexVar.ty, indexVar.kind, indexVar.scope, id⟩ : Slot) = descriptor := by
            simpa [lowerEnv, Array.getElem?_mapIdx, localAt] using row
          rw [← descriptorEq]
          have declaredScope := storageWalk_declared_index_scope indexChecked id idMember indexVar localAt
          simpa only [declaredScope] using (List.mem_cons_self : body.scope ∈ body.scope :: stack)
    exact (sourceChild viewSource visible loop).bind fun ownerView =>
      (StorageWalkAction.regrowOf _ stack loop ownerView.1).bind fun regrow =>
        (StorageWalkAction.eachSampled _ stack loop regrow ownerView.2).bind fun sampled =>
          (StorageWalkAction.emitDef _ stack loop (.constInt .i64 0) (by simp [StorageInstructionVisible])).bind fun start =>
            StorageWalkAction.whenLive () fun _ =>
              StorageWalkAction.eachHeader regrow ownerView.1 sampled start
                (fun header counter depth target => do
                  let address ← emitDef (.refElem ownerView.2 counter)
                  let value ← eachElemValue slot byRef address
                  lowerBlock (some ⟨depth, target, .next header .i64 counter⟩)
                    ((slot, value, origin) :: (none : Option VarId).toList.map (fun id => (id, counter, origin))) false body)
                (fun header counter depth target =>
                  (StorageWalkAction.emitDef _ stack (some ⟨depth, target, .next header .i64 counter⟩)
                    (.refElem ownerView.2 counter) (by simp [StorageInstructionVisible])).bind fun address =>
                      (StorageWalkAction.eachElemValue _ stack (some ⟨depth, target, .next header .i64 counter⟩)
                        slot byRef address).bind fun value =>
                          bodyChild {env with loops := env.loops + 1, visible := slot :: (none : Option VarId).toList ++ env.visible}
                            bodySource insideVisible (some ⟨depth, target, .next header .i64 counter⟩)
                            ((slot, value, origin) :: (none : Option VarId).toList.map (fun id => (id, counter, origin))) false
                            (preActive value counter))
  | some indexSlot =>
    intro output start finish source visible active loop
    obtain ⟨localVar, element, writable, indexStart, viewStart, viewFinish, bodyType,
      declared, indexChecked, viewSource, binding, bodySource, _⟩ := tyStmt_forEach_children source
    have nestedVisible := visible.mono (fun id member => List.mem_cons_of_mem body.scope member)
    have indexedVisible := nestedVisible.prepend (some indexSlot).toList (by
      intro variableId member localVar row
      rw [storageWalk_declared_index_scope indexChecked variableId member localVar row]
      exact List.mem_cons_self)
    have insideVisible := indexedVisible.declare (by simp) declared
    have preActive (value counter : ValueId) :
        ∀ entry ∈ ((slot, value, origin) :: (some indexSlot).toList.map (fun id => (id, counter, origin))),
          StorageSlotVisible (lowerEnv env.mod env.vars results).slots (body.scope :: stack) entry.1 := by
      intro entry member
      rcases List.mem_cons.mp member with same | member
      · cases same
        intro descriptor row
        exact storageWalk_declared_slot (by simp) declared results row
      · obtain ⟨id, idMember, same⟩ := List.mem_map.mp member
        subst entry
        intro descriptor row
        cases localAt : env.vars[id]? with
        | none => simp [lowerEnv, Array.getElem?_mapIdx, localAt] at row
        | some indexVar =>
          have descriptorEq : (⟨indexVar.ty, indexVar.kind, indexVar.scope, id⟩ : Slot) = descriptor := by
            simpa [lowerEnv, Array.getElem?_mapIdx, localAt] using row
          rw [← descriptorEq]
          have declaredScope := storageWalk_declared_index_scope indexChecked id idMember indexVar localAt
          simpa only [declaredScope] using (List.mem_cons_self : body.scope ∈ body.scope :: stack)
    exact (sourceChild viewSource visible loop).bind fun ownerView =>
      (StorageWalkAction.regrowOf _ stack loop ownerView.1).bind fun regrow =>
        (StorageWalkAction.eachSampled _ stack loop regrow ownerView.2).bind fun sampled =>
          (StorageWalkAction.emitDef _ stack loop (.constInt .i64 0) (by simp [StorageInstructionVisible])).bind fun start =>
            StorageWalkAction.whenLive () fun _ =>
              StorageWalkAction.eachHeader regrow ownerView.1 sampled start
                (fun header counter depth target => do
                  let address ← emitDef (.refElem ownerView.2 counter)
                  let value ← eachElemValue slot byRef address
                  lowerBlock (some ⟨depth, target, .next header .i64 counter⟩)
                    ((slot, value, origin) :: (some indexSlot).toList.map (fun id => (id, counter, origin))) false body)
                (fun header counter depth target =>
                  (StorageWalkAction.emitDef _ stack (some ⟨depth, target, .next header .i64 counter⟩)
                    (.refElem ownerView.2 counter) (by simp [StorageInstructionVisible])).bind fun address =>
                      (StorageWalkAction.eachElemValue _ stack (some ⟨depth, target, .next header .i64 counter⟩)
                        slot byRef address).bind fun value =>
                          bodyChild {env with loops := env.loops + 1, visible := slot :: (some indexSlot).toList ++ env.visible}
                            bodySource insideVisible (some ⟨depth, target, .next header .i64 counter⟩)
                            ((slot, value, origin) :: (some indexSlot).toList.map (fun id => (id, counter, origin))) false
                            (preActive value counter))

#print axioms storageWalk_source_while
#print axioms storageWalk_source_forRange
#print axioms storageWalk_source_forEach

end Goose.Lower.Validation
