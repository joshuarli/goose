import Goose.Lower.Validation.StorageWalkBuilder
import Goose.Lower.Validation.ScopeFlow

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

structure StorageWalkConfiguration (slots : Array Slot)
    (entry exit : BlockId → List ScopeId) (state : LS) : Prop where
  builder : StorageWalkBuilder slots entry exit state
  openCurrent : CurrentOpen state
  bounded : TargetsBounded state
  edges : ScopeEdges entry exit state

theorem StorageWalkConfiguration.emitDef {slots : Array Slot}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (config : StorageWalkConfiguration slots entry exit before) (op : Op) (env : LEnv)
    (visible : ∀ result, StorageInstructionVisible slots before.stack (.def result op)) :
    StorageWalkConfiguration slots entry exit (emitDef op env before).2 :=
  ⟨config.builder.emitDef op env visible, config.openCurrent.emitDef op env,
    config.bounded.emitDef op env, config.edges.emitDef op env⟩

theorem StorageWalkConfiguration.emitNeutralEffect {slots : Array Slot}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (config : StorageWalkConfiguration slots entry exit before) (effect : Effect)
    (neutral : scopeNeutral (.eff effect) = true) (env : LEnv)
    (visible : StorageInstructionVisible slots before.stack (.eff effect)) :
    StorageWalkConfiguration slots entry exit (emitEffect effect env before).2 :=
  ⟨config.builder.emitNeutralEffect effect neutral env visible,
    config.openCurrent.emitEffect effect env, config.bounded.emitEffect effect env,
    config.edges.emitEffect effect env⟩

structure StorageWalkAction (slots : Array Slot) (stack : List ScopeId)
    (loop : Option LoopCtx) (action : B α) : Prop where
  advance : AdvB action
  preserves : ∀ (env : LEnv) (before : LS) (entry exit : BlockId → List ScopeId),
    StorageWalkConfiguration slots entry exit before →
    ScopeLoopContext loop entry before.stack before.blocks.size → before.stack = stack →
    ∃ nextEntry nextExit, StorageWalkConfiguration slots nextEntry nextExit (action env before).2 ∧
      ScopeMapAdvance before entry exit nextEntry nextExit

theorem StorageWalkAction.pure (slots : Array Slot) (stack : List ScopeId)
    (loop : Option LoopCtx) (value : α) :
    StorageWalkAction slots stack loop (pure value : B α) := by
  refine ⟨AdvB.pure _, ?_⟩
  intro env before entry exit config context stackEq
  exact ⟨entry, exit, config, ScopeMapAdvance.refl _ _ _⟩

theorem StorageWalkAction.bind {slots : Array Slot} {stack : List ScopeId}
    {loop : Option LoopCtx} {first : B α} {next : α → B β}
    (action : StorageWalkAction slots stack loop first)
    (rest : ∀ value, StorageWalkAction slots stack loop (next value)) :
    StorageWalkAction slots stack loop (first >>= next) := by
  refine ⟨action.advance.bind (fun value => (rest value).advance), ?_⟩
  intro env before entry exit config context stackEq
  obtain ⟨middleEntry, middleExit, middleConfig, firstMaps⟩ :=
    action.preserves env before entry exit config context stackEq
  have advance := action.advance env before _ _ rfl
  have middleContext := ScopeLoopContext.advance context advance firstMaps
  have middleStack : (first env before).2.stack = stack := by
    rw [advance.stack]
    exact stackEq
  obtain ⟨afterEntry, afterExit, afterConfig, secondMaps⟩ :=
    (rest (first env before).1).preserves env (first env before).2 middleEntry middleExit
      middleConfig middleContext middleStack
  exact ⟨afterEntry, afterExit, afterConfig, firstMaps.trans advance secondMaps⟩

theorem StorageWalkAction.weakenLoop {slots : Array Slot} {stack : List ScopeId}
    {action : B α} (source : StorageWalkAction slots stack none action) (loop : Option LoopCtx) :
    StorageWalkAction slots stack loop action := by
  refine ⟨source.advance, ?_⟩
  intro env before entry exit config context stackEq
  exact source.preserves env before entry exit config trivial stackEq

theorem StorageWalkAction.observe (slots : Array Slot) (stack : List ScopeId)
    (loop : Option LoopCtx) (action : B α) (advance : AdvB action)
    (same : ∀ env before, (action env before).2 = before) :
    StorageWalkAction slots stack loop action := by
  refine ⟨advance, ?_⟩
  intro env before entry exit config context stackEq
  refine ⟨entry, exit, ?_, ScopeMapAdvance.refl _ _ _⟩
  rw [same]
  exact config

theorem StorageWalkAction.emitDef (slots : Array Slot) (stack : List ScopeId)
    (loop : Option LoopCtx) (op : Op)
    (visible : ∀ result, StorageInstructionVisible slots stack (.def result op)) :
    StorageWalkAction slots stack loop (emitDef op) := by
  refine ⟨advB_emitDef _, ?_⟩
  intro env before entry exit config context stackEq
  refine ⟨entry, exit, config.emitDef op env ?_, ScopeMapAdvance.refl _ _ _⟩
  intro result
  rw [stackEq]
  exact visible result

theorem StorageWalkAction.emitEffect (slots : Array Slot) (stack : List ScopeId)
    (loop : Option LoopCtx) (effect : Effect) (neutral : scopeNeutral (.eff effect) = true)
    (visible : StorageInstructionVisible slots stack (.eff effect)) :
    StorageWalkAction slots stack loop (emitEffect effect) := by
  refine ⟨advB_emitEffect _, ?_⟩
  intro env before entry exit config context stackEq
  exact ⟨entry, exit, config.emitNeutralEffect effect neutral env (by rw [stackEq]; exact visible),
    ScopeMapAdvance.refl _ _ _⟩

theorem StorageWalkAction.get (slots : Array Slot) (stack : List ScopeId) (loop : Option LoopCtx) :
    StorageWalkAction slots stack loop (get : B LS) :=
  .observe slots stack loop _ advB_get (fun _ _ => rfl)

theorem StorageWalkAction.read (slots : Array Slot) (stack : List ScopeId) (loop : Option LoopCtx) :
    StorageWalkAction slots stack loop (read : B LEnv) :=
  .observe slots stack loop _ advB_read (fun _ _ => rfl)

theorem StorageWalkAction.valTy (slots : Array Slot) (stack : List ScopeId)
    (loop : Option LoopCtx) (value : ValueId) :
    StorageWalkAction slots stack loop (valTy value) :=
  .observe slots stack loop _ (advB_valTy value) (fun env state => valTy_run value env state)

theorem StorageWalkAction.curBlock (slots : Array Slot) (stack : List ScopeId)
    (loop : Option LoopCtx) : StorageWalkAction slots stack loop curBlock :=
  .observe slots stack loop _ advB_curBlock (fun _ _ => rfl)

theorem StorageWalkAction.isLive (slots : Array Slot) (stack : List ScopeId)
    (loop : Option LoopCtx) : StorageWalkAction slots stack loop isLive :=
  .observe slots stack loop _ advB_isLive (fun _ _ => rfl)

theorem StorageWalkAction.intTyOf (slots : Array Slot) (stack : List ScopeId)
    (loop : Option LoopCtx) (value : ValueId) :
    StorageWalkAction slots stack loop (intTyOf value) := by
  unfold Goose.Lower.intTyOf
  refine (StorageWalkAction.valTy slots stack loop value).bind fun type => ?_
  cases type with
  | data type => cases type <;> exact .pure slots stack loop _
  | view _ _ => exact .pure slots stack loop _

end Goose.Lower.Validation
