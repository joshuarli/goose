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

theorem StorageWalkConfiguration.emitTerm {slots : Array Slot}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (config : StorageWalkConfiguration slots entry exit before) (term : Term)
    (neutral : scopeNeutral (.term term) = true) (env : LEnv)
    (targets : ScopeTermTargets entry before.stack term)
    (bounds : ∀ target ∈ term.successors, target < before.blocks.size) :
    StorageWalkConfiguration slots entry exit (emitTerm term env before).2 := by
  refine ⟨config.builder.emitNeutralTerm term neutral env, currentOpen_emitTerm before term env,
    config.bounded.emitTerm term bounds env, ?_⟩
  apply config.edges.emitTerm term env
  intro block live
  rw [config.builder.current block live]
  exact targets

theorem StorageWalkConfiguration.newBlock {slots : Array Slot}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (config : StorageWalkConfiguration slots entry exit before) (types : List VTy) (env : LEnv) :
    StorageWalkConfiguration slots
      (fun block => if block = before.blocks.size then before.stack else entry block)
      (fun block => if block = before.blocks.size then before.stack else exit block)
      (newBlock types env before).2 :=
  ⟨config.builder.newBlock config.openCurrent.bound env types, config.openCurrent.newBlock types env,
    config.bounded.newBlock types env, config.edges.newBlock config.bounded env types⟩

theorem StorageWalkConfiguration.setCur {slots : Array Slot}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (config : StorageWalkConfiguration slots entry exit before) (block : BlockId) (body : BlockB)
    (row : before.blocks[block]? = some body) (openBody : OpenBlock body)
    (stack : exit block = before.stack) (env : LEnv) :
    StorageWalkConfiguration slots entry exit (Goose.Lower.setCur (some block) env before).2 := by
  refine ⟨config.builder.setCur (some block) ?_ env,
    CurrentOpen.setCur row openBody env, config.bounded.setCur (some block) env,
    config.edges.of_blocks rfl⟩
  intro other same
  cases same
  exact stack

theorem StorageWalkConfiguration.setNone {slots : Array Slot}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (config : StorageWalkConfiguration slots entry exit before) (env : LEnv) :
    StorageWalkConfiguration slots entry exit (Goose.Lower.setCur none env before).2 :=
  ⟨config.builder.setCur none (by simp) env, currentOpen_none rfl,
    config.bounded.setCur none env, config.edges.of_blocks rfl⟩

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

theorem StorageWalkAction.emitTerm (slots : Array Slot) (stack : List ScopeId)
    (loop : Option LoopCtx) (term : Term) (neutral : scopeNeutral (.term term) = true)
    (targets : ∀ entry, ScopeTermTargets entry stack term)
    (bounds : ∀ (state : LS), ∀ target ∈ term.successors, target < state.blocks.size) :
    StorageWalkAction slots stack loop (emitTerm term) := by
  refine ⟨advB_emitTerm _, ?_⟩
  intro env before entry exit config context stackEq
  have targetFact : ScopeTermTargets entry before.stack term := by
    intro target member
    exact (targets entry target member).trans stackEq.symm
  exact ⟨entry, exit, config.emitTerm term neutral env targetFact (bounds before),
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

theorem StorageWalkAction.newBlock0 (slots : Array Slot) (stack : List ScopeId)
    (loop : Option LoopCtx) :
    StorageWalkAction slots stack loop (newBlock [] : B (BlockId × List ValueId)) := by
  refine ⟨advB_newBlock0, ?_⟩
  intro env before entry exit config context stackEq
  let nextEntry := fun block => if block = before.blocks.size then before.stack else entry block
  let nextExit := fun block => if block = before.blocks.size then before.stack else exit block
  refine ⟨nextEntry, nextExit, config.newBlock [] env, ?_⟩
  intro block old
  have distinct : block ≠ before.blocks.size := Nat.ne_of_lt old
  simp [nextEntry, nextExit, distinct]

theorem StorageWalkAction.newBlock1 (slots : Array Slot) (stack : List ScopeId)
    (loop : Option LoopCtx) (type : VTy) :
    StorageWalkAction slots stack loop (newBlock [type] : B (BlockId × List ValueId)) := by
  refine ⟨advB_newBlock1 type, ?_⟩
  intro env before entry exit config context stackEq
  let nextEntry := fun block => if block = before.blocks.size then before.stack else entry block
  let nextExit := fun block => if block = before.blocks.size then before.stack else exit block
  refine ⟨nextEntry, nextExit, config.newBlock [type] env, ?_⟩
  intro block old
  have distinct : block ≠ before.blocks.size := Nat.ne_of_lt old
  simp [nextEntry, nextExit, distinct]

theorem StorageWalkAction.freezeTo (slots : Array Slot) (stack : List ScopeId)
    (loop : Option LoopCtx) (mutability : Mutability) (value : ValueId) :
    StorageWalkAction slots stack loop (freezeTo mutability value) := by
  unfold Goose.Lower.freezeTo
  refine (StorageWalkAction.valTy slots stack loop value).bind fun type => ?_
  cases mutability <;> cases type <;> first
    | exact .pure slots stack loop _
    | (rename_i type; cases type <;> first
      | exact .pure slots stack loop _
      | (rename_i mutability type; cases mutability <;> first
        | exact .pure slots stack loop _
        | exact .emitDef slots stack loop _ (by intro result; simp [StorageInstructionVisible])))

theorem StorageWalkAction.borrowTo (slots : Array Slot) (stack : List ScopeId)
    (loop : Option LoopCtx) (mutability : Mutability) (value : ValueId) :
    StorageWalkAction slots stack loop (borrowTo mutability value) := by
  unfold Goose.Lower.borrowTo
  refine (StorageWalkAction.read slots stack loop).bind fun env =>
    (StorageWalkAction.valTy slots stack loop value).bind fun type => ?_
  dsimp only
  split
  all_goals
    first
    | (simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte];
        exact StorageWalkAction.freezeTo slots stack loop mutability value)
    | (split <;> first
        | exact StorageWalkAction.emitDef slots stack loop _ (by intro result; simp [StorageInstructionVisible])
        | exact StorageWalkAction.freezeTo slots stack loop mutability value)

theorem StorageWalkAction.coerceTo (slots : Array Slot) (stack : List ScopeId)
    (loop : Option LoopCtx) (target : Ty) (value : ValueId) (origin : OriginId) :
    StorageWalkAction slots stack loop (coerceTo target value origin) := by
  unfold Goose.Lower.coerceTo
  refine (StorageWalkAction.valTy slots stack loop value).bind fun source => ?_
  split
  · exact StorageWalkAction.emitDef slots stack loop _ (by intro result; simp [StorageInstructionVisible])
  · exact (StorageWalkAction.emitDef slots stack loop _ (by intro result; simp [StorageInstructionVisible])).bind fun _ =>
      StorageWalkAction.emitDef slots stack loop _ (by intro result; simp [StorageInstructionVisible])
  · exact StorageWalkAction.pure slots stack loop _

theorem StorageWalkAction.coerceSlot (slots : Array Slot) (stack : List ScopeId)
    (loop : Option LoopCtx) (slot : SlotId) (value : ValueId) (origin : OriginId) :
    StorageWalkAction slots stack loop (coerceSlot slot value origin) := by
  unfold Goose.Lower.coerceSlot
  refine (StorageWalkAction.read slots stack loop).bind fun env => ?_
  cases env.slots[slot]? with
  | none => exact StorageWalkAction.pure slots stack loop _
  | some destination => exact StorageWalkAction.coerceTo slots stack loop _ _ _

theorem StorageWalkAction.coerceResult (slots : Array Slot) (stack : List ScopeId)
    (loop : Option LoopCtx) (value : ValueId) (origin : OriginId) :
    StorageWalkAction slots stack loop (coerceResult value origin) := by
  unfold Goose.Lower.coerceResult
  refine (StorageWalkAction.read slots stack loop).bind fun env => ?_
  cases env.results.head? with
  | none => exact StorageWalkAction.pure slots stack loop _
  | some destination => exact StorageWalkAction.coerceTo slots stack loop _ _ _

theorem StorageWalkAction.growOwner (slots : Array Slot) (stack : List ScopeId)
    (loop : Option LoopCtx) (value : ValueId) :
    StorageWalkAction slots stack loop (growOwner value) := by
  unfold Goose.Lower.growOwner
  refine (StorageWalkAction.valTy slots stack loop value).bind fun type => ?_
  cases type with
  | data type => cases type <;> first
    | exact StorageWalkAction.pure slots stack loop _
    | (rename_i mutability target; cases target <;> exact StorageWalkAction.pure slots stack loop _)
  | view _ _ => exact StorageWalkAction.pure slots stack loop _

theorem StorageWalkAction.regrowOf (slots : Array Slot) (stack : List ScopeId)
    (loop : Option LoopCtx) (value : Option ValueId) :
    StorageWalkAction slots stack loop (regrowOf value) := by
  cases value with
  | none => exact .pure slots stack loop _
  | some value => exact .growOwner slots stack loop value

theorem StorageWalkAction.eachSampled (slots : Array Slot) (stack : List ScopeId)
    (loop : Option LoopCtx) (regrow : Bool) (view : ValueId) :
    StorageWalkAction slots stack loop (eachSampled regrow view) := by
  unfold Goose.Lower.eachSampled
  split
  · exact .pure slots stack loop _
  · exact .emitDef slots stack loop _ (by intro result; simp [StorageInstructionVisible])

theorem StorageWalkAction.eachLen (slots : Array Slot) (stack : List ScopeId)
    (loop : Option LoopCtx) (regrow : Bool) (owner : Option ValueId) (sampled : ValueId) :
    StorageWalkAction slots stack loop (eachLen regrow owner sampled) := by
  unfold Goose.Lower.eachLen
  split
  · cases owner <;> exact .emitDef slots stack loop _ (by intro result; simp [StorageInstructionVisible])
  · exact .pure slots stack loop _

theorem StorageWalkAction.eachElemValue (slots : Array Slot) (stack : List ScopeId)
    (loop : Option LoopCtx) (varId : VarId) (byRef : Bool) (element : ValueId) :
    StorageWalkAction slots stack loop (eachElemValue varId byRef element) := by
  unfold Goose.Lower.eachElemValue
  split
  · refine (StorageWalkAction.read slots stack loop).bind fun env => ?_
    cases localLookup : env.vars[varId]? with
    | none => simp [localLookup]; exact .pure slots stack loop _
    | some localVar =>
      cases type : localVar.ty with
      | ref mutability _ => simp [localLookup, type]; exact .borrowTo slots stack loop mutability element
      | _ => simp [localLookup, type]; exact .pure slots stack loop _
  · exact .emitDef slots stack loop _ (by intro result; simp [StorageInstructionVisible])

end Goose.Lower.Validation
