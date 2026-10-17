import Goose.Lower.Validation.ScopeWalk

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def StorageSlotVisible (slots : Array GIR.Slot) (stack : List ScopeId) (slot : SlotId) : Prop :=
  ∀ descriptor, slots[slot]? = some descriptor → descriptor.scope ∈ stack

def StorageInstructionVisible (slots : Array GIR.Slot) (stack : List ScopeId) : Inst → Prop
  | .def _ (.slotAddr slot) => StorageSlotVisible slots stack slot
  | .eff (.slotInit slot _ _) => StorageSlotVisible slots stack slot
  | _ => True

@[simp] theorem ScopeWalk.noteScopes_storage (walk : ScopeWalk) (message : String) :
    (walk.noteScopes message).storage = walk.storage := by
  cases scopes : walk.scopes <;> simp [ScopeWalk.noteScopes, scopes]

@[simp] theorem ScopeWalk.if_noteScopes_storage (condition : Prop) [Decidable condition]
    (walk : ScopeWalk) (message : String) :
    (if condition then walk else walk.noteScopes message).storage = walk.storage := by
  by_cases condition <;> simp [*]

inductive StorageWalkTrace (slots : Array GIR.Slot) :
    List ScopeId → List Inst → List ScopeId → Prop
  | nil (stack) : StorageWalkTrace slots stack [] stack
  | neutral {before after inst rest} (neutral : scopeNeutral inst = true)
      (visible : StorageInstructionVisible slots before inst)
      (tail : StorageWalkTrace slots before rest after) :
      StorageWalkTrace slots before (inst :: rest) after
  | enter {before after scope rest}
      (tail : StorageWalkTrace slots (scope :: before) rest after) :
      StorageWalkTrace slots before (.eff (.enter scope) :: rest) after
  | leave {before after scope rest}
      (tail : StorageWalkTrace slots before rest after) :
      StorageWalkTrace slots (scope :: before) (.eff (.leave scope) :: rest) after
  | ret {after values origin rest}
      (tail : StorageWalkTrace slots [] rest after) :
      StorageWalkTrace slots [] (.term (.ret values origin) :: rest) after

theorem StorageWalkTrace.append {slots : Array GIR.Slot}
    {before middle after : List ScopeId} {left right : List Inst}
    (first : StorageWalkTrace slots before left middle)
    (second : StorageWalkTrace slots middle right after) :
    StorageWalkTrace slots before (left ++ right) after := by
  induction first with
  | nil => exact second
  | neutral neutral visible tail ih => exact .neutral neutral visible (ih second)
  | enter tail ih => exact .enter (ih second)
  | leave tail ih => exact .leave (ih second)
  | ret tail ih => exact .ret (ih second)

theorem StorageWalkTrace.leavePrefix (slots : Array GIR.Slot) (front rest : List ScopeId) :
    StorageWalkTrace slots (front ++ rest) (front.map fun scope => .eff (.leave scope)) rest := by
  induction front with
  | nil => exact .nil rest
  | cons scope front ih => exact .leave ih

theorem StorageWalkTrace.leaveTo (slots : Array GIR.Slot)
    (stack : List ScopeId) (depth : Nat) :
    StorageWalkTrace slots stack
      ((stack.take (stack.length - depth)).map fun scope => .eff (.leave scope))
      (stack.drop (stack.length - depth)) := by
  have trace := StorageWalkTrace.leavePrefix slots
    (stack.take (stack.length - depth)) (stack.drop (stack.length - depth))
  simpa using trace

theorem StorageWalkTrace.leaveReturn (slots : Array GIR.Slot)
    (stack : List ScopeId) (values : List ValueId) (origin : Option OriginId) :
    StorageWalkTrace slots stack
      ((stack.map fun scope => .eff (.leave scope)) ++ [.term (.ret values origin)]) [] := by
  have leaves : StorageWalkTrace slots stack
      (stack.map fun scope => .eff (.leave scope)) [] := by
    simpa using StorageWalkTrace.leavePrefix slots stack []
  exact leaves.append (.ret (.nil []))

theorem StorageWalkTrace.scoped {slots : Array GIR.Slot}
    {stack : List ScopeId} {scope : ScopeId} {insts : List Inst}
    (inside : StorageWalkTrace slots (scope :: stack) insts (scope :: stack)) :
    StorageWalkTrace slots stack
      (.eff (.enter scope) :: (insts ++ [.eff (.leave scope)])) stack :=
  .enter (inside.append (.leave (.nil stack)))

theorem walkBlock_storage_neutral {func : Func} {block : BlockId} {params : List (ValueId × VTy)}
    {inst : Inst} {stack : List ScopeId} {walk : ScopeWalk}
    (neutral : scopeNeutral inst = true)
    (visible : StorageInstructionVisible func.slots stack inst) :
    (GIR.walkBlock func block ⟨params, [inst]⟩ stack walk).1 = stack ∧
      (GIR.walkBlock func block ⟨params, [inst]⟩ stack walk).2.storage = walk.storage := by
  cases inst with
  | «def» value op =>
    cases op with
    | slotAddr slot =>
      cases lookup : func.slots[slot]? with
      | none => simp [GIR.walkBlock, lookup]
      | some descriptor =>
        have inStack := visible descriptor lookup
        simp [GIR.walkBlock, ScopeWalk.noteStorage, lookup, List.contains_eq_mem, inStack]
    | _ => simp [GIR.walkBlock]
  | eff effect =>
    cases effect with
    | slotInit slot value origin =>
      cases lookup : func.slots[slot]? with
      | none => simp [GIR.walkBlock, lookup]
      | some descriptor =>
        have inStack := visible descriptor lookup
        simp [GIR.walkBlock, ScopeWalk.noteStorage, lookup, List.contains_eq_mem, inStack]
    | enter scope => simp [scopeNeutral] at neutral
    | leave scope => simp [scopeNeutral] at neutral
    | _ => simp [GIR.walkBlock]
  | term term =>
    cases term with
    | ret values origin => simp [scopeNeutral] at neutral
    | _ => simp [GIR.walkBlock]

theorem walkBlock_storage_enter {func : Func} {block : BlockId} {params : List (ValueId × VTy)}
    {scope : ScopeId} {stack : List ScopeId} {walk : ScopeWalk} :
    (GIR.walkBlock func block ⟨params, [.eff (.enter scope)]⟩ stack walk).1 = scope :: stack ∧
      (GIR.walkBlock func block ⟨params, [.eff (.enter scope)]⟩ stack walk).2.storage = walk.storage := by
  simp [GIR.walkBlock]

theorem walkBlock_storage_leave {func : Func} {block : BlockId} {params : List (ValueId × VTy)}
    {scope : ScopeId} {stack : List ScopeId} {walk : ScopeWalk} :
    (GIR.walkBlock func block ⟨params, [.eff (.leave scope)]⟩ (scope :: stack) walk).1 = stack ∧
      (GIR.walkBlock func block ⟨params, [.eff (.leave scope)]⟩ (scope :: stack) walk).2.storage = walk.storage := by
  simp [GIR.walkBlock]

theorem walkBlock_storage_ret {func : Func} {block : BlockId} {params : List (ValueId × VTy)}
    {values : List ValueId} {origin : Option OriginId} {walk : ScopeWalk} :
    (GIR.walkBlock func block ⟨params, [.term (.ret values origin)]⟩ [] walk).1 = [] ∧
      (GIR.walkBlock func block ⟨params, [.term (.ret values origin)]⟩ [] walk).2.storage = walk.storage := by
  simp [GIR.walkBlock]

theorem StorageWalkTrace.walkBlock {func : Func} {before after : List ScopeId} {insts : List Inst}
    (trace : StorageWalkTrace func.slots before insts after) (block : BlockId) (params)
    (walk : ScopeWalk) :
    (GIR.walkBlock func block ⟨params, insts⟩ before walk).1 = after ∧
      (GIR.walkBlock func block ⟨params, insts⟩ before walk).2.storage = walk.storage := by
  induction trace generalizing walk with
  | nil => simp [GIR.walkBlock]
  | @neutral before after inst rest neutral visible tail ih =>
    rw [walkBlock_cons]
    have one := walkBlock_storage_neutral (func := func) (block := block) (params := params)
      (stack := before) (walk := walk) neutral visible
    obtain ⟨out, storage⟩ := ih (GIR.walkBlock func block ⟨params, [inst]⟩ before walk).2
    dsimp only
    rw [one.1]
    exact ⟨out, storage.trans one.2⟩
  | @enter before after scope rest tail ih =>
    rw [walkBlock_cons]
    have one := walkBlock_storage_enter (func := func) (block := block) (params := params)
      (scope := scope) (stack := before) (walk := walk)
    obtain ⟨out, storage⟩ := ih (GIR.walkBlock func block ⟨params, [.eff (.enter scope)]⟩ before walk).2
    dsimp only
    rw [one.1]
    exact ⟨out, storage.trans one.2⟩
  | @leave before after scope rest tail ih =>
    rw [walkBlock_cons]
    have one := walkBlock_storage_leave (func := func) (block := block) (params := params)
      (scope := scope) (stack := before) (walk := walk)
    obtain ⟨out, storage⟩ := ih (GIR.walkBlock func block ⟨params, [.eff (.leave scope)]⟩ (scope :: before) walk).2
    dsimp only
    rw [one.1]
    exact ⟨out, storage.trans one.2⟩
  | @ret after values origin rest tail ih =>
    rw [walkBlock_cons]
    have one := walkBlock_storage_ret (func := func) (block := block) (params := params)
      (values := values) (origin := origin) (walk := walk)
    obtain ⟨out, storage⟩ := ih (GIR.walkBlock func block ⟨params, [.term (.ret values origin)]⟩ [] walk).2
    dsimp only
    rw [one.1]
    exact ⟨out, storage.trans one.2⟩

end Goose.Lower.Validation
