import Goose.Lower.Validation.StorageWalkActions
import Goose.Lower.Validation.ScopeFlow

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem StorageWalkBuilder.closedStack {slots : Array Slot}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (valid : StorageWalkBuilder slots entry exit before) (closed : before.cur = none)
    (stack : List ScopeId) :
    StorageWalkBuilder slots entry exit {before with stack := stack} := by
  refine ⟨valid.traces, ?_⟩
  intro block current
  simp [closed] at current

theorem StorageWalkBuilder.enter {slots : Array Slot}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (valid : StorageWalkBuilder slots entry exit before) (scope : ScopeId) (env : LEnv)
    (block : BlockId) (live : before.cur = some block) :
    StorageWalkBuilder slots entry (fun other => if other = block then scope :: exit block else exit other)
      ((emitEffect (.enter scope) >>= fun _ => pushScope scope) env before).2 := by
  rw [bind_run, emitEffect_run _ _ live, pushScope_run]
  dsimp only
  refine ⟨?_, ?_⟩
  · apply valid.traces.append block (.eff (.enter scope)) (scope :: exit block)
    exact .enter (.nil _)
  · intro other current
    have same : other = block := Option.some.inj (current.symm.trans live)
    subst other
    simp [valid.current block live]

theorem StorageWalkBuilder.leave {slots : Array Slot}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (valid : StorageWalkBuilder slots entry exit before) (scope : ScopeId) (rest : List ScopeId)
    (env : LEnv) (block : BlockId) (live : before.cur = some block)
    (stack : before.stack = scope :: rest) :
    StorageWalkBuilder slots entry (fun other => if other = block then rest else exit other)
      ((emitEffect (.leave scope) >>= fun _ => popScope) env before).2 := by
  rw [bind_run, emitEffect_run _ _ live, popScope_run]
  dsimp only
  refine ⟨?_, ?_⟩
  · apply valid.traces.append block (.eff (.leave scope)) rest
    rw [valid.current block live, stack]
    exact .leave (.nil _)
  · intro other current
    have same : other = block := Option.some.inj (current.symm.trans live)
    subst other
    simp [stack]

theorem StorageWalkBuilder.enterScope {slots : Array Slot}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (valid : StorageWalkBuilder slots entry exit before) (scope : ScopeId) (env : LEnv) :
    StorageWalkBuilder slots entry (scopeExitUpdate before.cur (scope :: before.stack) exit)
      (enterScope scope env before).2 := by
  cases live : before.cur with
  | none =>
    simp only [Goose.Lower.Validation.enterScope, bind_run, emitEffect_none _ _ live, pushScope_run]
    change StorageWalkBuilder slots entry exit { before with stack := scope :: before.stack }
    exact valid.closedStack live (scope :: before.stack)
  | some block =>
    have entered := valid.enter scope env block live
    have same : (fun other => if other = block then scope :: exit block else exit other) =
        scopeExitUpdate before.cur (scope :: before.stack) exit := by
      funext other
      rw [live, valid.current block live]
      simp [scopeExitUpdate, eq_comm]
    simpa only [same, live, Goose.Lower.Validation.enterScope] using entered

theorem StorageWalkBuilder.leaveScope {slots : Array Slot}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (valid : StorageWalkBuilder slots entry exit before) (scope : ScopeId) (rest : List ScopeId)
    (env : LEnv) (stack : before.stack = scope :: rest) :
    StorageWalkBuilder slots entry (scopeExitUpdate before.cur rest exit)
      (leaveScope scope env before).2 := by
  cases live : before.cur with
  | none =>
    simp only [Goose.Lower.Validation.leaveScope, bind_run, emitEffect_none _ _ live, popScope_run]
    change StorageWalkBuilder slots entry exit { before with stack := before.stack.drop 1 }
    simpa only [stack, List.drop_succ_cons, List.drop_zero] using valid.closedStack live rest
  | some block =>
    have left := valid.leave scope rest env block live stack
    have same : (fun other => if other = block then rest else exit other) =
        scopeExitUpdate before.cur rest exit := by
      funext other
      simp [scopeExitUpdate, live, eq_comm]
    simpa only [same, live, Goose.Lower.Validation.leaveScope] using left

theorem StorageWalkConfiguration.enterScope {slots : Array Slot}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (config : StorageWalkConfiguration slots entry exit before) (scope : ScopeId) (env : LEnv) :
    StorageWalkConfiguration slots entry (scopeExitUpdate before.cur (scope :: before.stack) exit)
      (Goose.Lower.Validation.enterScope scope env before).2 := by
  refine ⟨config.builder.enterScope scope env, ?_, ?_,
    config.edges.enterScope config.openCurrent scope env⟩
  · apply (config.openCurrent.emitEffect (.enter scope) env).of_state <;> rfl
  · apply (config.bounded.emitEffect (.enter scope) env).of_blocks
    rfl

theorem StorageWalkConfiguration.leaveScope {slots : Array Slot}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (config : StorageWalkConfiguration slots entry exit before) (scope : ScopeId)
    (rest : List ScopeId) (env : LEnv) (stack : before.stack = scope :: rest) :
    StorageWalkConfiguration slots entry (scopeExitUpdate before.cur rest exit)
      (Goose.Lower.Validation.leaveScope scope env before).2 := by
  refine ⟨config.builder.leaveScope scope rest env stack, ?_, ?_,
    config.edges.leaveScope config.openCurrent scope rest env⟩
  · apply (config.openCurrent.emitEffect (.leave scope) env).of_state <;> rfl
  · apply (config.bounded.emitEffect (.leave scope) env).of_blocks
    rfl

theorem StorageWalkAction.initSlots (slots : Array Slot) (stack : List ScopeId)
    (loop : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId))
    (visible : ∀ entry ∈ pre, StorageSlotVisible slots stack entry.1) :
    StorageWalkAction slots stack loop (Goose.Lower.initSlots pre) := by
  induction pre with
  | nil => exact .pure slots stack loop _
  | cons entry rest ih =>
    rcases entry with ⟨slot,value,origin⟩
    exact (StorageWalkAction.emitEffect slots stack loop (.slotInit slot value (some origin)) rfl
      (visible (slot,value,origin) (by simp))).bind fun _ =>
        ih (fun entry member => visible entry (by simp [member]))

theorem StorageWalkAction.scoped {slots : Array Slot} {stack : List ScopeId}
    {loop : Option LoopCtx} (scope : ScopeId) {inside : B α}
    (body : StorageWalkAction slots (scope :: stack) loop inside) :
    StorageWalkAction slots stack loop (scopedAction scope inside) := by
  refine ⟨?_, ?_⟩
  · rw [scopedAction_eq]
    exact AdvB.bind (advB_emitEffect _) fun _ => advB_inScope scope
      (AdvB.bind body.advance fun result => AdvB.bind (advB_emitEffect _) fun _ => AdvB.pure result)
  ·
    intro env before entry exit config context stackEq
    let entered := (enterScope scope env before).2
    let enteredExit := scopeExitUpdate before.cur (scope :: before.stack) exit
    have enteredState := enterScope_state scope env before
    have enteredConfig : StorageWalkConfiguration slots entry enteredExit entered :=
      config.enterScope scope env
    have enteredContext : ScopeLoopContext loop entry entered.stack entered.blocks.size := by
      rw [enteredState.2.1, enteredState.2.2]
      exact ScopeLoopContext.enter context scope
    have enteredStack : entered.stack = scope :: stack := by rw [enteredState.2.1, stackEq]
    obtain ⟨middleEntry, middleExit, middleConfig, middleMaps⟩ :=
      body.preserves env entered entry enteredExit enteredConfig enteredContext enteredStack
    have bodyAdvance := body.advance env entered _ _ rfl
    have middleStack : (inside env entered).2.stack = scope :: before.stack :=
      bodyAdvance.stack.trans enteredState.2.1
    have finalConfig := middleConfig.leaveScope scope before.stack env middleStack
    refine ⟨middleEntry, scopeExitUpdate (inside env entered).2.cur before.stack middleExit, finalConfig, ?_⟩
    intro block earlier
    have enteredEarlier : block < entered.blocks.size := by rw [enteredState.2.2]; exact earlier
    have middleFrame := middleMaps block enteredEarlier
    refine ⟨middleFrame.1, ?_⟩
    intro other
    have enteredOther : entered.cur ≠ some block := by rw [enteredState.1]; exact other
    have middleOther := LS_Adv.otherCurrent bodyAdvance enteredEarlier enteredOther
    simp only [scopeExitUpdate, middleOther, ite_false]
    rw [middleFrame.2 enteredOther]
    simp only [enteredExit, scopeExitUpdate, other, ite_false]


#print axioms StorageWalkBuilder.enterScope
#print axioms StorageWalkBuilder.leaveScope
#print axioms StorageWalkConfiguration.enterScope
#print axioms StorageWalkConfiguration.leaveScope
#print axioms StorageWalkAction.initSlots
#print axioms StorageWalkAction.scoped

end Goose.Lower.Validation
