import Goose.Lower.Validation.ScopeActions

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def scopeExitUpdate (current : Option BlockId) (stack : List ScopeId)
    (old : BlockId → List ScopeId) : BlockId → List ScopeId :=
  fun block => if current = some block then stack else old block

def enterScope (scope : ScopeId) : B Unit := do
  emitEffect (.enter scope)
  pushScope scope

def leaveScope (scope : ScopeId) : B Unit := do
  emitEffect (.leave scope)
  popScope

def scopedAction (scope : ScopeId) (inside : B α) : B α := do
  enterScope scope
  let result ← inside
  leaveScope scope
  pure result

theorem enterScope_state (scope : ScopeId) (env : LEnv) (before : LS) :
    (enterScope scope env before).2.cur = before.cur ∧
      (enterScope scope env before).2.stack = scope :: before.stack ∧
      (enterScope scope env before).2.blocks.size = before.blocks.size := by
  cases live : before.cur with
  | none => simp [enterScope, live, bind_run, emitEffect_none _ _ live, pushScope_run]
  | some block => simp [enterScope, live, bind_run, emitEffect_run _ _ live, pushScope_run]

theorem leaveScope_state (scope : ScopeId) (env : LEnv) (before : LS) :
    (leaveScope scope env before).2.cur = before.cur ∧
      (leaveScope scope env before).2.stack = before.stack.drop 1 ∧
      (leaveScope scope env before).2.blocks.size = before.blocks.size := by
  cases live : before.cur with
  | none => simp [leaveScope, live, bind_run, emitEffect_none _ _ live, popScope_run]
  | some block => simp [leaveScope, live, bind_run, emitEffect_run _ _ live, popScope_run]

theorem ScopeBuilder.enterScope {parents : Array (Option ScopeId)}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (valid : ScopeBuilder parents entry exit before) (scope : ScopeId) (env : LEnv)
    (parent : parents[scope]?.getD none = before.stack.head?) :
    ScopeBuilder parents entry (scopeExitUpdate before.cur (scope :: before.stack) exit)
      (enterScope scope env before).2 := by
  cases live : before.cur with
  | none =>
    simp only [Goose.Lower.Validation.enterScope, bind_run, emitEffect_none _ _ live, pushScope_run]
    change ScopeBuilder parents entry exit { before with stack := scope :: before.stack }
    exact valid.closedStack live (scope :: before.stack)
  | some block =>
    have entered := valid.enter scope env block live parent
    have same : (fun other => if other = block then scope :: exit block else exit other) =
        scopeExitUpdate before.cur (scope :: before.stack) exit := by
      funext other
      rw [live, valid.current block live]
      simp [scopeExitUpdate, eq_comm]
    simpa only [same, live, Goose.Lower.Validation.enterScope] using entered

theorem ScopeBuilder.leaveScope {parents : Array (Option ScopeId)}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (valid : ScopeBuilder parents entry exit before) (scope : ScopeId) (rest : List ScopeId)
    (env : LEnv) (stack : before.stack = scope :: rest) :
    ScopeBuilder parents entry (scopeExitUpdate before.cur rest exit)
      (leaveScope scope env before).2 := by
  cases live : before.cur with
  | none =>
    simp only [Goose.Lower.Validation.leaveScope, bind_run, emitEffect_none _ _ live, popScope_run]
    change ScopeBuilder parents entry exit { before with stack := before.stack.drop 1 }
    simpa only [stack, List.drop_succ_cons, List.drop_zero] using valid.closedStack live rest
  | some block =>
    have left := valid.leave scope rest env block live stack
    have same : (fun other => if other = block then rest else exit other) =
        scopeExitUpdate before.cur rest exit := by
      funext other
      simp [scopeExitUpdate, live, eq_comm]
    simpa only [same, live, Goose.Lower.Validation.leaveScope] using left

theorem scopedAction_eq (scope : ScopeId) (inside : B α) :
    scopedAction scope inside = (do
      emitEffect (.enter scope)
      inScope scope (do
        let result ← inside
        emitEffect (.leave scope)
        pure result)) := by
  rfl

theorem ScopeAction.scoped {parents : Array (Option ScopeId)} {parent : Option ScopeId}
    (scope : ScopeId) {inside : B α} (body : ScopeAction parents (some scope) inside)
    (parentAt : parents[scope]?.getD none = parent) :
    ScopeAction parents parent (scopedAction scope inside) := by
  refine ⟨?_, ?_⟩
  · rw [scopedAction_eq]
    exact AdvB.bind (advB_emitEffect _) fun _ => advB_inScope scope
      (AdvB.bind body.advance fun result => AdvB.bind (advB_emitEffect _) fun _ => AdvB.pure result)
  · intro env before entry exit valid bound head
    let entered := (enterScope scope env before).2
    let enteredExit := scopeExitUpdate before.cur (scope :: before.stack) exit
    have enteredState := enterScope_state scope env before
    have enteredValid : ScopeBuilder parents entry enteredExit entered :=
      valid.enterScope scope env (parentAt.trans head.symm)
    have enteredBound : ScopeLiveBound entered := by
      intro block current
      rw [enteredState.2.2]
      exact bound block (enteredState.1.symm.trans current)
    have enteredHead : entered.stack.head? = some scope := by
      rw [enteredState.2.1]
      rfl
    obtain ⟨middleEntry, middleExit, middleValid, middleMaps⟩ :=
      body.preserves env entered entry enteredExit enteredValid enteredBound enteredHead
    have bodyAdvance := body.advance env entered _ _ rfl
    have middleStack : (inside env entered).2.stack = scope :: before.stack :=
      bodyAdvance.stack.trans enteredState.2.1
    have finalValid := middleValid.leaveScope scope before.stack env middleStack
    refine ⟨middleEntry, scopeExitUpdate (inside env entered).2.cur before.stack middleExit,
      finalValid, ?_⟩
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

theorem scope_bind_assoc (first : B α) (next : α → B β) (last : β → B γ) :
    ((first >>= next) >>= last) = (first >>= fun value => next value >>= last) := by
  funext env before
  cases first env before
  rfl

end Goose.Lower.Validation
