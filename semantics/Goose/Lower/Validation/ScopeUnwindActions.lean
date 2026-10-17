import Goose.Lower.Validation.ScopeActions
import Goose.Lower.Validation.ScopeBlocks

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem leaveAll_none (scopes : List ScopeId) (env : LEnv) (before : LS) (closed : before.cur = none) :
    Goose.Lower.leaveAll scopes env before = ((), before) := by
  induction scopes with
  | nil => rfl
  | cons scope scopes ih =>
    simp only [Goose.Lower.leaveAll, bind_run, emitEffect_none _ _ closed]
    exact ih

theorem leaveTo_none (depth : Nat) (env : LEnv) (before : LS) (closed : before.cur = none) :
    Goose.Lower.leaveTo depth env before = ((), before) := by
  simpa only [Goose.Lower.leaveTo, bind_run, get_apply] using leaveAll_none _ env before closed

theorem leaveAll_size (scopes : List ScopeId) (env : LEnv) (before : LS) :
    (Goose.Lower.leaveAll scopes env before).2.blocks.size = before.blocks.size := by
  induction scopes generalizing before with
  | nil => rfl
  | cons scope scopes ih =>
    rw [Goose.Lower.leaveAll, bind_run]
    cases live : before.cur with
    | none => rw [emitEffect_none _ _ live]; exact ih before
    | some block =>
      rw [emitEffect_run _ _ live]
      dsimp only
      have rest := ih { before with blocks := before.blocks.modify block (fun body => { body with insts := body.insts.push (.eff (.leave scope)) }) }
      simpa only [Array.size_modify] using rest

theorem leaveTo_size (depth : Nat) (env : LEnv) (before : LS) :
    (Goose.Lower.leaveTo depth env before).2.blocks.size = before.blocks.size := by
  simpa only [Goose.Lower.leaveTo, bind_run, get_apply] using leaveAll_size _ env before

theorem emitDef_size (op : Op) (env : LEnv) (before : LS) :
    (Goose.Lower.emitDef op env before).2.blocks.size = before.blocks.size := by
  cases live : before.cur with
  | none => rw [emitDef_none _ _ live]
  | some block => rw [emitDef_run _ _ live]; simp

theorem emitTerm_size (term : Term) (env : LEnv) (before : LS) :
    (Goose.Lower.emitTerm term env before).2.blocks.size = before.blocks.size := by
  cases live : before.cur with
  | none => rw [emitTerm_none _ _ live]
  | some block => rw [emitTerm_run _ _ live]; simp

theorem ScopeBuilder.closeFromTrace {parents : Array (Option ScopeId)}
    {entry exit : BlockId → List ScopeId} {before after : LS}
    (valid : ScopeBuilder parents entry exit before) (advance : before.Adv after)
    (size : after.blocks.size = before.blocks.size) (closed : after.cur = none)
    (out : List ScopeId)
    (appended : ∀ block body afterBody, before.cur = some block →
      before.blocks[block]? = some body → after.blocks[block]? = some afterBody →
      ScopeTrace parents before.stack (afterBody.insts.toList.drop body.insts.size) out) :
    ScopeBuilder parents entry (scopeExitUpdate before.cur out exit) after := by
  constructor
  · intro block afterBody afterLookup
    obtain ⟨afterBound, _⟩ := Array.getElem?_eq_some_iff.mp afterLookup
    have beforeBound : block < before.blocks.size := by rw [← size]; exact afterBound
    let body := before.blocks[block]
    have beforeLookup : before.blocks[block]? = some body :=
      Array.getElem?_eq_some_iff.mpr ⟨beforeBound, rfl⟩
    by_cases current : before.cur = some block
    · have extension := advance.ext.2 block body beforeLookup
      obtain ⟨extended, extendedLookup, params, extra, insts⟩ := extension
      have same : extended = afterBody := Option.some.inj (extendedLookup.symm.trans afterLookup)
      subst extended
      have original := valid.traces block body beforeLookup
      rw [valid.current block current] at original
      have suffix := appended block body afterBody current beforeLookup afterLookup
      have split : afterBody.insts.toList = body.insts.toList ++
          afterBody.insts.toList.drop body.insts.size := by
        rw [insts]
        simp
      simp only [scopeExitUpdate, current, ite_true]
      rw [split]
      exact original.append suffix
    · have kept := advance.keep block body current beforeLookup
      have same : body = afterBody := Option.some.inj (kept.symm.trans afterLookup)
      rw [← same]
      simpa only [scopeExitUpdate, current, ite_false] using valid.traces block body beforeLookup
  · intro block current
    rw [closed] at current
    cases current

theorem ScopeAction.unwindTerm (parents : Array (Option ScopeId)) (parent : Option ScopeId)
    (depth : Nat) (term : Term)
    (termTrace : ∀ stack : List ScopeId,
      ScopeTrace parents (stack.drop (stack.length - depth)) [.term term]
        (stack.drop (stack.length - depth))) :
    ScopeAction parents parent (do Goose.Lower.leaveTo depth; Goose.Lower.emitTerm term) := by
  refine ⟨AdvB.bind (advB_leaveTo depth) (fun _ => advB_emitTerm term), ?_⟩
  intro env before entry exit valid bound head
  cases live : before.cur with
  | none =>
    simp only [bind_run, leaveTo_none _ _ _ live, emitTerm_none _ _ live]
    exact ⟨entry, exit, valid, ScopeMapAdvance.refl _ _ _⟩
  | some block =>
    have earlier := bound block live
    let body := before.blocks[block]
    have lookup : before.blocks[block]? = some body := Array.getElem?_eq_some_iff.mpr ⟨earlier, rfl⟩
    have afterValid := valid.unwindTerm depth term (termTrace before.stack) env block body live lookup
    refine ⟨entry, (fun other => if other = block then before.stack.drop (before.stack.length - depth) else exit other),
      afterValid, ?_⟩
    intro other old
    refine ⟨rfl, ?_⟩
    intro notCurrent
    have distinct : other ≠ block := by intro same; subst other; exact notCurrent live
    simp only [distinct, ite_false]

theorem ScopeAction.unwindBranch (parents : Array (Option ScopeId)) (parent : Option ScopeId)
    (depth : Nat) (target : BlockId) (arguments : List ValueId) :
    ScopeAction parents parent (do Goose.Lower.leaveTo depth; Goose.Lower.emitTerm (.br target arguments)) :=
  ScopeAction.unwindTerm parents parent depth (.br target arguments) (fun _ => .neutral rfl (.nil _))

theorem ScopeAction.unwindReturn (parents : Array (Option ScopeId)) (parent : Option ScopeId)
    (values : List ValueId) (origin : Option OriginId) :
    ScopeAction parents parent (do Goose.Lower.leaveTo 0; Goose.Lower.emitTerm (.ret values origin)) := by
  apply ScopeAction.unwindTerm
  intro stack
  simp only [Nat.sub_zero, List.drop_length]
  exact .ret (.nil [])

def unwindNext (depth : Nat) (type : IntTy) (counter : ValueId) (header : BlockId) : B Unit := do
  Goose.Lower.leaveTo depth
  let next ← Goose.Lower.emitDef (.next type counter)
  Goose.Lower.emitTerm (.br header [next])

theorem ScopeAction.unwindNext (parents : Array (Option ScopeId)) (parent : Option ScopeId)
    (depth : Nat) (type : IntTy) (counter : ValueId) (header : BlockId) :
    ScopeAction parents parent (Goose.Lower.Validation.unwindNext depth type counter header) := by
  have advance : AdvB (Goose.Lower.Validation.unwindNext depth type counter header) :=
    AdvB.bind (advB_leaveTo depth) fun _ => AdvB.bind (advB_emitDef _) fun _ => advB_emitTerm _
  refine ⟨advance, ?_⟩
  intro env before entry exit valid bound head
  let after := (Goose.Lower.Validation.unwindNext depth type counter header env before).2
  have changed := advance env before _ _ rfl
  have size : after.blocks.size = before.blocks.size := by
    simp only [after, Goose.Lower.Validation.unwindNext, bind_run]
    rw [emitTerm_size, emitDef_size, leaveTo_size]
  have isClosed : after.cur = none := by
    have fact := emitTerm_size (.br header []) env before
    simp only [after, Goose.Lower.Validation.unwindNext, bind_run]
    cases live : (Goose.Lower.emitDef (.next type counter) env (Goose.Lower.leaveTo depth env before).2).2.cur with
    | none => rw [emitTerm_none _ _ live]; exact live
    | some block => rw [emitTerm_run _ _ live]
  have afterValid := valid.closeFromTrace changed size isClosed
    (before.stack.drop (before.stack.length - depth)) (by
      intro block body afterBody live lookup afterLookup
      have trace := lowerStmt_continueNext_scopeTrace depth 0 header type counter 0 env before block body live lookup parents
      obtain ⟨_, emittedBody, emittedLookup, emittedTrace⟩ := trace
      have same : emittedBody = afterBody := Option.some.inj (emittedLookup.symm.trans afterLookup)
      subst emittedBody
      exact emittedTrace)
  refine ⟨entry, scopeExitUpdate before.cur (before.stack.drop (before.stack.length - depth)) exit,
    afterValid, ?_⟩
  intro block earlier
  refine ⟨rfl, ?_⟩
  intro other
  simp only [scopeExitUpdate, other, ite_false]

end Goose.Lower.Validation
