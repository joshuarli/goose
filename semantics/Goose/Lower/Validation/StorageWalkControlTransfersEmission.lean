import Goose.Lower.Validation.StorageWalkControlScope
import Goose.Lower.Validation.ScopeUnwindActions

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem storageWalk_continueNext_trace (depth : Nat) (exit header : BlockId)
    (type : IntTy) (counter : ValueId) (origin : OriginId)
    (env : LEnv) (before : LS) (block : BlockId) (body : BlockB)
    (live : before.cur = some block) (lookup : before.blocks[block]? = some body)
    (slots : Array Slot) :
    let after := (lowerStmt (some ⟨depth, exit, .next header type counter⟩) (.cont origin) env before).2
    after.cur = none ∧ ∃ afterBody, after.blocks[block]? = some afterBody ∧
      StorageWalkTrace slots before.stack (afterBody.insts.toList.drop body.insts.size)
        (before.stack.drop (before.stack.length - depth)) := by
  have emitted := leaveTo_emitted depth env before block body live lookup
  dsimp only at emitted ⊢
  have current : (leaveTo depth env before).2.cur = some block := emitted.1.trans live
  simp only [lowerStmt, bind_run]
  have currentNext : (emitDef (.next type counter) env (leaveTo depth env before).2).2.cur = some block := by
    rw [emitDef_run _ _ current]
    exact current
  rw [emitTerm_run _ _ currentNext]
  rw [emitDef_run _ _ current]
  dsimp only
  let leaves : Array Inst := ((before.stack.take (before.stack.length - depth)).map
    fun scope => Inst.eff (.leave scope)).toArray
  let value := (leaveTo depth env before).2.vals.size
  let afterBody : BlockB := { body with insts := ((body.insts ++ leaves).push (.def value (.next type counter))).push (.term (.br header [value])) }
  refine ⟨rfl, afterBody, ?_, ?_⟩
  · simp [afterBody, value, leaves, Array.getElem?_modify, emitted.2.2.2]
  · have trace := (StorageWalkTrace.leaveTo slots before.stack depth).append
      (.neutral (inst := .def (leaveTo depth env before).2.vals.size (.next type counter)) rfl trivial
        (.neutral (inst := .term (.br header [(leaveTo depth env before).2.vals.size])) rfl trivial (.nil _)))
    simpa [afterBody, value, leaves, List.drop_append] using trace

theorem StorageWalkBuilder.closeFromTrace {slots : Array Slot}
    {entry exit : BlockId → List ScopeId} {before after : LS}
    (valid : StorageWalkBuilder slots entry exit before) (advance : before.Adv after)
    (size : after.blocks.size = before.blocks.size) (closed : after.cur = none)
    (out : List ScopeId)
    (appended : ∀ block body afterBody, before.cur = some block →
      before.blocks[block]? = some body → after.blocks[block]? = some afterBody →
      StorageWalkTrace slots before.stack (afterBody.insts.toList.drop body.insts.size) out) :
    StorageWalkBuilder slots entry (scopeExitUpdate before.cur out exit) after := by
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

theorem StorageWalkBuilder.unwindTerm {slots : Array Slot}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (valid : StorageWalkBuilder slots entry exit before) (depth : Nat) (term : Term)
    (termTrace : StorageWalkTrace slots (before.stack.drop (before.stack.length - depth))
      [.term term] (before.stack.drop (before.stack.length - depth)))
    (env : LEnv) (block : BlockId) (body : BlockB)
    (live : before.cur = some block) (lookup : before.blocks[block]? = some body) :
    StorageWalkBuilder slots entry
      (fun other => if other = block then before.stack.drop (before.stack.length - depth) else exit other)
      ((leaveTo depth >>= fun _ => emitTerm term) env before).2 := by
  have emitted := unwindTerm_emitted depth term env before block body live lookup
  dsimp only at emitted
  constructor
  · intro other afterBody afterLookup
    by_cases same : other = block
    · subst other
      rw [emitted.2.2.2] at afterLookup
      cases afterLookup
      simp only [ite_true, Array.toList_push, Array.toList_append ]
      have first := valid.traces block body lookup
      rw [valid.current block live] at first
      exact (first.append (StorageWalkTrace.leaveTo slots before.stack depth)).append termTrace
    · have distinct := Ne.symm same
      rw [unwindTerm_otherBlock depth term env before block other live distinct] at afterLookup
      simpa only [same, ite_false] using valid.traces other afterBody afterLookup
  · intro other current
    rw [emitted.1] at current
    cases current

theorem StorageWalkBuilder.unwindNext {slots : Array Slot}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (valid : StorageWalkBuilder slots entry exit before) (depth : Nat) (type : IntTy)
    (counter : ValueId) (header : BlockId) (env : LEnv) :
    StorageWalkBuilder slots entry (scopeExitUpdate before.cur (before.stack.drop (before.stack.length - depth)) exit)
      (Goose.Lower.Validation.unwindNext depth type counter header env before).2 := by
  let action := Goose.Lower.Validation.unwindNext depth type counter header
  have advance : AdvB action :=
    AdvB.bind (advB_leaveTo depth) fun _ => AdvB.bind (advB_emitDef _) fun _ => advB_emitTerm _
  have size : (action env before).2.blocks.size = before.blocks.size := by
    simp only [action, Goose.Lower.Validation.unwindNext, bind_run]
    rw [emitTerm_size, emitDef_size, leaveTo_size]
  have closed : (action env before).2.cur = none := by
    simp only [action, Goose.Lower.Validation.unwindNext, bind_run]
    cases live : (Goose.Lower.emitDef (.next type counter) env (Goose.Lower.leaveTo depth env before).2).2.cur with
    | none => rw [emitTerm_none _ _ live]; exact live
    | some block => rw [emitTerm_run _ _ live]
  apply valid.closeFromTrace (advance env before _ _ rfl) size closed _
  intro block body afterBody live row afterRow
  have trace := storageWalk_continueNext_trace depth 0 header type counter 0 env before block body live row slots
  obtain ⟨_, emittedBody, emittedRow, emittedTrace⟩ := trace
  have same : emittedBody = afterBody := Option.some.inj (emittedRow.symm.trans afterRow)
  subst emittedBody
  exact emittedTrace


#print axioms storageWalk_continueNext_trace
#print axioms StorageWalkBuilder.closeFromTrace
#print axioms StorageWalkBuilder.unwindTerm
#print axioms StorageWalkBuilder.unwindNext

end Goose.Lower.Validation
