import Goose.Lower.Validation.SourceReadyTypedStatementsPreSlots

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.Core.Sound Goose.GIR.ReplacementContentFlow.Model

theorem typed_ready_if {state : State} {before : LS} {typingEnv output : TEnv} {results : List Ty}
    {loop : Option LoopCtx} {scope start finish : Nat} {origin : OriginId}
    {condition : Expr} {yes : Core.Block} {no : Option Core.Block}
    (source : Core.tyStmt typingEnv scope (.ifS condition yes no origin) start = .ok (output, finish))
    (visible : VisibleSlotsReady typingEnv state)
    (conditionChild : ∀ next, Core.tyExpr typingEnv condition start = .ok (.bool, next) →
      ValueReadyAt state (lowerExpr condition) (lowerEnv typingEnv.mod typingEnv.vars results) before)
    (yesChild : ∀ type next last, Core.tyBlock typingEnv [] yes next = .ok (type, last) →
      let env := lowerEnv typingEnv.mod typingEnv.vars results
      let evaluated := lowerExpr condition env before
      let forked := fork evaluated.1 env evaluated.2
      let selected := { forked.2 with cur := some forked.1.1 }
      evaluated.2.cur.isSome = true → EmitsOnly (ReadyOperands state) selected (lowerBlock loop [] false yes env selected).2)
    (noChild : ∀ body type next, no = some body → Core.tyBlock typingEnv [] body next = .ok (type, finish) →
      let env := lowerEnv typingEnv.mod typingEnv.vars results
      let evaluated := lowerExpr condition env before
      let forked := fork evaluated.1 env evaluated.2
      let selectedT := { forked.2 with cur := some forked.1.1 }
      let doneT := lowerBlock loop [] false yes env selectedT
      let selectedF := { doneT.2 with cur := some forked.1.2 }
      evaluated.2.cur.isSome = true → EmitsOnly (ReadyOperands state) selectedF (lowerBlock loop [] false body env selectedF).2) :
    EmitsOnly (ReadyOperands state) before
      (lowerStmt loop (.ifS condition yes no origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.ifS condition yes no origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true →
        VisibleSlotsReady output state) := by
  obtain ⟨next, yesType, yesFinish, conditionSource, yesSource, noSource, outputEq⟩ := tyStmt_if_children source
  subst output
  have conditionReady := conditionChild next conditionSource
  cases no with
  | none =>
    have branching := ready_ifThen conditionReady.2 (yesChild yesType next yesFinish yesSource)
    exact ⟨conditionReady.1.trans branching, fun _ => visible⟩
  | some body =>
    obtain ⟨noType, noChecked⟩ := noSource
    have branching := ready_ifArms conditionReady.2 (by
      intro live
      exact ⟨yesChild yesType next yesFinish yesSource live, noChild body noType yesFinish rfl noChecked live⟩)
    exact ⟨conditionReady.1.trans branching, fun _ => visible⟩

theorem typed_ready_while {state : State} {before : LS} {typingEnv output : TEnv} {results : List Ty}
    {loop : Option LoopCtx} {scope start finish : Nat} {origin : OriginId}
    {condition : Expr} {body : Core.Block}
    (source : Core.tyStmt typingEnv scope (.while condition body origin) start = .ok (output, finish))
    (visible : VisibleSlotsReady typingEnv state)
    (conditionChild : ∀ next, Core.tyExpr typingEnv condition start = .ok (.bool, next) →
      let env := lowerEnv typingEnv.mod typingEnv.vars results
      let created := newBlock [] env before
      let closed := (emitTerm (.br created.1.1 []) env created.2).2
      ValueReadyAt state (lowerExpr condition) env { closed with cur := some created.1.1 })
    (bodyChild : ∀ type next,
      Core.tyBlock { typingEnv with loops := typingEnv.loops + 1 } [] body next = .ok (type, finish) →
      VisibleSlotsReady { typingEnv with loops := typingEnv.loops + 1 } state →
      let env := lowerEnv typingEnv.mod typingEnv.vars results
      let created := newBlock [] env before
      let closed := (emitTerm (.br created.1.1 []) env created.2).2
      let started := { closed with cur := some created.1.1 }
      let evaluated := lowerExpr condition env started
      let forked := fork evaluated.1 env evaluated.2
      let selected := { forked.2 with cur := some forked.1.1 }
      evaluated.2.cur.isSome = true →
      EmitsOnly (ReadyOperands state) selected
        (lowerBlock (some ⟨evaluated.2.stack.length, forked.1.2, .jump created.1.1⟩) [] false body env selected).2) :
    EmitsOnly (ReadyOperands state) before
      (lowerStmt loop (.while condition body origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 ∧
      ((lowerStmt loop (.while condition body origin) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.cur.isSome = true →
        VisibleSlotsReady output state) := by
  obtain ⟨next, bodyType, conditionSource, bodySource, outputEq⟩ := tyStmt_while_children source
  subst output
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let created := newBlock [] env before
  let closed := (emitTerm (.br created.1.1 []) env created.2).2
  let started := { closed with cur := some created.1.1 }
  have conditionReady := conditionChild next conditionSource
  have bodyReady := bodyChild bodyType next bodySource visible
  have loopReady := ready_lowerWhile (header := created.1.1)
    (body := fun depth exit => lowerBlock (some ⟨depth, exit, .jump created.1.1⟩) [] false body)
    conditionReady bodyReady
  have newReady := emitsOnly_newBlock (ReadyOperands state) [] env before created.1 created.2 rfl
  have closedReady : EmitsOnly (ReadyOperands state) created.2 closed := ready_emitTerm (env := env) rfl (by
    intro _ operand member
    simp [Inst.uses, Term.uses] at member)
  have startReady : EmitsOnly (ReadyOperands state) closed started := .of_blocks rfl
  exact ⟨newReady.trans (closedReady.trans (startReady.trans loopReady)), fun _ => visible⟩

end Goose.Lower.Validation.ReplacementContentFlowSource
