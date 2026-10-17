import Goose.Lower.Validation.SourceReadyControlJoin

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem emitTerm_member {env : LEnv} {before : LS} {term : Term} {block : BlockId}
    (current : before.cur = some block) (bounded : block < before.blocks.size) :
    Inst.term term ∈ (emitTerm term env before).2.insts := by
  rw [emitTerm_run _ _ current]
  exact patchTerm_member (env := env) bounded

theorem SourceReadyFrame.conditionalParameter {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed fragment : LS}
    {condition : ValueId} {yes no : BlockId} {yesArgs noArgs : List ValueId}
    {target : BlockId} {args : List ValueId} {body : BlockB}
    {parameter : ValueId × VTy} {argument : ValueId}
    (frame : SourceReadyFrame module callees func types state completed)
    (extension : fragment.Ext completed)
    (member : Inst.term (.condbr condition yes yesArgs no noArgs) ∈ fragment.insts)
    (selected : (target = yes ∧ args = yesArgs) ∨ (target = no ∧ args = noArgs))
    (targetRow : fragment.blocks[target]? = some body)
    (binding : (parameter, argument) ∈ body.params.zip args)
    (bounded : parameter.1 < state.values.size) (available : flowAt state.values argument ≠ .pending) :
    flowAt state.values parameter.1 ≠ .pending := by
  obtain ⟨finalBody, finalRow, parameters, _⟩ := extension.2 target body targetRow
  let finalBlock : GIR.Block := ⟨finalBody.params, finalBody.insts.toList⟩
  have row : func.blocks[target]? = some finalBlock := by
    rw [frame.blocks]
    simp only [finishBlocks, Array.getElem?_map, finalRow, Option.map_some]
    rfl
  have paired : (parameter, argument) ∈ finalBlock.params.zip args := by simpa [finalBlock, parameters] using binding
  have fixed := frame.fixed_instruction extension member
  change edge func (edge func state yes yesArgs) no noArgs = state at fixed
  rcases selected with ⟨selectedTarget, selectedArgs⟩ | ⟨selectedTarget, selectedArgs⟩
  all_goals subst target args
  · have ready := edge_parameter_ready row paired bounded available
    have growth := edge_extends func (edge func state yes yesArgs) no noArgs
    have final := (growth.values.values parameter.1).ready ready
    rwa [fixed] at final
  · have growth := edge_extends func state yes yesArgs
    have ready := edge_parameter_ready row paired (by simpa only [← growth.values.size] using bounded)
      ((growth.values.values argument).ready available)
    rwa [fixed] at ready

theorem SourceReadyFrame.scFork {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before : LS} {env : LEnv}
    {isAnd : Bool} {condition : ValueId}
    (frame : SourceReadyFrame module callees func types state completed)
    (extension : (Goose.Lower.scFork isAnd condition env before).2.Ext completed)
    (allocated : before.vals.size < completed.vals.size) (bounded : LiveBound before)
    (live : before.cur.isSome = true) (available : flowAt state.values condition ≠ .pending) :
    EmitsOnly (ReadyOperands state) before (Goose.Lower.scFork isAnd condition env before).2 ∧
      flowAt state.values (Goose.Lower.scFork isAnd condition env before).1.2.2 ≠ .pending := by
  let first := newBlock [] env before
  let second := newBlock [.data .bool] env first.2
  let term := scTerm isAnd condition first.1.1 second.1.1
  let closed := (emitTerm term env second.2).2
  have one := emitsOnly_newBlock (ReadyOperands state) [] env before first.1 first.2 rfl
  have two := emitsOnly_newBlock (ReadyOperands state) [.data .bool] env first.2 second.1 second.2 rfl
  have termReady : ∀ value ∈ term.uses, flowAt state.values value ≠ .pending := by
    intro value member
    have same : value = condition := by cases isAnd <;> simpa [term, scTerm, Inst.uses, Term.uses] using member
    subst value
    exact available
  have closedReady := ready_emitTerm (show emitTerm term env second.2 = ((), closed) from rfl) (fun _ => termReady)
  have emissions : EmitsOnly (ReadyOperands state) before closed := one.trans (two.trans closedReady)
  have closedEq : (Goose.Lower.scFork isAnd condition env before).2 = closed := by
    cases isAnd <;> rfl
  have closedExtension : closed.Ext completed := closedEq ▸ extension
  have current : ∃ block, before.cur = some block := Option.isSome_iff_exists.mp live
  obtain ⟨block, current⟩ := current
  have secondCurrent : second.2.cur = some block := current
  have secondBound : block < second.2.blocks.size := by
    have old := bounded block current
    simp only [second, first, newBlock0_run, newBlock1_run, Array.size_push]
    nat_omega
  have member := emitTerm_member (env := env) (term := term) secondCurrent secondBound
  have initialRow : second.2.blocks[before.blocks.size + 1]? = some ⟨[(before.vals.size, .data .bool)], #[]⟩ := by
    change (before.blocks.push ⟨[], #[]⟩ |>.push ⟨[(before.vals.size, .data .bool)], #[]⟩)[before.blocks.size + 1]? = _
    simp only [Array.getElem?_push, Array.size_push, Nat.lt_irrefl, ↓reduceIte, beq_self_eq_true]
  obtain ⟨body, bodyRow, bodyParams, _⟩ := closedReady.extension.2 _ _ initialRow
  have actualBodyRow : closed.blocks[second.1.1]? = some body := by simpa only [second, first, newBlock0_run, newBlock1_run, Array.size_push] using bodyRow
  have valueBound : before.vals.size < state.values.size := by rw [frame.shape.values, ← frame.values]; exact allocated
  have ready : flowAt state.values before.vals.size ≠ .pending := by
    cases isAnd
    · exact frame.conditionalParameter closedExtension member (Or.inl ⟨rfl, rfl⟩) actualBodyRow
        (parameter := (before.vals.size, .data .bool)) (by simp [bodyParams]) valueBound available
    · exact frame.conditionalParameter closedExtension member (Or.inr ⟨rfl, rfl⟩) actualBodyRow
        (parameter := (before.vals.size, .data .bool)) (by simp [bodyParams]) valueBound available
  refine ⟨closedEq ▸ emissions, ?_⟩
  rw [scFork_run _ _ env current]
  exact ready

theorem SourceReadyFrame.shortCircuit {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {completed before : LS} {env : LEnv}
    {isAnd : Bool} {condition : ValueId} {rhs : B ValueId}
    (frame : SourceReadyFrame module callees func types state completed)
    (bounded : LiveBound before) (advance : AdvB rhs)
    (available : before.cur.isSome = true → flowAt state.values condition ≠ .pending)
    (child : before.cur.isSome = true →
      let forked := Goose.Lower.scFork isAnd condition env before
      ValueReadyAt state rhs env { forked.2 with cur := some forked.1.1 })
    (extension : (Goose.Lower.shortCircuit isAnd condition rhs env before).2.Ext completed)
    (allocated : before.cur.isSome = true → before.vals.size < completed.vals.size) :
    ValueReadyAt state (Goose.Lower.shortCircuit isAnd condition rhs) env before := by
  cases current : before.cur with
  | none =>
    simp only [ValueReadyAt, Goose.Lower.shortCircuit, whenLive_none _ _ _ current]
    exact ⟨.refl _ _, by simp [current]⟩
  | some block =>
    have live : before.cur.isSome = true := by simp [current]
    let forked := Goose.Lower.scFork isAnd condition env before
    let started := { forked.2 with cur := some forked.1.1 }
    let evaluated := rhs env started
    let closed := (emitTerm (.br forked.1.2.1 [evaluated.1]) env evaluated.2).2
    have childReady := child live
    have closedReady : EmitsOnly (ReadyOperands state) evaluated.2 closed := ready_emitTerm rfl (by
      intro active value member
      have same : value = evaluated.1 := by simpa [Inst.uses, Term.uses] using member
      subst value
      exact childReady.2 active)
    have forkExtension : forked.2.Ext completed := by
      have initial : forked.2.Ext started := (EmitsOnly.of_blocks (property := ReadyOperands state) rfl).extension
      have evaluatedExt := (advance env started _ _ rfl).ext
      have finalExt : closed.Ext (Goose.Lower.shortCircuit isAnd condition rhs env before).2 := by
        apply (EmitsOnly.of_blocks (property := ReadyOperands state) ?_).extension
        simp only [Goose.Lower.shortCircuit, whenLive_some _ _ _ current, bind_run, setCur_run,
          pure_run, forked, started, evaluated, closed]
      exact initial.trans (evaluatedExt.trans (closedReady.extension.trans (finalExt.trans extension)))
    have forkReady := frame.scFork forkExtension (allocated live) bounded live (available live)
    refine ⟨?_, ?_⟩
    · have startedReady : EmitsOnly (ReadyOperands state) forked.2 started := .of_blocks rfl
      have allReady := forkReady.1.trans (startedReady.trans (childReady.1.trans closedReady))
      have finalReady : EmitsOnly (ReadyOperands state) closed { closed with cur := some forked.1.2.1 } := .of_blocks rfl
      simpa only [Goose.Lower.shortCircuit, whenLive_some _ _ _ current, bind_run, setCur_run,
        pure_run, forked, started, evaluated, closed] using allReady.trans finalReady
    · intro _
      simpa only [Goose.Lower.shortCircuit, whenLive_some _ _ _ current, bind_run, setCur_run,
        pure_run, forked, started, evaluated, closed] using forkReady.2

#print axioms SourceReadyFrame.shortCircuit

#print axioms emitTerm_member
#print axioms SourceReadyFrame.conditionalParameter
#print axioms SourceReadyFrame.scFork

end Goose.Lower.Validation.ReplacementContentFlowSource
