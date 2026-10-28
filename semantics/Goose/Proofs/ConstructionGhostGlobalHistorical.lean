import Goose.Proofs.ConstructionActivationCounterGlobalHistory
import Goose.Proofs.ConstructionGhostGlobalReplay

namespace Goose.Proofs.ConstructionGhostGlobalHistorical
open Goose.Construct Goose.Proofs.ConstructionGhostGlobalStep Goose.Proofs.ConstructionGhostGlobalReplay
open Goose.Proofs.ConstructionActivationCounter Goose.Proofs.ConstructionActivationCounterGlobals
open Goose.Proofs.ConstructionActivationCounterEvaluation Goose.Proofs.ConstructionActivationCounterGlobalHistory
open Goose.Proofs.ConstructionInvocationReplay Goose.Proofs.ConstructionGhostInvocation

theorem globalInitializer_success_found (fuel : Nat) (config : EvalConfig) (global : Goose.Core.GlobalId)
    (before after : ExecutionState) (completed : globalInitializer fuel config global before = .ok () after) :
    ∃ descriptor, config.module.globals[global]? = some descriptor := by
  cases found : config.module.globals[global]? with
  | none => simp [globalInitializer, found, fault, EvalM.stop] at completed
  | some descriptor => exact ⟨descriptor, rfl⟩

theorem globalReplay_visitLower {fuel : Nat} {config : EvalConfig} {offset : Nat}
    {globals : List Goose.Core.GlobalId} {accumulator : List Unit} {before : ExecutionState}
    {outcome : ExecutionStep (List Unit)} {visits : List (Invocation Goose.Core.GlobalId Unit)}
    (replay : OperandReplay (globalInitializer fuel config) offset globals accumulator before outcome visits)
    (visit : Invocation Goose.Core.GlobalId Unit) (member : visit ∈ visits) :
    before.nextAct ≤ visit.before.nextAct := by
  induction replay with
  | done => simp at member
  | @next offset global rest accumulator before middle value outcome visits head tail ih =>
    have bound := counter_globalInitializer fuel config global (evaluation_preservesActivationCounter fuel config) before
    simp only [head, Goose.Proofs.Exit.stepState] at bound
    simp only [List.mem_cons] at member
    rcases member with same | later
    · subst visit; exact Nat.le_refl _
    · exact Nat.le_trans bound (ih later)
  | stopped | escaped | jumped =>
    simp only [List.mem_singleton] at member
    subst visit
    exact Nat.le_refl _

theorem globalReplay_uniqueActivations {fuel : Nat} {config : EvalConfig} {offset : Nat}
    {globals : List Goose.Core.GlobalId} {accumulator : List Unit} {before : ExecutionState}
    {outcome : ExecutionStep (List Unit)} {visits : List (Invocation Goose.Core.GlobalId Unit)}
    (replay : OperandReplay (globalInitializer fuel config) offset globals accumulator before outcome visits) :
    (visits.map fun visit => visit.before.nextAct).Nodup := by
  induction replay with
  | done => simp
  | @next offset global rest accumulator before middle value outcome visits head tail ih =>
    cases value
    obtain ⟨descriptor, found⟩ := globalInitializer_success_found fuel config global before middle head
    have strict := globalInitializer_nextAct_strict fuel config global before descriptor found
    simp only [head, Goose.Proofs.Exit.stepState] at strict
    simp only [List.map_cons, List.nodup_cons]
    constructor
    · intro repeated
      obtain ⟨visit, member, same⟩ := List.mem_map.mp repeated
      have lower := globalReplay_visitLower tail visit member
      rw [same] at lower
      exact (Nat.not_le_of_gt strict) lower
    · exact ih
  | stopped | escaped | jumped => simp

theorem globalReplay_visitAllocates {fuel : Nat} {config : EvalConfig} {offset : Nat}
    {globals : List Goose.Core.GlobalId} {accumulator : List Unit} {before : ExecutionState}
    {outcome : ExecutionStep (List Unit)} {visits : List (Invocation Goose.Core.GlobalId Unit)}
    (replay : OperandReplay (globalInitializer fuel config) offset globals accumulator before outcome visits)
    (visit : Invocation Goose.Core.GlobalId Unit) (member : visit ∈ visits)
    (descriptor : Global) (found : config.module.globals[visit.operand]? = some descriptor) :
    visit.before.nextAct < (Goose.Proofs.Exit.stepState visit.outcome).nextAct := by
  have strict := globalInitializer_nextAct_strict fuel config visit.operand visit.before descriptor found
  rw [visit_executes replay visit member] at strict
  exact strict

theorem runModule_globalActivationHistory (fuel : Nat) (config : EvalConfig) (before : ExecutionState) :
    ∃ outcome visits,
      OperandReplay (globalInitializer fuel config) 0 (List.range config.module.globals.size) [] before outcome visits ∧
      (visits.map fun visit => visit.before.nextAct).Nodup ∧
      (∀ visit ∈ visits, ∃ descriptor, config.module.globals[visit.operand]? = some descriptor ∧
        visit.before.nextAct < (Goose.Proofs.Exit.stepState visit.outcome).nextAct) ∧
      runModule fuel config before = moduleAfterGlobals fuel config (discardGlobalValues outcome) := by
  obtain ⟨outcome, visits, replay, ordered, once, execution⟩ :=
    initGlobals_replay fuel config (List.range config.module.globals.size) before
  refine ⟨outcome, visits, replay, globalReplay_uniqueActivations replay, ?_, ?_⟩
  · intro visit member
    have visited : visit.operand ∈ visits.map Invocation.operand := List.mem_map.mpr ⟨visit, member, rfl⟩
    rw [ordered] at visited
    have input : visit.operand ∈ List.range config.module.globals.size := List.mem_of_mem_take visited
    have bound : visit.operand < config.module.globals.size := List.mem_range.mp input
    refine ⟨config.module.globals[visit.operand], ?_, ?_⟩
    · simp [bound]
    · exact globalReplay_visitAllocates replay visit member config.module.globals[visit.operand] (by simp [bound])
  · simp only [runModule, bind, execution, moduleAfterGlobals, afterGlobals]
    cases outcome <;> rfl

#print axioms runModule_globalActivationHistory
#print axioms globalReplay_visitLower
#print axioms globalReplay_uniqueActivations
end Goose.Proofs.ConstructionGhostGlobalHistorical
