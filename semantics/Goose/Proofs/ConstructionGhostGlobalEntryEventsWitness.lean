import Goose.Proofs.ConstructionGhostGlobalEntryEvents

namespace Goose.Proofs.ConstructionGhostGlobalEntryEventsWitness
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostStatements Goose.Proofs.ConstructionGhostStatementEvents
open Goose.Proofs.ConstructionGhostInvocationEventChunks Goose.Proofs.ConstructionGhostMaterializedDeclarationEvents
open Goose.Proofs.ConstructionGhostModuleInitializerEvents Goose.Proofs.ConstructionGhostGlobalEntryEvents
open Goose.Proofs.ConstructionGhostGlobalStep Goose.Proofs.ConstructionGhostGlobalReplay
open Goose.Proofs.ConstructionInvocationReplay

private def context : Context := ⟨0, "entry", [], [], []⟩
private def bytes : Expr := .bytes (.varr (.int .u8)) [65, 66] 0
private def element : Expr := .len (.val bytes)
private def materialized : Expr := .values [.arrLit (.arr (.int .i64) 1) [element] 0]
private def fixedVar : LocalVar := ⟨"fixed", .int .i64, .immutable, 0, 0⟩
private def dynamicVar : LocalVar := ⟨"dynamic", .varr (.int .i64), .immutable, 0, 0⟩
private def statements : List Stmt := [.letS 0 element 0, .letS 1 materialized 0]
private def implementation : Impl := ⟨"entry", #[], #[], #[fixedVar, dynamicVar], .mk 0 statements none, .unknown⟩
private def global : Global := ⟨"bytes", .varr (.int .u8), .immutable, bytes, 0⟩
private def config : EvalConfig := ⟨.release,
  ⟨#[], #[], #[global], #[implementation], #[context], 0, #[], #[], #[]⟩⟩
private def activation : RuntimeActivation := ⟨0, 0, #[fixedVar, dynamicVar], [], []⟩
private def activated : ExecutionState := { ExecutionState.initial with nextAct := 1, activations := [activation] }
private def scopedEnvironment : RuntimeActivation := { activation with scopes := [(0, 0)] }
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

private theorem supported : ∀ act scopeInst sourceFuel id expr origin, .letS id expr origin ∈ statements →
    FuelSupport config sourceFuel (.value ⟨0, act, implementation.vars, [(0, scopeInst)], []⟩ expr) := by
  intro act scopeInst sourceFuel id expr origin member
  simp only [statements, List.mem_cons, List.not_mem_nil, or_false] at member
  have elementSupport : SupportedOperation config (.value ⟨0, act, implementation.vars, [(0, scopeInst)], []⟩ element) :=
    .lengthValue _ (.val bytes) (.valueView _ bytes (.valueBytes _ (.varr (.int .u8)) [65, 66] 0))
  rcases member with same | same
  · cases same
    exact .legacy sourceFuel elementSupport
  · cases same
    apply FuelSupport.legacy
    apply SupportedOperation.singleton ⟨0, act, implementation.vars, [(0, scopeInst)], []⟩ (.arrLit (.arr (.int .i64) 1) [element] 0)
    apply SupportedOperation.aggregate ⟨0, act, implementation.vars, [(0, scopeInst)], []⟩ (.arrLit (.arr (.int .i64) 1) [element] 0) [element]
      (.fixedArray (.arr (.int .i64) 1) [element] 0 rfl)
    intro operand inOperands
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inOperands
    subst operand
    exact elementSupport

private theorem globalDescriptor (id : Goose.Core.GlobalId) (descriptor : Global)
    (found : config.module.globals[id]? = some descriptor) : descriptor = global := by
  cases id with
  | zero => simpa [config] using found.symm
  | succ n => simp [config] at found

private theorem globalSupported : ∀ (id : Goose.Core.GlobalId) (descriptor : Global),
    config.module.globals[id]? = some descriptor → ∀ environment,
    FuelSupport config 50 (.value environment descriptor.init) := by
  intro id descriptor found environment
  have same := globalDescriptor id descriptor found
  subst descriptor
  exact .legacy 50 (.valueBytes environment (.varr (.int .u8)) [65, 66] 0)

private theorem directSupported : ∀ (id : Goose.Core.GlobalId) (descriptor : Global),
    config.module.globals[id]? = some descriptor → descriptor.ty.nonfixed = true →
    ordinaryProducerCount? 50 ⟨config.module, #[]⟩ descriptor.init = none →
    ∀ environment destination, SupportedOperation config (.builder environment destination descriptor.init) := by
  intro id descriptor found nonfixed direct environment destination
  have same := globalDescriptor id descriptor found
  subst descriptor
  exact .builderBytes environment destination (.varr (.int .u8)) [65, 66] 0

theorem globalAndEntry_nonempty : ∃ globalOutcome globalVisits globalChunks initialized entryOutcome entryVisits entryChunks final,
    OperandReplay (globalInitializer 50 config) 0 [0] [] .initial globalOutcome globalVisits ∧
    ChunksAlign globalVisits globalChunks ∧ globalChunks.flatten ≠ [] ∧
    discardGlobalValues globalOutcome = .ok () initialized ∧
    let activation : RuntimeActivation := ⟨0, initialized.nextAct, implementation.vars, [], []⟩
    let activated := { initialized with nextAct := initialized.nextAct + 1, activations := activation :: initialized.activations }
    let ready := Goose.Proofs.ConstructionGhostResultScope.resultScopeStart activation 0 activated
    let scopedEnvironment := { activation with scopes := [(0, activated.nextScope)] }
    StatementReplay config scopedEnvironment 47 0 statements ready entryOutcome entryVisits ∧
    (entryVisits.map StatementInvocation.ordinal).Nodup ∧ ChunksAlign (entryVisits.map statementInvocation) entryChunks ∧
    FixedVisitSourceEvents config scopedEnvironment entryVisits ∧ MaterializedVisitSourceEvents config scopedEnvironment entryVisits ∧
    entryChunks.flatten ≠ [] ∧ runModule 50 config .initial = .ok () final ∧ final.construction.events ≠ [] := by
  obtain ⟨globalOutcome, globalVisits, globalChunks, replay, globalFixed, globalMaterialized, globalDirect,
    ordered, once, aligned, finalEq, moduleExecution, entry⟩ :=
    runModule_globalAndEntryEvents 47 config .initial globalSupported directSupported context implementation rfl rfl rfl rfl
      0 statements none rfl supported
  let initialized := stepState (globalInitializer 50 config 0 .initial)
  have globalActual : globalInitializer 50 config 0 .initial = .ok () initialized := by
    unfold initialized stepState globalInitializer config global bytes context implementation fixedVar dynamicVar statements materialized element
    cbv
  let globalVisit : Invocation Goose.Core.GlobalId Unit := ⟨0, 0, .initial, .ok () initialized⟩
  have knownReplay : OperandReplay (globalInitializer 50 config) 0 [0] [] .initial (.ok [()] initialized) [globalVisit] :=
    .next globalActual (.done 1 [()] initialized)
  have globalEq : globalOutcome = .ok [()] initialized := by
    have actualReplay : OperandReplay (globalInitializer 50 config) 0 [0] [] .initial globalOutcome globalVisits := by
      simpa [config] using replay
    exact actualReplay.execute.symm.trans knownReplay.execute
  have globalsDone : discardGlobalValues globalOutcome = .ok () initialized := by rw [globalEq]; rfl
  have depth : initialized.activations.length < Goose.Core.maxCallDepth := by
    unfold initialized stepState globalInitializer config global bytes context implementation fixedVar dynamicVar statements materialized element
    cbv
  obtain ⟨moduleCall, reached⟩ := entry initialized globalsDone
  obtain ⟨entryOutcome, entryVisits, entryChunks, entryReplay, entryOrdered, entryOnce, entryAligned, entryFinal,
    fixed, materializedEvents, callExecution⟩ := reached depth
  refine ⟨globalOutcome, globalVisits, globalChunks, initialized, entryOutcome, entryVisits, entryChunks,
    stepState (runModule 50 config .initial), ?_, aligned, ?_, globalsDone, entryReplay, entryOnce, entryAligned, fixed,
    materializedEvents, ?_, ?_, ?_⟩
  · simpa [config] using replay
  · have prefixEq : (Goose.Proofs.Exit.stepState globalOutcome).construction.events = globalChunks.flatten := by
      simpa [ExecutionState.initial, ConstructionState.initial] using finalEq
    rw [← prefixEq, globalEq]
    intro empty
    unfold initialized stepState globalInitializer config global bytes context implementation fixedVar dynamicVar statements materialized element at empty
    cbv at empty
    cases empty
  · intro empty
    have finalEvents := entryFinal
    simp only [empty, List.flatten_nil, List.append_nil] at finalEvents
    rw [← entryReplay.sound] at finalEvents
    unfold initialized stepState globalInitializer config global bytes context implementation fixedVar dynamicVar statements materialized element at finalEvents
    cbv at finalEvents
    all_goals try (unfold evalValue at finalEvents; cbv at finalEvents)
    all_goals try (unfold evalValue at finalEvents; cbv at finalEvents)
    all_goals try (unfold evalValue at finalEvents; cbv at finalEvents)
    all_goals cases finalEvents
  · unfold stepState config global context implementation fixedVar dynamicVar statements materialized element bytes
    cbv
    all_goals try (unfold evalValue; cbv)
    all_goals try (unfold evalValue; cbv)
    all_goals try (unfold evalValue; cbv)
  · intro empty
    unfold stepState config global context implementation fixedVar dynamicVar statements materialized element bytes at empty
    cbv at empty
    all_goals try (unfold evalValue at empty; cbv at empty)
    all_goals try (unfold evalValue at empty; cbv at empty)
    all_goals try (unfold evalValue at empty; cbv at empty)
    all_goals cases empty

#print axioms globalAndEntry_nonempty
end Goose.Proofs.ConstructionGhostGlobalEntryEventsWitness
