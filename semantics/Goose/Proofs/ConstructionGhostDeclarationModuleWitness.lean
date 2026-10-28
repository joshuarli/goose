import Goose.Proofs.ConstructionGhostDeclarationModule

namespace Goose.Proofs.ConstructionGhostDeclarationModuleWitness
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostSyntaxFuel Goose.Proofs.ConstructionGhostStatements Goose.Proofs.ConstructionInvocationReplay
open Goose.Proofs.ConstructionGhostGlobalStep Goose.Proofs.ConstructionGhostGlobalReplay Goose.Proofs.ConstructionGhostCallArguments Goose.Proofs.ConstructionGhostCallActivation
open Goose.Proofs.ConstructionGhostDeclarationReplay Goose.Proofs.ConstructionGhostDeclarationModule
open Goose.Proofs.ConstructionGhostDeclarationOnce
open Goose.Proofs.ConstructionGhostResultScope

private def expression : Expr := .bytes (.varr (.int .u8)) [65, 66] 0
private def statement : Stmt := .letS 0 expression 0
private def descriptor : LocalVar := ⟨"bytes", .varr (.int .u8), .immutable, 0, 0⟩
private def implementation : Impl := ⟨"entry", #[], #[], #[descriptor], .mk 0 [statement] none, .unknown⟩
private def context : Context := ⟨0, "entry", [], [], []⟩
private def config : EvalConfig := ⟨.release, ⟨#[], #[], #[], #[implementation], #[context], 0, #[], #[], #[]⟩⟩
private def activation : RuntimeActivation := ⟨0, 0, implementation.vars, [], []⟩
private def activated : ExecutionState := { ExecutionState.initial with nextAct := 1, activations := [activation] }
private def ready : ExecutionState := resultScopeStart activation 0 activated
private def scopedEnvironment : RuntimeActivation := { activation with scopes := [(0, activated.nextScope)] }
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

private theorem statementSyntax : ∀ child ∈ [statement], StatementSyntax config child := by
  intro child member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst child
  exact .declaration 0 expression 0 (.bytes _ _ _) (.bytes _ _ _)

private theorem closed : ClosedModuleWithTails config := by
  intro contextId actualContext actualImplementation contextFound implementationFound
  cases contextId with
  | zero =>
      have contextEq : actualContext = context := by simpa [config] using contextFound.symm
      subst actualContext
      have implementationEq : actualImplementation = implementation := by simpa [config, context] using implementationFound.symm
      subst actualImplementation
      exact ⟨0, [statement], none, rfl, statementSyntax, .none⟩
  | succ n => simp [config] at contextFound

theorem module_declarationEvents : ∃ outcome visits,
    StatementReplay config scopedEnvironment 37 0 [statement] ready outcome visits ∧ visits ≠ [] ∧
    (∀ visit ∈ visits, ∀ sourceFuel localVar value origin,
      visit.fuel = sourceFuel + 1 → visit.statement = .letS localVar value origin →
      VisitClassification config scopedEnvironment visit sourceFuel localVar value origin) ∧
    runModule 40 config .initial = .ok () (stepState (runModule 40 config .initial)) ∧
    (stepState (runModule 40 config .initial)).construction.events = [.begin 0, .write 0 0, .write 0 1, .publish 0] := by
  have globalSupported : ∀ (global : Goose.Core.GlobalId) (actual : Global),
      config.module.globals[global]? = some actual → ∀ environment, FuelSupport config 40 (.value environment actual.init) := by
    intro global actual found
    simp [config] at found
  have globalDirect : ∀ (global : Goose.Core.GlobalId) (actual : Global),
      config.module.globals[global]? = some actual → actual.ty.nonfixed = true →
      ordinaryProducerCount? 40 ⟨config.module, #[]⟩ actual.init = none →
      ∀ environment destination, SupportedOperation config (.builder environment destination actual.init) := by
    intro global actual found
    simp [config] at found
  obtain ⟨globalOutcome, globalVisits, globalsReplay, moduleExecution, entry⟩ :=
    runModule_declarationVisits 37 config .initial globalSupported globalDirect context implementation rfl rfl rfl
      0 [statement] none rfl closed statementSyntax
  have globalsEq : globalOutcome = .ok [] .initial := by
    have execution := globalsReplay.execute
    simpa [config, List.range_zero, List.mapM.loop, pure] using execution.symm
  have globalsDone : discardGlobalValues globalOutcome = .ok () .initial := by rw [globalsEq]; rfl
  have channels : channelsFor config.layout 0 implementation.results.toList 0 .initial = .ok [] .initial := by
    simp [channelsFor, config, implementation, bind, pure]
  obtain ⟨callExecution, reached⟩ := entry .initial [] .initial globalsDone channels
  have prepared : prepareCallableChannels ⟨0, 0, #[], [], []⟩ [] implementation 0 .initial = .ok [] .initial := by
    simp [prepareCallableChannels, implementation, bind, pure]
  have refresh : refreshCallableChannels [] 0 .initial = .ok [] .initial := by simp [refreshCallableChannels, pure]
  have depth : ExecutionState.initial.activations.length < Goose.Core.maxCallDepth := by simp [ExecutionState.initial, Goose.Core.maxCallDepth]
  obtain ⟨outcome, visits, replay, once, classification, activationExecution⟩ :=
    reached [] .initial [] .initial prepared refresh depth
  refine ⟨outcome, visits, replay, ?_, classification, ?_, ?_⟩
  · intro empty
    subst visits
    cases replay
  · simp only [stepState, config, context, implementation, descriptor, statement, expression]
    cbv
  · simp only [stepState, config, context, implementation, descriptor, statement, expression]
    cbv

private def sourceReady : ExecutionState := stepState (newDestination config.layout 0 descriptor.ty .value 0 none
  (producerCount? ⟨config.module, scopedEnvironment.vars⟩ expression) ready)

theorem module_entryOccurrence : DeclarationOccurrence 35 config scopedEnvironment 0 expression 0 ready (some 0) sourceReady := by
  apply DeclarationOccurrence.direct descriptor (.local 0 0 0) ready implementation ready 0 sourceReady
  all_goals first | exact DeclarationFallback.absent _ rfl | skip
  all_goals simp only [sourceReady, stepState, config, context, implementation, descriptor, scopedEnvironment, activation, activated, ready, statement, expression]
  all_goals cbv

#print axioms module_entryOccurrence
#print axioms module_declarationEvents
end Goose.Proofs.ConstructionGhostDeclarationModuleWitness
