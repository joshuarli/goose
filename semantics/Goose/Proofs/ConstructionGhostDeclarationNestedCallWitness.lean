import Goose.Proofs.ConstructionGhostCallStatementPaths

namespace Goose.Proofs.ConstructionGhostDeclarationNestedCallWitness
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSyntaxFuel
open Goose.Proofs.ConstructionGhostStatements Goose.Proofs.ConstructionGhostDeclarationReplay
open Goose.Proofs.ConstructionGhostDeclarationNestedCall Goose.Proofs.ConstructionGhostResultScope
open Goose.Proofs.ConstructionGhostCallArguments Goose.Proofs.ConstructionGhostDeclarationOnce
open Goose.Proofs.ConstructionGhostCallStatementPaths Goose.Proofs.ConstructionGhostStatementPaths

private def expression : Expr := .bytes (.varr (.int .u8)) [65, 66] 0
private def statements : List Stmt := [.letS 0 expression 0]
private def descriptor : LocalVar := ⟨"bytes", .varr (.int .u8), .immutable, 0, 0⟩
private def implementation : Impl := ⟨"callee", #[], #[], #[descriptor],
  .mk 0 statements none, .unknown⟩
private def context : Context := ⟨0, "callee", [], [], []⟩
private def config : EvalConfig := ⟨.release, ⟨#[], #[], #[], #[implementation], #[context], 0, #[], #[], #[]⟩⟩
private def caller : RuntimeActivation := ⟨1, 7, #[], [], []⟩
private def before : ExecutionState := { ExecutionState.initial with nextAct := 8, activations := [caller] }
private def activation : RuntimeActivation := ⟨0, 8, implementation.vars, [], []⟩
private def activated : ExecutionState := { before with nextAct := 9, activations := activation :: before.activations }
private def ready : ExecutionState := resultScopeStart activation 0 activated
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

private theorem closed : ClosedModuleWithTails config := by
  intro contextId actualContext actualImplementation contextFound implementationFound
  cases contextId with
  | zero =>
      have same : actualContext = context := by simpa [config] using contextFound.symm
      subst actualContext
      have same : actualImplementation = implementation := by simpa [config, context] using implementationFound.symm
      subst actualImplementation
      refine ⟨0, statements, none, rfl, ?_, .none⟩
      intro statement member
      simp only [statements, List.mem_cons, List.not_mem_nil, or_false] at member
      subst statement
      exact .declaration 0 expression 0 (.bytes _ _ _) (.bytes _ _ _)
  | succ contextId => simp [config] at contextFound

private theorem statementSyntax : ∀ statement ∈ statements, StatementSyntax config statement := by
  intro statement member
  simp only [statements, List.mem_cons, List.not_mem_nil, or_false] at member
  subst statement
  exact .declaration 0 expression 0 (.bytes _ _ _) (.bytes _ _ _)

theorem nestedCall_nonempty : ∃ outcome visits,
    StatementReplay config { activation with scopes := [(0, activated.nextScope)] } 37 0 statements ready outcome visits ∧
    (visits.map StatementInvocation.ordinal).Nodup ∧ visits ≠ [] ∧
    (∀ visit ∈ visits, ∀ sourceFuel localVar value origin,
      visit.fuel = sourceFuel + 1 → visit.statement = .letS localVar value origin →
      VisitClassification config { activation with scopes := [(0, activated.nextScope)] } visit sourceFuel localVar value origin) ∧
    invokeCall 40 config caller 0 [] [] 0 before = .ok [] (stepState (invokeCall 40 config caller 0 [] [] 0 before)) ∧
    (stepState (invokeCall 40 config caller 0 [] [] 0 before)).construction.events =
      [.begin 0, .write 0 0, .write 0 1, .publish 0] := by
  have lookup : getImplementation config 0 before = .ok (0, implementation) before := by
    simp [getImplementation, config, context, bind, pure]
  have prepared : prepareCallableChannels caller [] implementation 0 before = .ok [] before := by
    simp [prepareCallableChannels, implementation, bind, pure]
  have arguments : evalArguments 39 config caller implementation.vars implementation.params.toList [] before = .ok [] before := by
    simp [evalArguments, implementation, pure]
  have refresh : Goose.Proofs.ConstructionGhostCallActivation.refreshCallableChannels [] 0 before = .ok [] before := by
    simp [Goose.Proofs.ConstructionGhostCallActivation.refreshCallableChannels, pure]
  have depth : before.activations.length < Goose.Core.maxCallDepth := by
    simp [before, Goose.Core.maxCallDepth]
  have bound : bindAll activation.act activated.nextScope [] (resultScopeStart activation 0 activated) = .ok () ready := by
    simp [ready, bindAll, bind, pure]
  obtain ⟨outcome, visits, replay, once, bodyExecution, classification, callExecution⟩ :=
    call_declarationVisits 37 config caller 0 [] [] 0 before before before before before ready
      0 implementation [] [] [] lookup rfl prepared arguments refresh depth 0 statements none rfl closed statementSyntax bound
  refine ⟨outcome, visits, replay, once, ?_, classification, ?_, ?_⟩
  · intro empty
    subst visits
    cases replay
  · simp only [stepState, config, caller, before, activation, activated, ready, context, implementation, descriptor, statements, expression]
    cbv
  · simp only [stepState, config, caller, before, activation, activated, ready, context, implementation, descriptor, statements, expression]
    cbv

private def scopedEnvironment : RuntimeActivation := { activation with scopes := [(0, activated.nextScope)] }
private def buildReady : ExecutionState := stepState (newDestination config.layout 8 descriptor.ty .value 0 none
  (producerCount? ⟨config.module, scopedEnvironment.vars⟩ expression) ready)

theorem nestedCall_occurrence : DeclarationOccurrence 35 config scopedEnvironment 0 expression 0 ready (some 0) buildReady ∧
    (Goose.Proofs.Exit.stepState (execStmt 36 config scopedEnvironment (.letS 0 expression 0) ready)).construction.events =
      [.begin 0, .write 0 0, .write 0 1, .publish 0] := by
  constructor
  · apply DeclarationOccurrence.direct descriptor (.local 8 0 0) ready implementation ready 0 buildReady
    · simp [scopedEnvironment, activation, implementation]
    · rfl
    · simp only [rootOf, scopedEnvironment, activation, activated, before, descriptor]
      cbv
    · rfl
    · apply DeclarationFallback.absent
      rfl
    · rfl
    · simp only [buildReady, stepState, config, context, implementation, descriptor, scopedEnvironment, activation, activated, ready, before, caller, statements, expression]
      cbv
  · simp only [config, context, implementation, descriptor, scopedEnvironment, activation, activated, ready, before, caller, statements, expression]
    cbv

#print axioms nestedCall_occurrence
private theorem argumentsSyntax : ∀ id actualImplementation start finish,
    getImplementation config 0 start = .ok (id, actualImplementation) finish →
    ArgumentSyntax config actualImplementation.params.toList [] := by
  intro id actualImplementation start finish lookup
  obtain ⟨actualContext, found, idEq, implFound⟩ := implementation_lookup_source config 0 start finish id actualImplementation lookup
  have contextEq : actualContext = context := by simpa [config] using found.symm
  subst actualContext
  subst id
  have implEq : actualImplementation = implementation := by simpa [config, context] using implFound.symm
  subst actualImplementation
  exact .nil

theorem nestedCall_actualPaths : ∃ outcome visits,
    StatementReplay config scopedEnvironment 37 0 statements ready outcome visits ∧ visits ≠ [] ∧
    (∀ visit ∈ visits, ∃ suffix, StatementPath 0 suffix visit.ordinal ∧
      SourceHistory config visit.fuel ([1, 0, 0] ++ suffix)
        (.statement scopedEnvironment visit.statement) visit.before visit.outcome) ∧
    (∀ visit ∈ visits, ∀ sourceFuel localVar value statementOrigin,
      visit.fuel = sourceFuel + 1 → visit.statement = .letS localVar value statementOrigin →
      ∃ suffix, StatementPath 0 suffix visit.ordinal ∧ ∀ destination sourceReady,
        DeclarationOccurrence sourceFuel config scopedEnvironment localVar value statementOrigin visit.before destination sourceReady →
        match destination with
        | none => SourceHistory config sourceFuel (([1, 0, 0] ++ suffix) ++ [0])
            (.value scopedEnvironment value) sourceReady (evalValue sourceFuel config scopedEnvironment value sourceReady)
        | some destination => SourceHistory config sourceFuel (([1, 0, 0] ++ suffix) ++ [0])
            (.builder scopedEnvironment destination value) sourceReady (buildExpr sourceFuel config scopedEnvironment destination value sourceReady)) := by
  have support := (syntaxFuel_existsWithTails 40 config closed).channelCall caller 0 [] [] 0 argumentsSyntax
  have history := Goose.Proofs.ConstructionGhostSourceFuel.fuelHistory_exists 40 config _ [] before support
  have lookup : getImplementation config 0 before = .ok (0, implementation) before := by
    simp [getImplementation, config, context, bind, pure]
  have prepared : prepareCallableChannels caller [] implementation 0 before = .ok [] before := by
    simp [prepareCallableChannels, implementation, bind, pure]
  have arguments : evalArguments 39 config caller implementation.vars implementation.params.toList [] before = .ok [] before := by
    simp [evalArguments, implementation, pure]
  have refresh : Goose.Proofs.ConstructionGhostCallActivation.refreshCallableChannels [] 0 before = .ok [] before := by
    simp [Goose.Proofs.ConstructionGhostCallActivation.refreshCallableChannels, pure]
  have depth : before.activations.length < Goose.Core.maxCallDepth := by simp [before, Goose.Core.maxCallDepth]
  have bound : bindAll activation.act activated.nextScope [] (resultScopeStart activation 0 activated) = .ok () ready := by
    simp [ready, bindAll, bind, pure]
  obtain ⟨outcome, visits, replay, once, paths, classification, declarationPaths⟩ :=
    call_statementPaths 37 config caller [] 0 [] [] 0 before before before before before ready 0 implementation [] [] []
      history lookup rfl rfl prepared arguments refresh depth 0 statements none rfl closed statementSyntax bound
  refine ⟨outcome, visits, replay, ?_, ?_, ?_⟩
  · intro empty
    subst visits
    cases replay
  · simpa [scopedEnvironment, activation, activated, before] using paths
  · intro visit member sourceFuel localVar value statementOrigin visitFuel visitStatement
    obtain ⟨suffix, suffixPath, children⟩ := declarationPaths visit member sourceFuel localVar value statementOrigin visitFuel visitStatement
    refine ⟨suffix, suffixPath, ?_⟩
    intro destination sourceReady occurrence
    have occurrence' := occurrence
    simp only [scopedEnvironment, activation, activated, before] at occurrence'
    have child := children destination sourceReady occurrence'
    cases destination <;> simpa [scopedEnvironment, activation, activated, before, List.append_assoc] using child

#print axioms nestedCall_actualPaths
#print axioms nestedCall_nonempty
end Goose.Proofs.ConstructionGhostDeclarationNestedCallWitness
