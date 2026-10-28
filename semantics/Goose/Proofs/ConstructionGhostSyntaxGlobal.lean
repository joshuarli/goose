import Goose.Proofs.ConstructionGhostSyntaxFuel
import Goose.Proofs.ConstructionGhostSourceGlobal

namespace Goose.Proofs.ConstructionGhostSyntaxGlobal
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostSyntaxFuel Goose.Proofs.ConstructionGhostSourceGlobal
open Goose.Proofs.ConstructionGhostGlobalStep Goose.Proofs.ConstructionGhostGlobalReplay
open Goose.Proofs.ConstructionInvocationReplay

theorem syntaxModule_globalsAndEntry (fuel : Nat) (config : EvalConfig) (before : ExecutionState)
    (closed : ClosedModule config)
    (globalSyntax : ∀ (global : Goose.Core.GlobalId) (descriptor : Global),
      config.module.globals[global]? = some descriptor → ValueSyntax config descriptor.init)
    (directSupported : ∀ (global : Goose.Core.GlobalId) (descriptor : Global),
      config.module.globals[global]? = some descriptor → descriptor.ty.nonfixed = true →
      ordinaryProducerCount? fuel ⟨config.module, #[]⟩ descriptor.init = none →
      ∀ environment destination, SupportedOperation config (.builder environment destination descriptor.init))
    (entryContext : Context) (entryImplementation : Impl)
    (entryFound : config.module.contexts[config.module.entry]? = some entryContext)
    (entryImplementationFound : config.module.impls[entryContext.impl]? = some entryImplementation)
    (entryResults : entryImplementation.results = #[]) (entryParameters : entryImplementation.params = #[]) :
    ∃ outcome visits,
      OperandReplay (globalInitializer fuel config) 0 (List.range config.module.globals.size) [] before outcome visits ∧
      FixedSourceForest fuel config visits ∧ MaterializedSourceForest fuel config visits ∧ DirectSourceForest fuel config visits ∧
      visits.map Invocation.operand = (List.range config.module.globals.size).take visits.length ∧
      (visits.map Invocation.ordinal).Nodup ∧
      runModule fuel config before = moduleAfterGlobals fuel config (discardGlobalValues outcome) ∧
      ∀ initialized, discardGlobalValues outcome = .ok () initialized →
        SourceHistory config fuel [config.module.globals.size, 0]
          (.callWith ⟨0, 0, #[], [], []⟩ config.module.entry [] 0) initialized
          (invokeCall fuel config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 initialized) ∧
        runModule fuel config before = entryCallResult
          (invokeCall fuel config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 initialized) := by
  obtain ⟨outcome, visits, replay, fixed, ordered, once, execution⟩ := runModule_globalReplay fuel config before
  have fuelSupported := syntaxFuel_exists fuel config closed
  have fixedForest : FixedSourceForest fuel config visits := by
    apply globalReplay_fuelSourceForest replay
    intro global descriptor found fixed environment
    exact fuelSupported.value environment descriptor.init (globalSyntax global descriptor found)
  have materializedForest : MaterializedSourceForest fuel config visits := by
    apply globalReplay_materializedFuelSourceForest replay
    intro global descriptor count found nonfixed materialized environment
    exact fuelSupported.value environment descriptor.init (globalSyntax global descriptor found)
  have directForest := globalReplay_directSourceForest replay directSupported
  refine ⟨outcome, visits, replay, fixedForest, materializedForest, directForest, ordered, once, execution, ?_⟩
  intro initialized globals
  have args : ArgumentSyntax config entryImplementation.params.toList [] := by
    simpa [entryParameters] using (ArgumentSyntax.nil : ArgumentSyntax config [] [])
  have supported := fuelSupported.call ⟨0, 0, #[], [], []⟩ config.module.entry [] 0 entryContext entryImplementation
    entryFound entryImplementationFound entryResults args
  refine ⟨fuelHistory_exists fuel config _ _ initialized supported, ?_⟩
  rw [execution, globals]
  simp only [moduleAfterGlobals, afterGlobals, bind, getImplementation, entryFound, entryImplementationFound, entryResults,
    Array.toList_empty, channelsFor, List.mapM_nil, pure, entryCallResult]
  cases invokeCall fuel config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 initialized <;> rfl

private def entryContext : Context := ⟨0, "entry", [], [], []⟩
private def recursiveContext : Context := ⟨1, "recursive", [], [], []⟩
private def sourceContext : Context := ⟨2, "source", [], [], []⟩
private def entryStatements : List Stmt := [.expr (.call 1 [.byVal (.lit .i64 1)] 0) 0]
private def recursiveStatements : List Stmt := [.print [.text "r"] 0, .expr (.call 1 [.byVal (.lit .i64 1)] 0) 0]
private def sourceStatements : List Stmt := [.print [.text "x"] 0]
private def entryImplementation : Impl := ⟨"entry", #[], #[], #[], .mk 0 entryStatements none, .unknown⟩
private def recursiveImplementation : Impl := ⟨"recursive", #[⟨0, .byValue⟩], #[],
  #[⟨"n", .int .i64, .immutable, 0, 0⟩], .mk 1 recursiveStatements none, .unknown⟩
private def sourceImplementation : Impl := ⟨"source", #[], #[], #[], .mk 2 sourceStatements none, .unknown⟩
private def global : Global := ⟨"fixed", .arr .unit 3, .immutable, .fill (.arr .unit 3) (.call 2 [] 0) 0, 0⟩
private def config : EvalConfig := ⟨.release,
  ⟨#[], #[], #[global], #[entryImplementation, recursiveImplementation, sourceImplementation],
    #[entryContext, recursiveContext, sourceContext], 0, #[], #[], #[]⟩⟩
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

private theorem recursiveCall_syntax : ValueSyntax config (.call 1 [.byVal (.lit .i64 1)] 0) :=
  .call 1 _ 0 recursiveContext recursiveImplementation rfl rfl rfl
    (.value 0 [] (.lit .i64 1) [] (.base (.integer .i64 1)) .nil)

private theorem entryStatements_syntax : ∀ statement ∈ entryStatements, StatementSyntax config statement := by
  intro statement member
  simp only [entryStatements, List.mem_cons, List.not_mem_nil, or_false] at member
  subst statement
  exact .expression _ 0 recursiveCall_syntax

private theorem recursiveStatements_syntax : ∀ statement ∈ recursiveStatements, StatementSyntax config statement := by
  intro statement member
  simp only [recursiveStatements, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact .printText "r" 0
  · exact .expression _ 0 recursiveCall_syntax

private theorem sourceStatements_syntax : ∀ statement ∈ sourceStatements, StatementSyntax config statement := by
  intro statement member
  simp only [sourceStatements, List.mem_cons, List.not_mem_nil, or_false] at member
  subst statement
  exact .printText "x" 0

private theorem closed : ClosedModule config := by
  intro contextId context implementation contextFound implementationFound
  cases contextId with
  | zero =>
      have contextEq : context = entryContext := by simpa [config] using contextFound.symm
      subst context
      have implementationEq : implementation = entryImplementation := by simpa [config, entryContext] using implementationFound.symm
      subst implementation
      exact ⟨0, entryStatements, rfl, entryStatements_syntax⟩
  | succ contextId =>
      cases contextId with
      | zero =>
          have contextEq : context = recursiveContext := by simpa [config] using contextFound.symm
          subst context
          have implementationEq : implementation = recursiveImplementation := by simpa [config, recursiveContext] using implementationFound.symm
          subst implementation
          exact ⟨1, recursiveStatements, rfl, recursiveStatements_syntax⟩
      | succ contextId =>
          cases contextId with
          | zero =>
              have contextEq : context = sourceContext := by simpa [config] using contextFound.symm
              subst context
              have implementationEq : implementation = sourceImplementation := by simpa [config, sourceContext] using implementationFound.symm
              subst implementation
              exact ⟨2, sourceStatements, rfl, sourceStatements_syntax⟩
          | succ contextId => simp [config] at contextFound

private theorem globals_syntax : ∀ (globalId : Goose.Core.GlobalId) (descriptor : Global),
    config.module.globals[globalId]? = some descriptor → ValueSyntax config descriptor.init := by
  intro globalId descriptor found
  have descriptorEq : descriptor = global := by
    cases globalId with
    | zero => simpa [config] using found.symm
    | succ globalId => simp [config] at found
  subst descriptor
  exact .fill .unit 3 (.call 2 [] 0) 0 rfl (.call 2 [] 0 sourceContext sourceImplementation rfl rfl rfl .nil)

private theorem direct_supported (fuel : Nat) : ∀ (globalId : Goose.Core.GlobalId) (descriptor : Global),
    config.module.globals[globalId]? = some descriptor → descriptor.ty.nonfixed = true →
    ordinaryProducerCount? fuel ⟨config.module, #[]⟩ descriptor.init = none →
    ∀ environment destination, SupportedOperation config (.builder environment destination descriptor.init) := by
  intro globalId descriptor found nonfixed direct environment destination
  have descriptorEq : descriptor = global := by
    cases globalId with
    | zero => simpa [config] using found.symm
    | succ globalId => simp [config] at found
  subst descriptor
  simp [global, Ty.nonfixed, Ty.variableElement] at nonfixed

theorem recursiveGlobalModule_history (fuel : Nat) : ∃ outcome visits,
    OperandReplay (globalInitializer fuel config) 0 (List.range config.module.globals.size) [] .initial outcome visits ∧
    FixedSourceForest fuel config visits ∧
    ∀ initialized, discardGlobalValues outcome = .ok () initialized →
      SourceHistory config fuel [config.module.globals.size, 0] (.callWith ⟨0, 0, #[], [], []⟩ 0 [] 0) initialized
        (invokeCall fuel config ⟨0, 0, #[], [], []⟩ 0 [] [] 0 initialized) ∧
      runModule fuel config .initial = entryCallResult
        (invokeCall fuel config ⟨0, 0, #[], [], []⟩ 0 [] [] 0 initialized) := by
  obtain ⟨outcome, visits, replay, fixed, materialized, direct, ordered, once, execution, entry⟩ :=
    syntaxModule_globalsAndEntry fuel config .initial closed globals_syntax (direct_supported fuel)
      entryContext entryImplementation rfl rfl rfl rfl
  exact ⟨outcome, visits, replay, fixed, entry⟩

theorem recursiveGlobalModule_terminal : ∃ state,
    runModule 25 config .initial = .stop .timeout state ∧ 2 < state.nextAct ∧
    2 < state.construction.stdout.data.size ∧
    ∃ outcome visits, OperandReplay (globalInitializer 25 config) 0 (List.range config.module.globals.size) [] .initial outcome visits ∧
      FixedSourceForest 25 config visits ∧
      ∀ initialized, discardGlobalValues outcome = .ok () initialized →
        SourceHistory config 25 [config.module.globals.size, 0] (.callWith ⟨0, 0, #[], [], []⟩ 0 [] 0) initialized
          (invokeCall 25 config ⟨0, 0, #[], [], []⟩ 0 [] [] 0 initialized) ∧
        runModule 25 config .initial = entryCallResult
          (invokeCall 25 config ⟨0, 0, #[], [], []⟩ 0 [] [] 0 initialized) := by
  obtain ⟨outcome, visits, replay, fixed, entry⟩ := recursiveGlobalModule_history 25
  refine ⟨stepState (runModule 25 config .initial), ?_, ?_, ?_, outcome, visits, replay, fixed, entry⟩ <;>
    unfold stepState config entryContext recursiveContext sourceContext entryImplementation recursiveImplementation sourceImplementation
      entryStatements recursiveStatements sourceStatements global <;> cbv

#print axioms recursiveGlobalModule_history
#print axioms recursiveGlobalModule_terminal

#print axioms syntaxModule_globalsAndEntry
end Goose.Proofs.ConstructionGhostSyntaxGlobal
