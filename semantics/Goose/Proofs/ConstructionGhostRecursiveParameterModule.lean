import Goose.Proofs.ConstructionGhostSourceFuel
import Goose.Proofs.ConstructionAcceptedEntryInvocation

namespace Goose.Proofs.ConstructionGhostRecursiveParameterModule
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionAcceptedExecution

theorem entryRecursiveParameter_supported (fuel : Nat) (config : EvalConfig)
    (entryContext : Context) (entryImplementation : Impl) (targetId : Goose.Core.ContextId)
    (targetContext : Context) (targetImplementation : Impl) (parameter : Goose.Core.VarId)
    (ty : Goose.Core.IntTy) (number : Int) (entryScope targetScope : Nat)
    (entryStatementOrigin targetCallOrigin targetStatementOrigin : Goose.Core.OriginId)
    (entryFound : config.module.contexts[config.module.entry]? = some entryContext)
    (entryImplementationFound : config.module.impls[entryContext.impl]? = some entryImplementation)
    (entryResults : entryImplementation.results = #[]) (entryParameters : entryImplementation.params = #[])
    (entryBody : entryImplementation.body = .mk entryScope
      [.expr (.call targetId [.byVal (.lit ty number)] targetCallOrigin) entryStatementOrigin] none)
    (targetFound : config.module.contexts[targetId]? = some targetContext)
    (targetImplementationFound : config.module.impls[targetContext.impl]? = some targetImplementation)
    (targetResults : targetImplementation.results = #[]) (targetParameters : targetImplementation.params = #[⟨parameter, .byValue⟩])
    (targetBody : targetImplementation.body = .mk targetScope
      [.expr (.call targetId [.byVal (.lit ty number)] targetCallOrigin) targetStatementOrigin] none) :
    FuelSupport config fuel (.call ⟨0, 0, #[], [], []⟩ config.module.entry 0) := by
  cases fuel with
  | zero => exact .timeout _
  | succ fuel =>
    cases fuel with
    | zero =>
      exact .callOne ⟨0, 0, #[], [], []⟩ config.module.entry 0 entryContext entryImplementation
        entryFound entryImplementationFound entryResults
    | succ fuel =>
      apply FuelSupport.call fuel ⟨0, 0, #[], [], []⟩ config.module.entry 0 entryContext entryImplementation
        entryFound entryImplementationFound entryParameters entryResults
      intro act
      let activation : RuntimeActivation := ⟨entryContext.impl, act, entryImplementation.vars, [], []⟩
      change FuelSupport config (fuel + 1) (.activation activation entryImplementation.body 0)
      rw [entryBody]
      cases fuel with
      | zero => exact .activation 0 activation entryScope _ 0 (.timeout _)
      | succ fuel =>
        apply FuelSupport.activation (fuel + 1)
        apply FuelSupport.activationBody fuel
        intro environment
        cases fuel with
        | zero => exact .timeout _
        | succ fuel =>
          apply FuelSupport.sequence fuel
          · cases fuel with
            | zero => exact .timeout _
            | succ fuel =>
              apply FuelSupport.expression fuel
              cases fuel with
              | zero => exact .timeout _
              | succ fuel =>
                apply FuelSupport.valueCallWith fuel environment targetId [.byVal (.lit ty number)] targetCallOrigin
                  targetContext targetImplementation targetFound targetImplementationFound targetResults
                have targetHistory := recursiveParameter_supported fuel config targetId targetContext targetImplementation
                  parameter ty number targetScope targetCallOrigin targetStatementOrigin targetFound targetImplementationFound
                  targetResults targetParameters targetBody environment
                exact targetHistory
          · exact .legacy fuel (.empty environment)

theorem moduleRecursiveParameter_history (fuel : Nat) (config : EvalConfig)
    (entryContext : Context) (entryImplementation : Impl) (targetId : Goose.Core.ContextId)
    (targetContext : Context) (targetImplementation : Impl) (parameter : Goose.Core.VarId)
    (ty : Goose.Core.IntTy) (number : Int) (entryScope targetScope : Nat)
    (entryStatementOrigin targetCallOrigin targetStatementOrigin : Goose.Core.OriginId)
    (noGlobals : config.module.globals.size = 0)
    (entryFound : config.module.contexts[config.module.entry]? = some entryContext)
    (entryImplementationFound : config.module.impls[entryContext.impl]? = some entryImplementation)
    (entryResults : entryImplementation.results = #[]) (entryParameters : entryImplementation.params = #[])
    (entryBody : entryImplementation.body = .mk entryScope
      [.expr (.call targetId [.byVal (.lit ty number)] targetCallOrigin) entryStatementOrigin] none)
    (targetFound : config.module.contexts[targetId]? = some targetContext)
    (targetImplementationFound : config.module.impls[targetContext.impl]? = some targetImplementation)
    (targetResults : targetImplementation.results = #[]) (targetParameters : targetImplementation.params = #[⟨parameter, .byValue⟩])
    (targetBody : targetImplementation.body = .mk targetScope
      [.expr (.call targetId [.byVal (.lit ty number)] targetCallOrigin) targetStatementOrigin] none) :
    ∃ outcome, SourceHistory config fuel [] (.call ⟨0, 0, #[], [], []⟩ config.module.entry 0) .initial outcome ∧
      runModule fuel config .initial = moduleCallResult outcome := by
  have supported := entryRecursiveParameter_supported fuel config entryContext entryImplementation targetId
    targetContext targetImplementation parameter ty number entryScope targetScope entryStatementOrigin targetCallOrigin targetStatementOrigin
    entryFound entryImplementationFound entryResults entryParameters entryBody targetFound targetImplementationFound
    targetResults targetParameters targetBody
  have history := fuelHistory_exists fuel config _ [] .initial supported
  change SourceHistory config fuel [] (.call ⟨0, 0, #[], [], []⟩ config.module.entry 0) .initial
    (invokeCall fuel config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 .initial) at history
  refine ⟨_, history, ?_⟩
  rw [zeroGlobals_runModule_entry fuel config entryContext entryImplementation noGlobals entryFound entryImplementationFound entryResults]
  simp only [bind, moduleCallResult]
  cases invokeCall fuel config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 .initial <;> rfl

private def entryContext : Context := ⟨0, "entry", [], [], []⟩
private def targetContext : Context := ⟨1, "recursive", [], [], []⟩
private def targetImplementation : Impl := ⟨"recursive", #[⟨0, .byValue⟩], #[],
  #[⟨"n", .int .i64, .immutable, 0, 0⟩], .mk 1 [.expr (.call 1 [.byVal (.lit .i64 1)] 0) 0] none, .unknown⟩
private def entryImplementation : Impl := ⟨"entry", #[], #[], #[],
  .mk 0 [.expr (.call 1 [.byVal (.lit .i64 1)] 0) 0] none, .unknown⟩
private def config : EvalConfig := ⟨.release,
  ⟨#[], #[], #[], #[entryImplementation, targetImplementation], #[entryContext, targetContext], 0, #[], #[], #[]⟩⟩
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

theorem recursiveParameterModule_history (fuel : Nat) : ∃ outcome,
    SourceHistory config fuel [] (.call ⟨0, 0, #[], [], []⟩ 0 0) .initial outcome ∧
      runModule fuel config .initial = moduleCallResult outcome :=
  moduleRecursiveParameter_history fuel config entryContext entryImplementation 1 targetContext targetImplementation 0 .i64 1 0 1 0 0 0
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem recursiveParameterModule_terminal : ∃ state,
    runModule 20 config .initial = .stop .timeout state ∧ 1 < state.nextAct ∧
    ∃ outcome, SourceHistory config 20 [] (.call ⟨0, 0, #[], [], []⟩ 0 0) .initial outcome ∧
      runModule 20 config .initial = moduleCallResult outcome := by
  obtain ⟨outcome, history, execution⟩ := recursiveParameterModule_history 20
  refine ⟨stepState (runModule 20 config .initial), ?_, ?_, outcome, history, execution⟩ <;>
    unfold stepState config entryContext targetContext entryImplementation targetImplementation <;> cbv

#print axioms entryRecursiveParameter_supported
#print axioms moduleRecursiveParameter_history
#print axioms recursiveParameterModule_history
#print axioms recursiveParameterModule_terminal
end Goose.Proofs.ConstructionGhostRecursiveParameterModule
