import Goose.Proofs.ConstructionByteModuleCompletedWorld

namespace Goose.Proofs.ConstructionAcceptedExecution

open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem acceptedEntry_lowFuel_afterGlobals (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (initialized : ExecutionState) (live : Goose.Core.RootInst → Prop)
    (world : AcceptedWorld config config.module.globals.size initialized [] (declaredRootTypes config.module) live [] [])
    (globals : initGlobals fuel config (List.range config.module.globals.size) .initial = .ok () initialized)
    (low : fuel < 3) :
    ∃ after ambient,
      runModule fuel config .initial = .stop .timeout after ∧
      AcceptedWorld config config.module.globals.size after ambient (declaredRootTypes config.module) live [] [] := by
  obtain ⟨original, implementation, originalAt, implementationAt, parameters, results⟩ :=
    validated_entry config.module accepted.accepted
  let activation : RuntimeActivation := ⟨original.impl, initialized.nextAct, implementation.vars, [], []⟩
  have depth : initialized.activations.length < Goose.Core.maxCallDepth := by
    have runtime := world.ownership.runtime.activations
    cases active : initialized.activations with
    | nil => simp [Goose.Core.maxCallDepth]
    | cons head tail => simp [active, OwnershipAmbient.activations] at runtime
  have pushed := acceptedWorld_pushEmptyActivation config config.module.globals.size initialized []
    (declaredRootTypes config.module) live [] [] activation world rfl rfl
  cases fuel with
  | zero =>
    refine ⟨initialized, [], ?_, world⟩
    simp [runModule, globals, getImplementation, originalAt, implementationAt, results, channelsFor, invokeCall, timeout, EvalM.stop, bind, pure]
  | succ fuel =>
    cases fuel with
    | zero =>
      refine ⟨initialized, [], ?_, world⟩
      simp [runModule, globals, getImplementation, originalAt, implementationAt, results, parameters, channelsFor,
        invokeCall, evalArguments, timeout, EvalM.stop, bind, pure]
    | succ fuel =>
      have zero : fuel = 0 := by omega
      subst fuel
      have notDepth : ¬ Goose.Core.maxCallDepth ≤ initialized.activations.length := by omega
      refine ⟨{ initialized with nextAct := initialized.nextAct + 1, activations := activation :: initialized.activations },
        [.callChannels activation []], ?_, pushed⟩
      simp [runModule, globals, getImplementation, originalAt, implementationAt, results, parameters, channelsFor,
        invokeCall, evalArguments, freshAct, EvalM.get, EvalM.set, enterActivation, execActivationBody, finishActivation,
        timeout, EvalM.stop, bind, pure, notDepth, activation]

theorem acceptedByteModule_lowFuel (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (declarations : ∀ id, id < config.module.globals.size →
      ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
        descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin)
    (low : fuel < 3) :
    ∃ stop after initialized ambient types live regions,
      runModule fuel config .initial = .stop stop after ∧
      AcceptedWorld config initialized after ambient types live regions [] := by
  obtain ⟨completed, live, regions, bound, world, final⟩ :=
    initGlobals_byteOwners_initial_complete fuel config accepted declarations
  cases globals : initGlobals fuel config (List.range config.module.globals.size) .initial with
  | stop stop after =>
    simp only [globals, Goose.Proofs.Exit.stepState] at world final
    exact ⟨stop, after, completed, [], declaredRootTypes config.module, live, regions, final.2, world⟩
  | ok value after =>
    cases value
    simp only [globals, Goose.Proofs.Exit.stepState] at world final
    obtain ⟨completedEq, regionsEq, clear⟩ := final
    subst completed
    subst regions
    obtain ⟨stopped, ambient, moduleStop, finalWorld⟩ :=
      acceptedEntry_lowFuel_afterGlobals fuel config accepted after live world globals low
    exact ⟨.timeout, stopped, config.module.globals.size, ambient, declaredRootTypes config.module, live, [], moduleStop, finalWorld⟩
  | escape target carriers after | jump target kind after =>
    simp only [globals] at final

theorem acceptedByteModule_allFuel (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (declarations : List ByteOwnerDeclaration) (original : Context) (implementation : Impl)
    (globals : ∀ id, id < config.module.globals.size →
      ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
        descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin)
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (body : implementation.body.stmts = declarations.map ByteOwnerDeclaration.statement)
    (tail : implementation.body.value = none)
    (owners : ∀ declaration ∈ declarations,
      (implementation.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (checkFuel : declarations.length ≤ 4094) :
    ∃ initialized ambient types live regions,
      AcceptedWorld config initialized (Goose.Proofs.Exit.stepState (runModule fuel config .initial)) ambient types live regions [] ∧
      (match runModule fuel config .initial with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  by_cases low : fuel < 3
  · obtain ⟨stop, after, initialized, ambient, types, live, regions, done, world⟩ :=
      acceptedByteModule_lowFuel fuel config accepted globals low
    simp only [done, Goose.Proofs.Exit.stepState]
    exact ⟨initialized, ambient, types, live, regions, world, trivial⟩
  · obtain ⟨remaining, exactFuel⟩ : ∃ remaining, fuel = remaining + 3 := ⟨fuel - 3, by omega⟩
    subst fuel
    rcases acceptedByteModule_noTail remaining config accepted declarations original implementation globals
        originalAt implementationAt body tail owners checkFuel with stopped | done
    · obtain ⟨stop, after, initialized, ambient, types, live, regions, executed, world⟩ := stopped
      simp only [executed, Goose.Proofs.Exit.stepState]
      exact ⟨initialized, ambient, types, live, regions, world, trivial⟩
    · obtain ⟨after, initialized, types, live, regions, executed, world⟩ := done
      simp only [executed, Goose.Proofs.Exit.stepState]
      exact ⟨initialized, [], types, live, regions, world, trivial⟩

#print axioms acceptedEntry_lowFuel_afterGlobals
#print axioms acceptedByteModule_lowFuel
#print axioms acceptedByteModule_allFuel

end Goose.Proofs.ConstructionAcceptedExecution
