import Goose.Proofs.ConstructionAcceptedDependentGlobal

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem acceptedDependentGlobalModule_lowFuel (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (declarations : ∀ id, id < config.module.globals.size →
      ∃ descriptor, config.module.globals[id]? = some descriptor ∧ DependentGlobalInitializer config id descriptor)
    (low : fuel < 3) :
    ∃ stop after initialized ambient types live regions,
      runModule fuel config .initial = .stop stop after ∧
      AcceptedWorld config initialized after ambient types live regions [] := by
  obtain ⟨completed, live, regions, bound, world, final⟩ :=
    initGlobals_dependent_initial_complete fuel config accepted declarations
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

theorem acceptedDependentGlobalModule_noTail (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (original : Context) (implementation : Impl)
    (globals : ∀ id, id < config.module.globals.size →
      ∃ descriptor, config.module.globals[id]? = some descriptor ∧ DependentGlobalInitializer config id descriptor)
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (form : MixedAssignStatements implementation.body.stmts)
    (owners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ implementation.body.stmts →
      (implementation.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (scalarOwners : ∀ id expression origin, .letS id expression origin ∈ implementation.body.stmts →
      AcceptedBinaryExpression expression → ∀ descriptor, implementation.vars[id]? = some descriptor →
        (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (localTargets : ∀ id expression origin, .assign (.var id) expression origin ∈ implementation.body.stmts →
      ∀ descriptor, implementation.vars[id]? = some descriptor →
        (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (globalTargets : ∀ id expression origin, .assign (.global id) expression origin ∈ implementation.body.stmts →
      ∀ descriptor, config.module.globals[id]? = some descriptor →
        (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (tail : implementation.body.value = none) :
    (∃ stop after initialized ambient types live regions,
      runModule (fuel + 3) config .initial = .stop stop after ∧
      AcceptedWorld config initialized after ambient types live regions []) ∨
    (∃ after initialized types live regions,
      runModule (fuel + 3) config .initial = .ok () after ∧
      AcceptedWorld config initialized after [] types live regions []) := by
  obtain ⟨completed, initialLive, initialRegions, bound, initialWorld, final⟩ :=
    initGlobals_dependent_initial_complete (fuel + 3) config accepted globals
  cases initializedRun : initGlobals (fuel + 3) config (List.range config.module.globals.size) .initial with
  | stop reason after =>
    simp only [initializedRun, Goose.Proofs.Exit.stepState] at initialWorld final
    exact Or.inl ⟨reason, after, completed, [], declaredRootTypes config.module, initialLive, initialRegions, final.2, initialWorld⟩
  | escape address carriers after | jump target kind after => simp only [initializedRun] at final
  | ok value state =>
    cases value
    simp only [initializedRun, Goose.Proofs.Exit.stepState] at initialWorld final
    obtain ⟨completedEq, regionsEq, clear⟩ := final
    subst completed
    subst initialRegions
    let live := initialLive
    have world : AcceptedWorld config config.module.globals.size state [] (declaredRootTypes config.module) live [] [] := initialWorld
    obtain ⟨frame, next, activation, types, nextLive, regions, channels, implEq, callStep, bodyResult⟩ :=
      acceptedMixedAssignEntry_normal_scope fuel config accepted state live original implementation world
        originalAt implementationAt form owners scalarOwners localTargets globalTargets tail
    let activated := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
    let before := ownershipResultScopeState activation frame.source.impl.body.scope activated
    let entryFrame := entryStatementsFrame config frame activated.nextScope
    have moduleStep : runModule (fuel + 3) config .initial =
        (invokeCall (fuel + 3) config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 >>= fun carriers =>
          publishCarriers 0 carriers) state := by
      have results := validated_entry config.module accepted.accepted
      obtain ⟨entry, impl, entryAt, implAt, params, results⟩ := results
      have sameEntry : entry = original := Option.some.inj (entryAt.symm.trans originalAt)
      subst entry
      have sameImpl : impl = implementation := Option.some.inj (implAt.symm.trans implementationAt)
      subst impl
      simp only [runModule, initializedRun, bind, getImplementation, originalAt, implementationAt, results,
        Array.toList_empty, channelsFor, List.mapM_nil, pure]
    change (match execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before with
      | .ok (.normal .unit) after => _ | .stop reason after => _ | _ => False) at bodyResult
    cases outcome : execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before with
    | escape address carriers after | jump target kind after => simp only [outcome] at bodyResult
    | stop reason after =>
      simp only [outcome] at bodyResult
      obtain ⟨stopped, afterWorld⟩ := bodyResult
      apply Or.inl
      refine ⟨reason, after, next.initialized, [.callChannels activation []], types, nextLive, regions, ?_, afterWorld⟩
      rw [moduleStep]
      simp only [bind, callStep, finishActivation, stopped]
    | ok flow after =>
      simp only [outcome] at bodyResult
      cases flow with
      | breaking value | continuing => cases bodyResult
      | normal value =>
        cases value with
        | unit =>
          obtain ⟨done, afterWorld⟩ := bodyResult
          let released := releaseScopeState activation frame.source.impl.body.scope activated.nextScope after
          let finished := { released with activations := released.activations.filter (fun current => current.act != activation.act) }
          have finishedWorld := afterWorld.finishEntry config next.initialized released activation types _ regions []
          apply Or.inr
          refine ⟨finished, next.initialized, types, _, regions, ?_, finishedWorld⟩
          rw [moduleStep]
          simp [bind, callStep, finishActivation, done, channels, finishChannels, landCarriersInto, deliverCarriers,
            publishCarriers, liftConstruction, publishOperation, preflightPublication, ConstructionM.get,
            bind, pure, Except.pure, Except.bind, finished, released, activated]
        | _ => cases bodyResult


theorem acceptedDependentGlobalModule_allFuel (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (original : Context) (implementation : Impl)
    (globals : ∀ id, id < config.module.globals.size →
      ∃ descriptor, config.module.globals[id]? = some descriptor ∧ DependentGlobalInitializer config id descriptor)
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (form : MixedAssignStatements implementation.body.stmts)
    (owners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ implementation.body.stmts →
      (implementation.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (scalarOwners : ∀ id expression origin, .letS id expression origin ∈ implementation.body.stmts →
      AcceptedBinaryExpression expression → ∀ descriptor, implementation.vars[id]? = some descriptor →
        (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (localTargets : ∀ id expression origin, .assign (.var id) expression origin ∈ implementation.body.stmts →
      ∀ descriptor, implementation.vars[id]? = some descriptor →
        (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (globalTargets : ∀ id expression origin, .assign (.global id) expression origin ∈ implementation.body.stmts →
      ∀ descriptor, config.module.globals[id]? = some descriptor →
        (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (tail : implementation.body.value = none) :
    ∃ initialized ambient types live regions,
      AcceptedWorld config initialized (Goose.Proofs.Exit.stepState (runModule fuel config .initial)) ambient types live regions [] ∧
      (match runModule fuel config .initial with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  by_cases low : fuel < 3
  · obtain ⟨stop, after, initialized, ambient, types, live, regions, done, world⟩ :=
      acceptedDependentGlobalModule_lowFuel fuel config accepted globals low
    simp only [done, Goose.Proofs.Exit.stepState]
    exact ⟨initialized, ambient, types, live, regions, world, trivial⟩
  · obtain ⟨remaining, exactFuel⟩ : ∃ remaining, fuel = remaining + 3 := ⟨fuel - 3, by omega⟩
    subst fuel
    rcases acceptedDependentGlobalModule_noTail remaining config accepted original implementation globals
        originalAt implementationAt form owners scalarOwners localTargets globalTargets tail with stopped | done
    · obtain ⟨stop, after, initialized, ambient, types, live, regions, executed, world⟩ := stopped
      simp only [executed, Goose.Proofs.Exit.stepState]
      exact ⟨initialized, ambient, types, live, regions, world, trivial⟩
    · obtain ⟨after, initialized, types, live, regions, executed, world⟩ := done
      simp only [executed, Goose.Proofs.Exit.stepState]
      exact ⟨initialized, [], types, live, regions, world, trivial⟩


#print axioms acceptedDependentGlobalModule_allFuel
#print axioms acceptedDependentGlobalModule_noTail
#print axioms acceptedDependentGlobalModule_lowFuel
end Goose.Proofs.ConstructionAcceptedExecution
