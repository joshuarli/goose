import Goose.Proofs.ConstructionAcceptedRecursiveCallGlobal
import Goose.Proofs.ConstructionAcceptedMixedAssignModule
import Goose.Proofs.ConstructionByteModuleLowFuel

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem acceptedRecursiveCallModule_noTail (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (descriptor : Global) (target origin : Nat) (calleeContext : Context) (callee : Impl)
    (size : config.module.globals.size = 1) (present : config.module.globals[0]? = some descriptor)
    (initializer : descriptor.init = .call target [] origin)
    (scalar : (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (calleeAt : config.module.contexts[target]? = some calleeContext)
    (implementationAt : config.module.impls[calleeContext.impl]? = some callee)
    (parameters : callee.params = #[]) (results : callee.results = #[⟨descriptor.ty, .register, none⟩])
    (graph : RegisterCallGraph config descriptor.ty)
    (original : Context) (implementation : Impl)
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (entryImplementationAt : config.module.impls[original.impl]? = some implementation)
    (form : MixedAssignStatements implementation.body.stmts)
    (owners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ implementation.body.stmts →
      (implementation.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (scalarOwners : ∀ id expression origin, .letS id expression origin ∈ implementation.body.stmts →
      AcceptedBinaryExpression expression → ∀ descriptor, implementation.vars[id]? = some descriptor →
        (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (localTargets : ∀ id expression origin, .assign (.var id) expression origin ∈ implementation.body.stmts →
      ∀ descriptor, implementation.vars[id]? = some descriptor → (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (globalTargets : ∀ id expression origin, .assign (.global id) expression origin ∈ implementation.body.stmts →
      ∀ descriptor, config.module.globals[id]? = some descriptor → (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (tail : implementation.body.value = none) :
    (∃ stop after initialized ambient types live regions,
      runModule (fuel + 3) config .initial = .stop stop after ∧ AcceptedWorld config initialized after ambient types live regions []) ∨
    (∃ after initialized types live regions,
      runModule (fuel + 3) config .initial = .ok () after ∧ AcceptedWorld config initialized after [] types live regions []) := by
  obtain ⟨completed, initialTypes, initialLive, initialAmbient, extend, lower, upper, initialWorld, final⟩ :=
    initGlobals_recursive_register_single (fuel + 3) 0 config accepted .initial [] (declaredRootTypes config.module) (fun _ => False)
      descriptor target origin calleeContext callee (initial_acceptedWorld config accepted.accepted) (futureGlobalsClear_initial config)
      present initializer scalar calleeAt implementationAt parameters results graph
  have range : List.range config.module.globals.size = [0] := by simp [size]
  cases initializedRun : initGlobals (fuel + 3) config (List.range config.module.globals.size) .initial with
  | stop reason after =>
    rw [range] at initializedRun
    simp only [initializedRun, Goose.Proofs.Exit.stepState] at initialWorld final
    have moduleStop : runModule (fuel + 3) config .initial = .stop reason after := by
      simp [runModule, range, initializedRun, bind]
    exact Or.inl ⟨reason, after, completed, initialAmbient, initialTypes, initialLive, [], moduleStop, initialWorld⟩
  | escape address carriers after | jump target kind after =>
    rw [range] at initializedRun
    simp only [initializedRun] at final
  | ok value state =>
    cases value
    have initializedRun' : initGlobals (fuel + 3) config [0] .initial = .ok () state := by simpa [range] using initializedRun
    simp only [initializedRun', Goose.Proofs.Exit.stepState] at initialWorld final
    obtain ⟨ambientEq, completedEq, clear⟩ := final
    subst initialAmbient completed
    let live := initialLive
    have world : AcceptedWorld config config.module.globals.size state [] initialTypes live [] [] := by simpa [size, live] using initialWorld
    obtain ⟨frame, next, activation, types, nextLive, regions, channels, implEq, callStep, bodyResult⟩ :=
      acceptedMixedAssignEntry_normal_scope fuel config accepted state live original implementation world
        originalAt entryImplementationAt form owners scalarOwners localTargets globalTargets tail
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
      have sameImpl : impl = implementation := Option.some.inj (implAt.symm.trans entryImplementationAt)
      subst impl
      simp only [runModule, initializedRun, bind, getImplementation, originalAt, entryImplementationAt, results,
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


theorem acceptedRecursiveCallModule_allFuel (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (descriptor : Global) (target origin : Nat) (calleeContext : Context) (callee : Impl)
    (size : config.module.globals.size = 1) (present : config.module.globals[0]? = some descriptor)
    (initializer : descriptor.init = .call target [] origin)
    (scalar : (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (calleeAt : config.module.contexts[target]? = some calleeContext)
    (implementationAt : config.module.impls[calleeContext.impl]? = some callee)
    (parameters : callee.params = #[]) (results : callee.results = #[⟨descriptor.ty, .register, none⟩])
    (graph : RegisterCallGraph config descriptor.ty)
    (original : Context) (implementation : Impl)
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (entryImplementationAt : config.module.impls[original.impl]? = some implementation)
    (form : MixedAssignStatements implementation.body.stmts)
    (owners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ implementation.body.stmts →
      (implementation.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (scalarOwners : ∀ id expression origin, .letS id expression origin ∈ implementation.body.stmts →
      AcceptedBinaryExpression expression → ∀ descriptor, implementation.vars[id]? = some descriptor →
        (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (localTargets : ∀ id expression origin, .assign (.var id) expression origin ∈ implementation.body.stmts →
      ∀ descriptor, implementation.vars[id]? = some descriptor → (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (globalTargets : ∀ id expression origin, .assign (.global id) expression origin ∈ implementation.body.stmts →
      ∀ descriptor, config.module.globals[id]? = some descriptor → (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (tail : implementation.body.value = none) :
    ∃ initialized ambient types live regions,
      AcceptedWorld config initialized (Goose.Proofs.Exit.stepState (runModule fuel config .initial)) ambient types live regions [] ∧
      (match runModule fuel config .initial with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  by_cases low : fuel < 3
  · obtain ⟨completed, initialTypes, initialLive, initialAmbient, extend, lower, upper, initialWorld, final⟩ :=
      initGlobals_recursive_register_single fuel 0 config accepted .initial [] (declaredRootTypes config.module) (fun _ => False)
        descriptor target origin calleeContext callee (initial_acceptedWorld config accepted.accepted) (futureGlobalsClear_initial config)
        present initializer scalar calleeAt implementationAt parameters results graph
    have range : List.range config.module.globals.size = [0] := by simp [size]
    cases globals : initGlobals fuel config (List.range config.module.globals.size) .initial with
    | stop reason after =>
      have globals' : initGlobals fuel config [0] .initial = .stop reason after := by simpa [range] using globals
      simp only [globals', Goose.Proofs.Exit.stepState] at initialWorld final
      have moduleStop : runModule fuel config .initial = .stop reason after := by simp [runModule, globals, bind]
      simp only [moduleStop, Goose.Proofs.Exit.stepState]
      exact ⟨completed, initialAmbient, initialTypes, initialLive, [], initialWorld, trivial⟩
    | escape address carriers after | jump target kind after =>
      rw [range] at globals
      simp only [globals] at final
    | ok value after =>
      cases value
      have globals' : initGlobals fuel config [0] .initial = .ok () after := by simpa [range] using globals
      simp only [globals', Goose.Proofs.Exit.stepState] at initialWorld final
      obtain ⟨ambientEq, completedEq, clear⟩ := final
      subst initialAmbient completed
      have world : AcceptedWorld config config.module.globals.size after [] initialTypes initialLive [] [] := by
        simpa [size] using initialWorld
      obtain ⟨stopped, ambient, moduleStop, finalWorld⟩ :=
        acceptedEntry_lowFuel_afterGlobals fuel config accepted after initialLive world globals low
      simp only [moduleStop, Goose.Proofs.Exit.stepState]
      exact ⟨config.module.globals.size, ambient, initialTypes, initialLive, [], finalWorld, trivial⟩
  · obtain ⟨remaining, exactFuel⟩ : ∃ remaining, fuel = remaining + 3 := ⟨fuel - 3, by omega⟩
    subst fuel
    rcases acceptedRecursiveCallModule_noTail remaining config accepted descriptor target origin calleeContext callee size present
      initializer scalar calleeAt implementationAt parameters results graph original implementation originalAt entryImplementationAt
      form owners scalarOwners localTargets globalTargets tail with stopped | done
    · obtain ⟨reason, after, initialized, ambient, types, live, regions, executed, world⟩ := stopped
      simp only [executed, Goose.Proofs.Exit.stepState]
      exact ⟨initialized, ambient, types, live, regions, world, trivial⟩
    · obtain ⟨after, initialized, types, live, regions, executed, world⟩ := done
      simp only [executed, Goose.Proofs.Exit.stepState]
      exact ⟨initialized, [], types, live, regions, world, trivial⟩

#print axioms acceptedRecursiveCallModule_allFuel
#print axioms acceptedRecursiveCallModule_noTail
end Goose.Proofs.ConstructionAcceptedExecution
