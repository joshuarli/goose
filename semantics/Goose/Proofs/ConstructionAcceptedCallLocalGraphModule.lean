import Goose.Proofs.ConstructionAcceptedRecursiveLocalCallGlobal
import Goose.Proofs.ConstructionAcceptedEarlierCallLocalGraph
import Goose.Proofs.ConstructionAcceptedModuleFromGlobals

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem callLocalGraphInitialGlobalsOutcome (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (descriptor : Global) (target origin : Nat) (calleeContext : Context) (callee : Impl)
    (size : config.module.globals.size = 1) (present : config.module.globals[0]? = some descriptor)
    (initializer : descriptor.init = .call target [] origin)
    (scalar : (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (calleeAt : config.module.contexts[target]? = some calleeContext)
    (implementationAt : config.module.impls[calleeContext.impl]? = some callee)
    (parameters : callee.params = #[]) (results : callee.results = #[⟨descriptor.ty, .register, none⟩])
    (graph : RegisterCallGraphWithCallLocals config descriptor.ty) : InitialGlobalsOutcome fuel config := by
  obtain ⟨completed, types, live, ambient, extend, lower, upper, world, final⟩ :=
    initGlobals_registerCall_fromEvaluation fuel 0 config accepted .initial [] (declaredRootTypes config.module) (fun _ => False)
      descriptor target origin calleeContext callee (initial_acceptedWorld config accepted.accepted) (futureGlobalsClear_initial config)
      present initializer scalar calleeAt implementationAt parameters results (by
        intro names roots typingAfter rootsAfter
        dsimp only
        intro activeWorld frameSource checked
        let frame := scalarGlobalInitializerFrame config 0 ExecutionState.initial.nextAct names
        let activated := { ExecutionState.initial with nextAct := ExecutionState.initial.nextAct + 1 }
        cases fuel with
        | zero =>
          simp only [evalValue, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
          exact ⟨_, _, _, (fun _ _ found => found), activeWorld, frameSource.futureGlobals, trivial⟩
        | succ fuel =>
          obtain ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, clear, observed, result⟩ :=
            invokeCall_recursive_register_callLocal_earlier fuel config accepted descriptor.ty scalar graph
              frame activated [] (declaredRootTypes config.module) (fun _ => False) [] []
              target calleeContext callee origin activeWorld frameSource calleeAt implementationAt parameters results
              roots typingAfter rootsAfter checked
          have safe : ∃ nextTypes nextLive nextAmbient,
              let outcome := invokeCall fuel config frame.interpretation.environment target [] [.register descriptor.ty] origin activated
              RootTypesExtend (declaredRootTypes config.module) nextTypes ∧ activated.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
              activated.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
              AcceptedWorld config 0 (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive [] [] ∧
              FutureGlobalsClear config 0 (Goose.Proofs.Exit.stepState outcome) ∧
              (match outcome with
               | .ok carriers _ => nextAmbient = [] ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation descriptor.ty value
               | .stop .. => True | .escape .. | .jump .. => False) :=
            ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, clear, result⟩
          obtain ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, world, clear, result⟩ :=
            evalValue_registerCall_fromInvoke fuel config 0 frame.interpretation.environment activated [] (declaredRootTypes config.module)
              [] [] target calleeContext callee descriptor.ty origin calleeAt implementationAt results safe
          exact ⟨nextTypes, nextLive, nextAmbient, extend, world, clear, result⟩)
  have range : List.range config.module.globals.size = [0] := by simp [size]
  refine ⟨completed, types, live, ambient, [], by omega, ?_, ?_⟩
  · simpa only [range] using world
  · cases run : initGlobals fuel config [0] .initial with
    | ok value after =>
      simp only [run, Goose.Proofs.Exit.stepState] at final
      simp only [range, run, Goose.Proofs.Exit.stepState]
      exact ⟨final.1, by simpa [size] using final.2.1, trivial, by simpa [size] using final.2.2⟩
    | stop reason after =>
      simp only [run, Goose.Proofs.Exit.stepState] at final
      simp only [range, run, Goose.Proofs.Exit.stepState]
      exact ⟨by omega, by simp [runModule, range, run, bind]⟩
    | escape address carriers after | jump destination kind after => simp only [run] at final

theorem acceptedCallLocalGraphModule_allFuel (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (descriptor : Global) (target origin : Nat) (calleeContext : Context) (callee : Impl)
    (size : config.module.globals.size = 1) (present : config.module.globals[0]? = some descriptor)
    (initializer : descriptor.init = .call target [] origin)
    (scalar : (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (calleeAt : config.module.contexts[target]? = some calleeContext)
    (implementationAt : config.module.impls[calleeContext.impl]? = some callee)
    (parameters : callee.params = #[]) (results : callee.results = #[⟨descriptor.ty, .register, none⟩])
    (graph : RegisterCallGraphWithCallLocals config descriptor.ty)
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
  exact acceptedModuleFromGlobals_allFuel fuel config accepted original implementation
    (callLocalGraphInitialGlobalsOutcome fuel config accepted descriptor target origin calleeContext callee size present
      initializer scalar calleeAt implementationAt parameters results graph)
    originalAt entryImplementationAt form owners scalarOwners localTargets globalTargets tail

#print axioms acceptedCallLocalGraphModule_allFuel
#print axioms callLocalGraphInitialGlobalsOutcome
end Goose.Proofs.ConstructionAcceptedExecution
