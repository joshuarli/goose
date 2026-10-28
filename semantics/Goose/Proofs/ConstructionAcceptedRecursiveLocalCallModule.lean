import Goose.Proofs.ConstructionAcceptedRecursiveLocalCallGlobal
import Goose.Proofs.ConstructionAcceptedModuleFromGlobals

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem localCallInitialGlobalsOutcome (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (descriptor : Global) (target origin : Nat) (calleeContext : Context) (callee : Impl)
    (size : config.module.globals.size = 1) (present : config.module.globals[0]? = some descriptor)
    (initializer : descriptor.init = .call target [] origin)
    (scalar : (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (calleeAt : config.module.contexts[target]? = some calleeContext)
    (implementationAt : config.module.impls[calleeContext.impl]? = some callee)
    (parameters : callee.params = #[]) (results : callee.results = #[⟨descriptor.ty, .register, none⟩])
    (graph : RegisterCallGraphWithLocals config descriptor.ty) : InitialGlobalsOutcome fuel config := by
  obtain ⟨completed, types, live, ambient, extend, lower, upper, world, final⟩ :=
    initGlobals_recursive_register_single_withLocals fuel 0 config accepted .initial [] (declaredRootTypes config.module) (fun _ => False)
      descriptor target origin calleeContext callee (initial_acceptedWorld config accepted.accepted) (futureGlobalsClear_initial config)
      present initializer scalar calleeAt implementationAt parameters results graph
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

theorem acceptedLocalCallModule_allFuel (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (descriptor : Global) (target origin : Nat) (calleeContext : Context) (callee : Impl)
    (size : config.module.globals.size = 1) (present : config.module.globals[0]? = some descriptor)
    (initializer : descriptor.init = .call target [] origin)
    (scalar : (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (calleeAt : config.module.contexts[target]? = some calleeContext)
    (implementationAt : config.module.impls[calleeContext.impl]? = some callee)
    (parameters : callee.params = #[]) (results : callee.results = #[⟨descriptor.ty, .register, none⟩])
    (graph : RegisterCallGraphWithLocals config descriptor.ty)
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
    (localCallInitialGlobalsOutcome fuel config accepted descriptor target origin calleeContext callee size present
      initializer scalar calleeAt implementationAt parameters results graph)
    originalAt entryImplementationAt form owners scalarOwners localTargets globalTargets tail

#print axioms acceptedLocalCallModule_allFuel
#print axioms localCallInitialGlobalsOutcome
end Goose.Proofs.ConstructionAcceptedExecution
