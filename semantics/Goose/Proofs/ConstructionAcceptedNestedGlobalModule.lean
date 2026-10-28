import Goose.Proofs.ConstructionAcceptedNestedGlobalSequence
import Goose.Proofs.ConstructionAcceptedModuleFromGlobals

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem nestedInitialGlobalsOutcome (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (scalars : FlatGlobalsAreScalar config)
    (declarations : ∀ id, id < config.module.globals.size →
      ∃ descriptor, config.module.globals[id]? = some descriptor ∧ NestedGlobalInitializer descriptor) :
    InitialGlobalsOutcome fuel config := by
  obtain ⟨completed, live, regions, bound, world, final⟩ :=
    initGlobals_nested_initial_complete fuel config accepted scalars declarations
  refine ⟨completed, declaredRootTypes config.module, live, [], regions, bound, world, ?_⟩
  cases outcome : initGlobals fuel config (List.range config.module.globals.size) .initial with
  | ok value after => simp only [outcome] at final ⊢; exact ⟨trivial, final⟩
  | stop stop after => simpa only [outcome] using final
  | escape target carriers after | jump target kind after => simp only [outcome] at final

theorem acceptedNestedGlobalModule_lowFuel (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config) (scalars : FlatGlobalsAreScalar config)
    (declarations : ∀ id, id < config.module.globals.size →
      ∃ descriptor, config.module.globals[id]? = some descriptor ∧ NestedGlobalInitializer descriptor)
    (low : fuel < 3) :
    ∃ stop after initialized ambient types live regions,
      runModule fuel config .initial = .stop stop after ∧
      AcceptedWorld config initialized after ambient types live regions [] := by
  exact acceptedModuleFromGlobals_lowFuel fuel config accepted
    (nestedInitialGlobalsOutcome fuel config accepted scalars declarations) low


theorem acceptedNestedGlobalModule_noTail (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config) (scalars : FlatGlobalsAreScalar config)
    (original : Context) (implementation : Impl)
    (globals : ∀ id, id < config.module.globals.size →
      ∃ descriptor, config.module.globals[id]? = some descriptor ∧ NestedGlobalInitializer descriptor)
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
  exact acceptedModuleFromGlobals_noTail fuel config accepted original implementation
    (nestedInitialGlobalsOutcome (fuel + 3) config accepted scalars globals)
    originalAt implementationAt form owners scalarOwners localTargets globalTargets tail


theorem acceptedNestedGlobalModule_allFuel (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config) (scalars : FlatGlobalsAreScalar config)
    (original : Context) (implementation : Impl)
    (globals : ∀ id, id < config.module.globals.size →
      ∃ descriptor, config.module.globals[id]? = some descriptor ∧ NestedGlobalInitializer descriptor)
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
  exact acceptedModuleFromGlobals_allFuel fuel config accepted original implementation
    (nestedInitialGlobalsOutcome fuel config accepted scalars globals)
    originalAt implementationAt form owners scalarOwners localTargets globalTargets tail


#print axioms acceptedNestedGlobalModule_allFuel
#print axioms acceptedNestedGlobalModule_noTail
#print axioms acceptedNestedGlobalModule_lowFuel
end Goose.Proofs.ConstructionAcceptedExecution
