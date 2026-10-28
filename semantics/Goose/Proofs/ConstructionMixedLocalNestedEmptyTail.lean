import Goose.Proofs.ConstructionMixedLocalEntryReplay
import Goose.Proofs.ConstructionMixedLocalNestedAssignTail
import Goose.Proofs.ConstructionAcceptedMixedLocalAsAssign
import Goose.Proofs.ConstructionAcceptedNestedEmptyAnyUse
import Goose.Proofs.ConstructionAcceptedRecursiveGlobalModule
import Goose.Proofs.ConstructionEntryArgumentHelperTail
import Goose.Proofs.ConstructionAcceptedActivationWorld

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem acceptedMixedLocalModule_nestedEmptyTail_fromEntry (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (original : Context) (implementation : Impl) (helperContextId origin : Nat) (helperContext : Context) (helper : Impl)
    (expressions : List Expr) (parameterTypes : List Ty)
    (globals : ∀ id, id < config.module.globals.size →
      ∃ descriptor, config.module.globals[id]? = some descriptor ∧ RecursiveGlobalInitializer descriptor)
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (form : MixedLocalStatements implementation.body.stmts)
    (owners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ implementation.body.stmts →
      (implementation.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (scalarOwners : ∀ id expression origin, .letS id expression origin ∈ implementation.body.stmts →
      AcceptedBinaryExpression expression → ∀ descriptor, implementation.vars[id]? = some descriptor →
        (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (tail : implementation.body.value = some (.call helperContextId (expressions.map Arg.byVal) origin))
    (helperContextAt : config.module.contexts[helperContextId]? = some helperContext)
    (helperAt : config.module.impls[helperContext.impl]? = some helper)
    (helperResults : helper.results = #[])
    (descriptors : ScalarParameterDescriptors helper 0 helper.params.toList parameterTypes)
    (forms : NestedEffectfulArguments expressions)
    (blockConditions : ∀ expression ∈ expressions, ∀ scope id statementOrigin blockOrigin value intTy literal,
      expression = .blockE ⟨scope, [.assign (.global id) value statementOrigin], some (.lit intTy literal)⟩ blockOrigin →
      scope ≠ implementation.body.scope ∧ (∀ descriptor ∈ implementation.vars.toList, descriptor.scope ≠ scope) ∧
      (∀ descriptor, config.module.globals[id]? = some descriptor → (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool))
    (nestedConditions : ∀ expression ∈ expressions, ∀ outerScope innerScope id statementOrigin innerOrigin outerOrigin value intTy literal,
      expression = .blockE ⟨outerScope, [], some (.blockE
        ⟨innerScope, [.assign (.global id) value statementOrigin], some (.lit intTy literal)⟩ innerOrigin)⟩ outerOrigin →
      outerScope ≠ implementation.body.scope ∧ innerScope ≠ implementation.body.scope ∧ innerScope ≠ outerScope ∧
      (∀ descriptor ∈ implementation.vars.toList, descriptor.scope ≠ outerScope) ∧
      (∀ descriptor ∈ implementation.vars.toList, descriptor.scope ≠ innerScope) ∧
      (∀ descriptor, config.module.globals[id]? = some descriptor → (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool))
    (helperForm : MixedLocalStatements helper.body.stmts) (helperTail : helper.body.value = none)
    (helperOwners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ helper.body.stmts →
      (helper.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (helperScalarOwners : ∀ id expression origin, .letS id expression origin ∈ helper.body.stmts →
      AcceptedBinaryExpression expression → ∀ descriptor, helper.vars[id]? = some descriptor →
        (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool) :
    (∃ stop after initialized ambient types live regions,
      runModule (fuel + 3) config .initial = .stop stop after ∧
      AcceptedWorld config initialized after ambient types live regions []) ∨
    (∃ after initialized types live regions,
      runModule (fuel + 3) config .initial = .ok () after ∧
      AcceptedWorld config initialized after [] types live regions []) := by
  have localTargets : ∀ id expression statementOrigin, .assign (.var id) expression statementOrigin ∈ helper.body.stmts →
      ∀ descriptor, helper.vars[id]? = some descriptor → (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool := by
    intro id expression statementOrigin member descriptor declared
    exact (helperForm.noAssignment (.var id) expression statementOrigin member).elim
  have globalTargets : ∀ id expression statementOrigin, .assign (.global id) expression statementOrigin ∈ helper.body.stmts →
      ∀ descriptor, config.module.globals[id]? = some descriptor → (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool := by
    intro id expression statementOrigin member descriptor declared
    exact (helperForm.noAssignment (.global id) expression statementOrigin member).elim
  exact acceptedMixedLocalModule_nestedAssignEmptyTail_fromEntry fuel config accepted original implementation helperContextId origin helperContext helper expressions parameterTypes
    globals originalAt implementationAt form owners scalarOwners tail helperContextAt helperAt helperResults descriptors forms
    blockConditions nestedConditions helperForm.asAssign helperTail helperOwners helperScalarOwners localTargets globalTargets

theorem acceptedMixedLocalModule_nestedEmptyTail (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (original : Context) (implementation : Impl) (helperContextId origin : Nat) (helperContext : Context) (helper : Impl)
    (expressions : List Expr) (parameterTypes : List Ty)
    (globals : ∀ id, id < config.module.globals.size →
      ∃ descriptor, config.module.globals[id]? = some descriptor ∧ RecursiveGlobalInitializer descriptor)
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (form : MixedLocalStatements implementation.body.stmts)
    (owners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ implementation.body.stmts →
      (implementation.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (scalarOwners : ∀ id expression origin, .letS id expression origin ∈ implementation.body.stmts →
      AcceptedBinaryExpression expression → ∀ descriptor, implementation.vars[id]? = some descriptor →
        (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (tail : implementation.body.value = some (.call helperContextId (expressions.map Arg.byVal) origin))
    (helperContextAt : config.module.contexts[helperContextId]? = some helperContext)
    (helperAt : config.module.impls[helperContext.impl]? = some helper)
    (helperResults : helper.results = #[])
    (descriptors : ScalarParameterDescriptors helper 0 helper.params.toList parameterTypes)
    (forms : NestedEffectfulArguments expressions)
    (blockConditions : ∀ expression ∈ expressions, ∀ scope id statementOrigin blockOrigin value intTy literal,
      expression = .blockE ⟨scope, [.assign (.global id) value statementOrigin], some (.lit intTy literal)⟩ blockOrigin →
      scope ≠ implementation.body.scope ∧ (∀ descriptor ∈ implementation.vars.toList, descriptor.scope ≠ scope) ∧
      (∀ descriptor, config.module.globals[id]? = some descriptor → (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool))
    (nestedConditions : ∀ expression ∈ expressions, ∀ outerScope innerScope id statementOrigin innerOrigin outerOrigin value intTy literal,
      expression = .blockE ⟨outerScope, [], some (.blockE
        ⟨innerScope, [.assign (.global id) value statementOrigin], some (.lit intTy literal)⟩ innerOrigin)⟩ outerOrigin →
      outerScope ≠ implementation.body.scope ∧ innerScope ≠ implementation.body.scope ∧ innerScope ≠ outerScope ∧
      (∀ descriptor ∈ implementation.vars.toList, descriptor.scope ≠ outerScope) ∧
      (∀ descriptor ∈ implementation.vars.toList, descriptor.scope ≠ innerScope) ∧
      (∀ descriptor, config.module.globals[id]? = some descriptor → (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool))
    (helperForm : MixedLocalStatements helper.body.stmts) (helperTail : helper.body.value = none)
    (helperOwners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ helper.body.stmts →
      (helper.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (helperScalarOwners : ∀ id expression origin, .letS id expression origin ∈ helper.body.stmts →
      AcceptedBinaryExpression expression → ∀ descriptor, helper.vars[id]? = some descriptor →
        (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool) :
    (∃ stop after initialized ambient types live regions,
      runModule fuel config .initial = .stop stop after ∧
      AcceptedWorld config initialized after ambient types live regions []) ∨
    (∃ after initialized types live regions,
      runModule fuel config .initial = .ok () after ∧
      AcceptedWorld config initialized after [] types live regions []) := by
  have localTargets : ∀ id expression statementOrigin, .assign (.var id) expression statementOrigin ∈ helper.body.stmts →
      ∀ descriptor, helper.vars[id]? = some descriptor → (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool := by
    intro id expression statementOrigin member descriptor declared
    exact (helperForm.noAssignment (.var id) expression statementOrigin member).elim
  have globalTargets : ∀ id expression statementOrigin, .assign (.global id) expression statementOrigin ∈ helper.body.stmts →
      ∀ descriptor, config.module.globals[id]? = some descriptor → (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool := by
    intro id expression statementOrigin member descriptor declared
    exact (helperForm.noAssignment (.global id) expression statementOrigin member).elim
  exact acceptedMixedLocalModule_nestedAssignEmptyTail fuel config accepted original implementation helperContextId origin helperContext helper expressions parameterTypes
    globals originalAt implementationAt form owners scalarOwners tail helperContextAt helperAt helperResults descriptors forms
    blockConditions nestedConditions helperForm.asAssign helperTail helperOwners helperScalarOwners localTargets globalTargets

#print axioms acceptedMixedLocalModule_nestedEmptyTail
#print axioms acceptedMixedLocalModule_nestedEmptyTail_fromEntry
end Goose.Proofs.ConstructionAcceptedExecution
