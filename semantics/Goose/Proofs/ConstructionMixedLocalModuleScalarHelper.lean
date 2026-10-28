import Goose.Proofs.ConstructionMixedLocalEntryReplay
import Goose.Proofs.ConstructionMixedLocalNestedEmptyTail
import Goose.Proofs.ConstructionAcceptedParameterPositionInvoke
import Goose.Proofs.ConstructionEntryScalarHelperTail
import Goose.Proofs.ConstructionAcceptedActivationWorld

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem acceptedMixedLocalModule_scalarHelperTail_fromEntry (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (original : Context) (implementation : Impl) (helperContextId origin : Nat) (helperContext : Context) (helper : Impl)
    (parameter : Param) (descriptor : LocalVar) (argument : Expr)
    (globals : ∀ id, id < config.module.globals.size →
      ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
        descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin)
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (form : MixedLocalStatements implementation.body.stmts)
    (owners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ implementation.body.stmts →
      (implementation.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (scalarOwners : ∀ id expression origin, .letS id expression origin ∈ implementation.body.stmts →
      AcceptedBinaryExpression expression → ∀ descriptor, implementation.vars[id]? = some descriptor →
        (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (tail : implementation.body.value = some (.call helperContextId [.byVal argument] origin))
    (helperContextAt : config.module.contexts[helperContextId]? = some helperContext)
    (helperAt : config.module.impls[helperContext.impl]? = some helper)
    (helperParams : helper.params = #[parameter]) (helperResults : helper.results = #[])
    (parameterMode : parameter.mode = .byValue) (parameterDeclared : helper.vars[0]? = some descriptor)
    (parameterScalar : (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (argumentForm : AcceptedBinaryExpression argument)
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
  have recursiveGlobals : ∀ id, id < config.module.globals.size →
      ∃ global, config.module.globals[id]? = some global ∧ RecursiveGlobalInitializer global := by
    intro id bound
    obtain ⟨global, bytes, bytesOrigin, declared, ty, init⟩ := globals id bound
    exact ⟨global, declared, Or.inr ⟨bytes, bytesOrigin, ty, init⟩⟩
  have parameterAt : helper.params[0]? = some parameter := by simp [helperParams]
  have descriptors : ScalarParameterDescriptors helper 0 helper.params.toList [descriptor.ty] := by
    rw [helperParams]
    exact .cons parameterAt descriptor parameterDeclared parameterMode parameterScalar (.nil 1)
  have forms : NestedEffectfulArguments [argument] := .cons (.flat (.scalar argumentForm)) .nil
  have noBlock : ∀ block origin, argument ≠ .blockE block origin := by
    intro block origin equal
    subst argument
    cases argumentForm with
    | numeric form =>
      cases form with
      | scalar form =>
        cases form with
        | scalar form => cases form
  have blockConditions : ∀ expression ∈ [argument], ∀ scope id statementOrigin blockOrigin value intTy literal,
      expression = .blockE ⟨scope, [.assign (.global id) value statementOrigin], some (.lit intTy literal)⟩ blockOrigin →
      scope ≠ implementation.body.scope ∧ (∀ item ∈ implementation.vars.toList, item.scope ≠ scope) ∧
      (∀ global, config.module.globals[id]? = some global → (∃ ty, global.ty = .int ty) ∨ global.ty = .bool) := by
    intro expression member scope id statementOrigin blockOrigin value intTy literal equal
    simp only [List.mem_singleton] at member
    exact (noBlock _ _ (member.symm.trans equal)).elim
  have nestedConditions : ∀ expression ∈ [argument], ∀ outerScope innerScope id statementOrigin innerOrigin outerOrigin value intTy literal,
      expression = .blockE ⟨outerScope, [], some (.blockE
        ⟨innerScope, [.assign (.global id) value statementOrigin], some (.lit intTy literal)⟩ innerOrigin)⟩ outerOrigin →
      outerScope ≠ implementation.body.scope ∧ innerScope ≠ implementation.body.scope ∧ innerScope ≠ outerScope ∧
      (∀ item ∈ implementation.vars.toList, item.scope ≠ outerScope) ∧
      (∀ item ∈ implementation.vars.toList, item.scope ≠ innerScope) ∧
      (∀ global, config.module.globals[id]? = some global → (∃ ty, global.ty = .int ty) ∨ global.ty = .bool) := by
    intro expression member outerScope innerScope id statementOrigin innerOrigin outerOrigin value intTy literal equal
    simp only [List.mem_singleton] at member
    exact (noBlock _ _ (member.symm.trans equal)).elim
  exact acceptedMixedLocalModule_nestedEmptyTail_fromEntry fuel config accepted original implementation helperContextId origin
    helperContext helper [argument] [descriptor.ty] recursiveGlobals originalAt implementationAt form owners scalarOwners
    (by simpa using tail) helperContextAt helperAt helperResults descriptors forms blockConditions nestedConditions
    helperForm helperTail helperOwners helperScalarOwners

theorem acceptedMixedLocalModule_scalarHelperTail (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (original : Context) (implementation : Impl) (helperContextId origin : Nat) (helperContext : Context) (helper : Impl)
    (parameter : Param) (descriptor : LocalVar) (argument : Expr)
    (globals : ∀ id, id < config.module.globals.size →
      ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
        descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin)
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (form : MixedLocalStatements implementation.body.stmts)
    (owners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ implementation.body.stmts →
      (implementation.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (scalarOwners : ∀ id expression origin, .letS id expression origin ∈ implementation.body.stmts →
      AcceptedBinaryExpression expression → ∀ descriptor, implementation.vars[id]? = some descriptor →
        (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (tail : implementation.body.value = some (.call helperContextId [.byVal argument] origin))
    (helperContextAt : config.module.contexts[helperContextId]? = some helperContext)
    (helperAt : config.module.impls[helperContext.impl]? = some helper)
    (helperParams : helper.params = #[parameter]) (helperResults : helper.results = #[])
    (parameterMode : parameter.mode = .byValue) (parameterDeclared : helper.vars[0]? = some descriptor)
    (parameterScalar : (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (argumentForm : AcceptedBinaryExpression argument)
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
  cases fuel with
  | zero => exact Or.inl (acceptedByteModule_lowFuel 0 config accepted globals (by omega))
  | succ fuel =>
    cases fuel with
    | zero => exact Or.inl (acceptedByteModule_lowFuel 1 config accepted globals (by omega))
    | succ fuel =>
      cases fuel with
      | zero => exact Or.inl (acceptedByteModule_lowFuel 2 config accepted globals (by omega))
      | succ fuel =>
        have same : fuel + 3 = fuel + 1 + 1 + 1 := by omega
        rw [← same]
        exact acceptedMixedLocalModule_scalarHelperTail_fromEntry fuel config accepted original implementation helperContextId origin
          helperContext helper parameter descriptor argument globals originalAt implementationAt form owners scalarOwners tail helperContextAt helperAt
          helperParams helperResults parameterMode parameterDeclared parameterScalar argumentForm helperForm helperTail helperOwners helperScalarOwners

#print axioms acceptedMixedLocalModule_scalarHelperTail
#print axioms acceptedMixedLocalModule_scalarHelperTail_fromEntry
end Goose.Proofs.ConstructionAcceptedExecution
