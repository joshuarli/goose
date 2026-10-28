import Goose.Proofs.ConstructionAcceptedUnaryCallComplete
import Goose.Proofs.ConstructionAcceptedSingleScalarGlobal
import Goose.Proofs.ConstructionAcceptedModuleFromGlobals

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem unaryCallInitialGlobalsOutcome (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (descriptor : Global) (integer : Goose.Core.IntTy)
    (size : config.module.globals.size = 1) (present : config.module.globals[0]? = some descriptor)
    (descriptorType : descriptor.ty = .int integer)
    (form : UnaryRegisterExpression config integer descriptor.init)
    (graph : RegisterCallGraphWithCallLocals config (.int integer)) : InitialGlobalsOutcome fuel config := by
  apply singleScalarInitialGlobalsOutcome fuel config accepted descriptor size present (Or.inl ⟨integer, descriptorType⟩)
  intro names roots typingAfter rootsAfter frame activated activeWorld frameSource checked
  have checked' : CheckedValue frame descriptor.init (.int integer) roots typingAfter rootsAfter := by simpa [descriptorType] using checked
  obtain ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, world, source, clear, observed, result⟩ :=
    evalValue_unaryRegisterExpression config integer form fuel accepted frame activated [] (declaredRootTypes config.module)
      (fun _ => False) [] [] graph activeWorld frameSource roots typingAfter rootsAfter checked'
  refine ⟨nextTypes, nextLive, nextAmbient, extend, world, clear, ?_⟩
  rw [descriptorType]
  exact result

theorem acceptedUnaryCallModule_allFuel (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (descriptor : Global) (integer : Goose.Core.IntTy)
    (size : config.module.globals.size = 1) (present : config.module.globals[0]? = some descriptor)
    (descriptorType : descriptor.ty = .int integer) (form : UnaryRegisterExpression config integer descriptor.init)
    (graph : RegisterCallGraphWithCallLocals config (.int integer))
    (original : Context) (implementation : Impl)
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (entryImplementationAt : config.module.impls[original.impl]? = some implementation)
    (entryForm : MixedAssignStatements implementation.body.stmts)
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
    (unaryCallInitialGlobalsOutcome fuel config accepted descriptor integer size present descriptorType form graph)
    originalAt entryImplementationAt entryForm owners scalarOwners localTargets globalTargets tail

#print axioms acceptedUnaryCallModule_allFuel
#print axioms unaryCallInitialGlobalsOutcome
end Goose.Proofs.ConstructionAcceptedExecution
