import Goose.Proofs.ConstructionAcceptedCheckedModuleFromGlobals
import Goose.Proofs.ConstructionAcceptedInitialGlobalsOutcome
import Goose.Proofs.ConstructionAcceptedMixedAssignModule
import Goose.Proofs.ConstructionByteModuleLowFuel

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem mixedAssign_checkedSequence (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (original : Context) (implementation : Impl)
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
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
    (frame : ConstructionSourceFrame) (activation : RuntimeActivation) (before : ExecutionState)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (scopeInst : Nat)
    (world : AcceptedWorld config frame.initialized before [.callChannels activation []] types live regions [])
    (source : AcceptedFrame config accepted frame before types) (phase : frame.phase = .implementation config.module.entry)
    (impl : frame.source.impl = implementation)
    (scopes : frame.interpretation.environment.scopes = (implementation.body.scope, scopeInst) :: activation.scopes)
    (empty : activation.scopes = []) (position : SourcePosition accepted frame (.statements implementation.body.stmts))
    (initialized : frame.initialized = config.module.globals.size) (limit : frame.typing.globalLimit ≤ config.module.globals.size)
    (bounded : GlobalEffectTargetsBounded frame.rootCursor.eff config.module.globals.size) :
    StatementWorldOutcome config accepted frame.initialized [.callChannels activation []] []
      (execStmts fuel config frame.interpretation.environment implementation.body.stmts before) := by
  obtain ⟨entry, entryImpl, entryAt, implAt, params, results⟩ := validated_entry config.module accepted.accepted
  have sameEntry : entry = original := Option.some.inj (entryAt.symm.trans originalAt)
  subst entry
  have sameImpl : entryImpl = implementation := Option.some.inj (implAt.symm.trans implementationAt)
  subst entryImpl
  have unnamed : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ implementation.body.stmts →
      (frame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some declaration.id)) = none := by
    intro declaration member
    simp [impl, results]
  have owners' : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ implementation.body.stmts →
      (frame.source.impl.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)) := by simpa [impl] using owners
  have scalarOwners' : ∀ id expression origin, .letS id expression origin ∈ implementation.body.stmts →
      AcceptedBinaryExpression expression → ∀ descriptor, frame.source.impl.vars[id]? = some descriptor →
        (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool := by simpa [impl] using scalarOwners
  have localTargets' : ∀ id expression origin, .assign (.var id) expression origin ∈ implementation.body.stmts →
      ∀ descriptor, frame.source.impl.vars[id]? = some descriptor → (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool := by
    simpa [impl] using localTargets
  obtain ⟨next, nextTypes, nextLive, nextRegions, initializedEq, extend, finalWorld, finalSource, flow⟩ :=
    execStmts_mixedAssign_accepted_world form fuel config accepted frame config.module.entry before
      [.callChannels activation []] types live regions [] world source phase position initialized limit bounded
      owners' scalarOwners' localTargets' globalTargets unnamed
  cases executed : execStmts fuel config frame.interpretation.environment implementation.body.stmts before with
  | stop reason after =>
    simp only [executed, Goose.Proofs.Exit.stepState] at finalWorld
    simp only [StatementWorldOutcome, executed]
    exact ⟨[.callChannels activation []], nextTypes, nextLive, nextRegions, initializedEq ▸ finalWorld⟩
  | escape address carriers after | jump destination kind after => simp only [executed] at flow
  | ok result after =>
    simp only [executed, Goose.Proofs.Exit.stepState] at finalWorld finalSource flow
    simp only [StatementWorldOutcome, executed]
    exact ⟨flow, next, nextTypes, nextLive, nextRegions, initializedEq, initializedEq ▸ finalWorld, finalSource⟩

theorem acceptedModuleFromGlobals_lowFuel (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (initial : InitialGlobalsOutcome fuel config)
    (low : fuel < 3) :
    ∃ stop after initialized ambient types live regions,
      runModule fuel config .initial = .stop stop after ∧
      AcceptedWorld config initialized after ambient types live regions [] := by
  exact acceptedCheckedModuleFromGlobals_lowFuel fuel config accepted initial low


theorem acceptedModuleFromGlobals_noTail (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (original : Context) (implementation : Impl)
    (initial : InitialGlobalsOutcome (fuel + 3) config)
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
  exact acceptedCheckedModuleFromGlobals_noTail fuel config accepted original implementation initial tail originalAt implementationAt
    (mixedAssign_checkedSequence fuel config accepted original implementation originalAt implementationAt form owners scalarOwners localTargets globalTargets)


theorem acceptedModuleFromGlobals_allFuel (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (original : Context) (implementation : Impl)
    (initial : InitialGlobalsOutcome fuel config)
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
  exact acceptedCheckedModuleFromGlobals_allFuel fuel config accepted original implementation initial tail originalAt implementationAt
    (fun sequenceFuel => mixedAssign_checkedSequence sequenceFuel config accepted original implementation originalAt implementationAt form owners scalarOwners localTargets globalTargets)


#print axioms mixedAssign_checkedSequence
#print axioms acceptedModuleFromGlobals_allFuel
#print axioms acceptedModuleFromGlobals_noTail
#print axioms acceptedModuleFromGlobals_lowFuel
end Goose.Proofs.ConstructionAcceptedExecution
