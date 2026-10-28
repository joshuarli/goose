import Goose.Proofs.ConstructionAcceptedMixedLocalExecution
import Goose.Proofs.ConstructionAcceptedMixedLocalAsAssign
import Goose.Proofs.ConstructionAcceptedMixedAssignBoundBody
import Goose.Proofs.ConstructionAcceptedParameterScopeExit

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem mixedLocal_boundBody_world (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (activation : RuntimeActivation) (pre : List (Nat × Value))
    (before boundState : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId : Nat)
    (environment : frame.interpretation.environment = activation) (channels : activation.channels = [])
    (results : frame.source.impl.results = #[])
    (tail : frame.source.impl.body.value = none) (phase : frame.phase = .implementation contextId)
    (initialized : frame.initialized = config.module.globals.size)
    (bound : bindAll activation.act before.nextScope pre
      (ownershipResultScopeState activation frame.source.impl.body.scope before) = .ok () boundState)
    (world : AcceptedWorld config config.module.globals.size boundState (.callChannels activation [] :: ambient) types live regions pending)
    (source : AcceptedFrame config accepted (entryStatementsFrame config frame before.nextScope) boundState types)
    (position : SourcePosition accepted (entryStatementsFrame config frame before.nextScope) (.statements frame.source.impl.body.stmts))
    (form : MixedLocalStatements frame.source.impl.body.stmts)
    (owners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ frame.source.impl.body.stmts →
      (frame.source.impl.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (scalarOwners : ∀ id expression origin, .letS id expression origin ∈ frame.source.impl.body.stmts →
      AcceptedBinaryExpression expression → ∀ descriptor, frame.source.impl.vars[id]? = some descriptor →
        (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool) :
    match execActivationBody (fuel + 1) config activation pre frame.source.impl.body before with
    | .stop _ after => ∃ nextTypes nextLive nextRegions,
        AcceptedWorld config config.module.globals.size after (.callChannels activation [] :: ambient) nextTypes nextLive nextRegions pending
    | .ok carriers after => carriers = [] ∧ ∃ nextTypes nextLive nextRegions,
        AcceptedWorld config config.module.globals.size after (.callChannels activation [] :: ambient) nextTypes nextLive nextRegions pending
    | _ => False := by
  have localTargets : ∀ id expression origin, .assign (.var id) expression origin ∈ frame.source.impl.body.stmts →
      ∀ descriptor, frame.source.impl.vars[id]? = some descriptor →
        (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool := by
    intro id expression origin member descriptor declared
    exact (form.noAssignment (.var id) expression origin member).elim
  have globalTargets : ∀ id expression origin, .assign (.global id) expression origin ∈ frame.source.impl.body.stmts →
      ∀ descriptor, config.module.globals[id]? = some descriptor →
        (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool := by
    intro id expression origin member descriptor declared
    exact (form.noAssignment (.global id) expression origin member).elim
  have result := mixedAssign_boundBody_world fuel config accepted frame activation pre before boundState ambient types live regions pending
    contextId environment channels results tail phase initialized bound world source position form.asAssign owners scalarOwners localTargets globalTargets
  cases step : execActivationBody (fuel + 1) config activation pre frame.source.impl.body before <;> simpa [step] using result

#print axioms mixedLocal_boundBody_world
end Goose.Proofs.ConstructionAcceptedExecution
