import Goose.Proofs.ConstructionAcceptedMixedModule
import Goose.Proofs.ConstructionExecutionProtocolLifecycle

namespace Goose.Proofs.ConstructionAcceptedExecution

open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem acceptedMixedModule_allFuel_trace (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (original : Context) (implementation : Impl)
    (globals : ∀ id, id < config.module.globals.size →
      ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
        descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin)
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (form : MixedScalarByteStatements implementation.body.stmts)
    (owners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ implementation.body.stmts →
      (implementation.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (tail : implementation.body.value = none) :
    ∃ initialized ambient types live regions,
      let outcome := runModule fuel config .initial
      let after := Goose.Proofs.Exit.stepState outcome
      AcceptedWorld config initialized after ambient types live regions [] ∧
      DestinationTraceProtocol after.construction ∧
      (match outcome with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  obtain ⟨initialized, ambient, types, live, regions, world, flow⟩ :=
    acceptedMixedModule_allFuel fuel config accepted original implementation globals originalAt implementationAt form owners tail
  exact ⟨initialized, ambient, types, live, regions, world,
    Goose.Proofs.ConstructionExecutionProtocol.runModule_destination_trace_protocol fuel config, flow⟩

#print axioms acceptedMixedModule_allFuel_trace

end Goose.Proofs.ConstructionAcceptedExecution
