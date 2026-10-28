import Goose.Proofs.ConstructionAcceptedScalarGlobalsRegisterBody

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem singleGlobal_registerResultBody_observedWorld (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (activation : RuntimeActivation) (pre : List (Nat × Value))
    (before boundState : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId : Nat) (context : Context) (helper : Impl) (ty : Ty) (expression : Expr)
    (globalId globalOrigin : Nat) (assigned : Expr) (assignedForm : AcceptedBinaryExpression assigned)
    (helperAt : config.module.impls[context.impl]? = some helper)
    (helperEq : frame.source.impl = helper) (phase : frame.phase = .implementation contextId)
    (environment : frame.interpretation.environment = activation) (channels : activation.channels = [.register ty])
    (results : helper.results = #[⟨ty, .register, none⟩])
    (scalar : (∃ intTy, ty = .int intTy) ∨ ty = .bool)
    (tail : helper.body.value = some expression) (shape : AcceptedBinaryExpression expression)
    (statements : helper.body.stmts = [.assign (.global globalId) assigned globalOrigin])
    (globalScalar : ∀ descriptor, config.module.globals[globalId]? = some descriptor →
      (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (initialized : frame.initialized = config.module.globals.size)
    (bound : bindAll activation.act before.nextScope pre
      (ownershipResultScopeState activation helper.body.scope before) = .ok () boundState)
    (world : AcceptedWorld config config.module.globals.size boundState (.callChannels activation [] :: ambient) types live regions pending)
    (source : AcceptedFrame config accepted (entryStatementsFrame config frame before.nextScope) boundState types)
    (position : SourcePosition accepted (entryStatementsFrame config frame before.nextScope) (.statements helper.body.stmts)) :
    match execActivationBody (fuel + 1) config activation pre helper.body before with
    | .stop _ after => ∃ nextLive nextRegions,
        AcceptedWorld config config.module.globals.size after (.callChannels activation [] :: ambient) types nextLive nextRegions pending
    | .ok carriers after => ∃ value nextLive nextRegions, carriers = [.register value] ∧
        ValueRepresentation ty value ∧
        AcceptedWorld config config.module.globals.size after (.callChannels activation [] :: ambient) types nextLive nextRegions pending ∧
        ScalarGlobalObservation activation.act boundState after
    | _ => False := by
  apply scalarGlobals_registerResultBody_observedWorld fuel config accepted frame activation pre before boundState ambient types live regions pending
    contextId context helper ty expression helperAt helperEq phase environment channels results scalar tail shape
  · rw [statements]
    exact .cons globalId assigned globalOrigin [] assignedForm .nil
  · intro id expression origin member descriptor declared
    simp [statements] at member
    obtain ⟨rfl, rfl, rfl⟩ := member
    exact globalScalar descriptor declared
  · exact initialized
  · exact bound
  · exact world
  · exact source
  · exact position

#print axioms singleGlobal_registerResultBody_observedWorld
end Goose.Proofs.ConstructionAcceptedExecution
