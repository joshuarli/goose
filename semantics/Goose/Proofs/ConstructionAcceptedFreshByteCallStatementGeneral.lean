import Goose.Proofs.ConstructionAcceptedFreshByteCallBindGeneral
import Goose.Proofs.ConstructionAcceptedByteCallStatement

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (OriginId RootInst)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ExitExecution

private theorem byteCall_bind_stop {α β : Type} (action : EvalM α) (next : α → EvalM β)
    (before after : ExecutionState) (reason : Goose.Core.Stop) (step : action before = .stop reason after) :
    (action >>= next) before = .stop reason after := by simp only [bind, step]

private theorem byteCall_bind_ok {α β : Type} (action : EvalM α) (next : α → EvalM β)
    (before after : ExecutionState) (value : α) (step : action before = .ok value after) :
    (action >>= next) before = next value after := by simp only [bind, step]

theorem acceptedByteCall_let_pending_world (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (contextId scope localId : Nat) (root : RootInst) (bytes : List UInt8)
    (statementOrigin origin : OriginId) (context : Context) (helper implementation : Impl)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types)
    (descriptor : LocalVar) (rootOrder : localId = frame.rootCursor.nextVar) (typingOrder : localId = frame.typingCounter)
    (declared : frame.typing.variables[localId]? = some descriptor) (descriptorType : descriptor.ty = .varr (.int .u8))
    (resolved : rootOf frame.interpretation.environment localId before = .ok root before)
    (conforms : LayoutConforms config.layout (.varr (.int .u8)))
    (implementationFound : config.module.impls[frame.interpretation.environment.implementation]? = some implementation)
    (unnamed : (implementation.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some localId)) = none)
    (contextAt : config.module.contexts[contextId]? = some context)
    (helperAt : config.module.impls[context.impl]? = some helper)
    (parameters : helper.params = #[])
    (results : helper.results = #[⟨.varr (.int .u8), .value, none⟩])
    (body : helper.body = ⟨scope, [], some (.bytes (.varr (.int .u8)) bytes origin)⟩)
    (absent : ∀ item ∈ helper.vars.toList, item.scope ≠ scope)
    (coverage : EvaluationHistoryCoverage before ambient pending)
    (fits : bytes.length < 2 ^ 32) (depth : before.activations.length < Goose.Core.maxCallDepth) :
    match execStmt (fuel + 2) config frame.interpretation.environment (.letS localId (.call contextId [] origin) statementOrigin) before with
    | .stop _ after => ∃ nextAmbient nextRegions,
        AcceptedWorld config frame.initialized after nextAmbient types live nextRegions pending
    | .ok flow after => ∃ nextRegions, flow = .normal .unit ∧
        RootTypesExtend types (registerRootType types root (.varr (.int .u8))) ∧
        AcceptedWorld config frame.initialized after ambient (registerRootType types root (.varr (.int .u8)))
          (fun other => other = root ∨ live other) nextRegions pending ∧
        AcceptedFrame config accepted (advanceLocalFrame frame localId) after (registerRootType types root (.varr (.int .u8)))
    | _ => False := by
  let caller := frame.interpretation.environment
  have runtimeDeclared : caller.vars[localId]? = some descriptor := by
    simpa only [caller, source.compatible.variables] using declared
  have allocation := newDestination_byteOwner_world_outcome config accepted frame caller.act statementOrigin none before ambient types live regions pending world source
  cases created : newDestination config.layout caller.act (.varr (.int .u8)) .value statementOrigin none none before with
  | escape target carriers after | jump target kind after => simp [created] at allocation
  | stop reason after =>
    simp only [created] at allocation
    have query := byteCall_ordinaryProducerCount (fuel + 1) config caller contextId origin context helper contextAt helperAt results
    simp [caller, execStmt, runtimeDeclared, descriptorType, Ty.nonfixed, implementationFound, unnamed, materializeProducer,
      query, resolved, producerCount?, literalCount, created, bind, pure]
    exact ⟨ambient, regions, allocation.1⟩
  | ok id allocated =>
    have action := byteCall_let_action fuel config caller localId contextId statementOrigin origin descriptor implementation context helper root before allocated id
      runtimeDeclared descriptorType implementationFound unnamed resolved contextAt helperAt results created
    have binding := fresh_byteCall_bind_pending fuel config accepted frame caller contextId scope localId root bytes statementOrigin origin context helper
      none before allocated id ambient types live regions pending world coverage source descriptor rootOrder typingOrder declared descriptorType resolved conforms
      contextAt helperAt parameters results body absent fits depth created
    cases step : (do
        let stored ← (do
          buildExpr (fuel + 1) config caller id (.call contextId [] origin)
          let destination ← completedReceivingDestination id
          publishCarriers statementOrigin [.completed destination]
          storedDestination destination)
        bindRoot root (.stored { stored with ty := .varr (.int .u8), object := none })) allocated with
    | escape target carriers after | jump target kind after => simp [step] at binding
    | stop reason after =>
      simp only [step] at binding
      rw [action]
      have stopped := byteCall_bind_stop _ (fun _ => pure (Flow.normal .unit)) allocated after reason step
      rw [stopped]
      obtain ⟨nextAmbient, finalWorld⟩ := binding
      exact ⟨nextAmbient, freshReceivingRegion before id :: regions, finalWorld⟩
    | ok value after =>
      cases value
      simp only [step] at binding
      obtain ⟨stored, extended, finalWorld, finalFrame, storageEq, destinationEq⟩ := binding
      rw [action]
      have done := byteCall_bind_ok _ (fun _ => pure (Flow.normal .unit)) allocated after () step
      rw [done]
      exact ⟨_, rfl, extended, finalWorld, finalFrame⟩

theorem acceptedByteCall_let_pending_lowFuel (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (contextId localId : Nat) (root : RootInst)
    (statementOrigin origin : OriginId) (context : Context) (helper implementation : Impl)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types) (descriptor : LocalVar)
    (declared : frame.typing.variables[localId]? = some descriptor) (descriptorType : descriptor.ty = .varr (.int .u8))
    (resolved : rootOf frame.interpretation.environment localId before = .ok root before)
    (implementationFound : config.module.impls[frame.interpretation.environment.implementation]? = some implementation)
    (unnamed : (implementation.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some localId)) = none)
    (contextAt : config.module.contexts[contextId]? = some context)
    (helperAt : config.module.impls[context.impl]? = some helper)
    (results : helper.results = #[⟨.varr (.int .u8), .value, none⟩]) :
    execStmt 0 config frame.interpretation.environment (.letS localId (.call contextId [] origin) statementOrigin) before = .stop .timeout before ∧
    match execStmt 1 config frame.interpretation.environment (.letS localId (.call contextId [] origin) statementOrigin) before with
    | .stop _ after => ∃ nextRegions, AcceptedWorld config frame.initialized after ambient types live nextRegions pending
    | _ => False := by
  let caller := frame.interpretation.environment
  have runtimeDeclared : caller.vars[localId]? = some descriptor := by
    simpa only [caller, source.compatible.variables] using declared
  have query := byteCall_ordinaryProducerCount 0 config caller contextId origin context helper contextAt helperAt results
  have allocation := newDestination_byteOwner_world_outcome config accepted frame caller.act statementOrigin none before ambient types live regions pending world source
  refine ⟨by simp [execStmt, Goose.Construct.timeout, EvalM.stop], ?_⟩
  cases created : newDestination config.layout caller.act (.varr (.int .u8)) .value statementOrigin none none before with
  | escape target carriers after | jump target kind after => simp [created] at allocation
  | stop reason after =>
    simp only [created] at allocation
    simp [caller, execStmt, runtimeDeclared, descriptorType, Ty.nonfixed, implementationFound, unnamed, materializeProducer,
      query, resolved, producerCount?, literalCount, created, bind, pure]
    exact ⟨regions, allocation.1⟩
  | ok id allocated =>
    simp only [created] at allocation
    simp [caller, execStmt, runtimeDeclared, descriptorType, Ty.nonfixed, implementationFound, unnamed, materializeProducer,
      query, resolved, producerCount?, literalCount, created, buildExpr, Goose.Construct.timeout, EvalM.stop, bind, pure]
    exact ⟨freshReceivingRegion before id :: regions, allocation.1⟩

theorem acceptedByteCall_let_pending_allFuel (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (contextId scope localId : Nat) (root : RootInst) (bytes : List UInt8)
    (statementOrigin origin : OriginId) (context : Context) (helper implementation : Impl)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types)
    (descriptor : LocalVar) (rootOrder : localId = frame.rootCursor.nextVar) (typingOrder : localId = frame.typingCounter)
    (declared : frame.typing.variables[localId]? = some descriptor) (descriptorType : descriptor.ty = .varr (.int .u8))
    (resolved : rootOf frame.interpretation.environment localId before = .ok root before)
    (conforms : LayoutConforms config.layout (.varr (.int .u8)))
    (implementationFound : config.module.impls[frame.interpretation.environment.implementation]? = some implementation)
    (unnamed : (implementation.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some localId)) = none)
    (contextAt : config.module.contexts[contextId]? = some context)
    (helperAt : config.module.impls[context.impl]? = some helper)
    (parameters : helper.params = #[])
    (results : helper.results = #[⟨.varr (.int .u8), .value, none⟩])
    (body : helper.body = ⟨scope, [], some (.bytes (.varr (.int .u8)) bytes origin)⟩)
    (absent : ∀ item ∈ helper.vars.toList, item.scope ≠ scope)
    (coverage : EvaluationHistoryCoverage before ambient pending)
    (fits : bytes.length < 2 ^ 32) (depth : before.activations.length < Goose.Core.maxCallDepth) :
    match execStmt fuel config frame.interpretation.environment (.letS localId (.call contextId [] origin) statementOrigin) before with
    | .stop _ after => ∃ nextAmbient nextRegions,
        AcceptedWorld config frame.initialized after nextAmbient types live nextRegions pending
    | .ok flow after => ∃ nextRegions, flow = .normal .unit ∧
        RootTypesExtend types (registerRootType types root (.varr (.int .u8))) ∧
        AcceptedWorld config frame.initialized after ambient (registerRootType types root (.varr (.int .u8)))
          (fun other => other = root ∨ live other) nextRegions pending ∧
        AcceptedFrame config accepted (advanceLocalFrame frame localId) after (registerRootType types root (.varr (.int .u8)))
    | _ => False := by
  cases fuel with
  | zero =>
    have low := acceptedByteCall_let_pending_lowFuel config accepted frame contextId localId root statementOrigin origin context helper implementation
      before ambient types live regions pending world source descriptor declared descriptorType resolved implementationFound unnamed contextAt helperAt results
    simpa only [low.1] using ⟨ambient, regions, world⟩
  | succ fuel =>
    cases fuel with
    | zero =>
      have low := acceptedByteCall_let_pending_lowFuel config accepted frame contextId localId root statementOrigin origin context helper implementation
        before ambient types live regions pending world source descriptor declared descriptorType resolved implementationFound unnamed contextAt helperAt results
      cases result : execStmt 1 config frame.interpretation.environment (.letS localId (.call contextId [] origin) statementOrigin) before with
      | stop reason after =>
        simp only [result] at low
        simp only []
        obtain ⟨nextRegions, finalWorld⟩ := low.2
        exact ⟨ambient, nextRegions, finalWorld⟩
      | ok value after | escape target value after | jump target value after => simp [result] at low
    | succ fuel =>
      simpa only [Nat.add_assoc] using acceptedByteCall_let_pending_world fuel config accepted frame contextId scope localId root bytes
        statementOrigin origin context helper implementation before ambient types live regions pending world source descriptor rootOrder typingOrder
        declared descriptorType resolved conforms implementationFound unnamed contextAt helperAt parameters results body absent coverage fits depth

#print axioms acceptedByteCall_let_pending_allFuel
end Goose.Proofs.ConstructionAcceptedExecution
