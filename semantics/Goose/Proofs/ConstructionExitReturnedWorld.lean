import Goose.Proofs.ConstructionExitTargetRegisters
import Goose.Proofs.ExitExecutionPathContext

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst OriginId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ExitExecution

theorem acceptedWorld_returned (config : EvalConfig) (initialized : Nat) (state : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (channels : List Channel) (carriers : List Carrier)
    (world : AcceptedWorld config initialized state ambient types live regions pending)
    (ready : CarriersLandingReady state channels carriers)
    (backed : ∀ carrier ∈ carriers, CarrierResultBacking config.layout state carrier) :
    AcceptedWorld config initialized state (.returned carriers :: ambient) types live regions
      (⟨channels, carriers⟩ :: pending) := by
  have ownership := ownershipExecutionContext_returned state ambient carriers world.ownership
  refine ⟨{ world.toAcceptedWorldCore with ownership := ownership, carriers := ?_ }, world.globalLive⟩
  intro frame member
  rcases List.mem_cons.mp member with same | old
  · subst frame
    exact ⟨ready, backed⟩
  · exact world.carriers frame old

theorem reached_checked_register_returnFrom_world (rootFuel fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (source : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (targetId : Nat) (target : RuntimeActivation) (origin : OriginId) (operands : List (CheckedNumericOperand source))
    (world : AcceptedWorld config source.initialized state ambient types live regions pending)
    (frame : AcceptedFrame config accepted source state types) (history : EvaluationHistoryCoverage state ambient pending)
    (selected : targetActivation config targetId state = .ok target state)
    (channels : target.channels = (operands.map CheckedNumericOperand.ty).map Channel.register)
    (reached : ExitReached rootFuel config (.statement (fuel + 1) source.interpretation.environment
      (.returnFrom targetId (operands.map CheckedNumericOperand.expression) origin)) state)
    (carriers : List Carrier) (after : ExecutionState)
    (success : evalOperands fuel config source.interpretation.environment target.channels
      (operands.map CheckedNumericOperand.expression) state = .ok carriers after) :
    execStmt (fuel + 1) config source.interpretation.environment
        (.returnFrom targetId (operands.map CheckedNumericOperand.expression) origin) state =
      .escape ⟨target.act, .nonlocal targetId⟩ carriers state ∧
    ExitReached rootFuel config (.operands fuel source.interpretation.environment target.channels
      (operands.map CheckedNumericOperand.expression)) state ∧
    CarriersLandingReady state target.channels carriers ∧
    landCarriersInto origin target.channels carriers state = .ok () state ∧
    AcceptedWorld config source.initialized state (.returned carriers :: ambient) types live regions
      (⟨target.channels, carriers⟩ :: pending) ∧
    EvaluationHistoryLifecycle state (.returned carriers :: ambient) (⟨target.channels, carriers⟩ :: pending) := by
  obtain ⟨escaped, ready, backed, landed, _, tracked⟩ :=
    checked_register_returnFrom fuel config accepted source state ambient types live regions pending targetId target origin operands
      world frame history selected channels carriers after success
  have setup := exitChannels_registers source.interpretation.environment target origin state
    (operands.map CheckedNumericOperand.ty) (operands.map CheckedNumericOperand.expression) channels (by simp)
  have child : ExitReached rootFuel config (.operands fuel source.interpretation.environment target.channels
      (operands.map CheckedNumericOperand.expression)) state := by
    exact .call reached (.returnFromOperands fuel source.interpretation.environment target targetId
      (operands.map CheckedNumericOperand.expression) origin state state target.channels selected (by simpa only [channels] using setup))
  exact ⟨escaped, child, ready, landed, acceptedWorld_returned config source.initialized state ambient types live regions pending
    target.channels carriers world ready backed, tracked⟩

#print axioms acceptedWorld_returned
#print axioms reached_checked_register_returnFrom_world

end Goose.Proofs.ConstructionAcceptedExecution
