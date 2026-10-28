import Goose.Proofs.ConstructionStdoutOwnership
import Goose.Proofs.ConstructionStdoutBacking
import Goose.Proofs.ConstructionAcceptedCallerContents

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation

theorem AcceptedWorld.appendStdout (config : EvalConfig) (initialized : Nat) (state : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (bytes : ByteArray)
    (world : AcceptedWorld config initialized state ambient types live regions pending) :
    AcceptedWorld config initialized (appendStdoutState bytes state) ambient types live regions pending := by
  refine ⟨⟨?_, world.globals, world.globalTypes, world.layouts, world.typeFrontier,
    world.syntheticFrontier, world.heap, world.objectsRegistered, world.ordinalsRegistered,
    appendStdout_rooted_backing bytes state config.layout live world.backing, ?_, ?_⟩, world.globalLive⟩
  · exact appendStdout_context state ambient bytes world.ownership
  · intro region member
    exact appendStdout_protection bytes state config.layout live region (world.protections region member)
  · intro carrierFrame member
    obtain ⟨ready, backed⟩ := world.carriers carrierFrame member
    exact ⟨appendStdout_carriers_ready bytes state carrierFrame.channels carrierFrame.carriers ready,
      fun carrier present => appendStdout_carrier_backing bytes state config.layout carrier (backed carrier present)⟩

theorem AcceptedFrame.appendStdout {config : EvalConfig} {accepted : AcceptedModule config}
    {frame : ConstructionSourceFrame} {state : ExecutionState} {types : RootTypes}
    (source : AcceptedFrame config accepted frame state types) (bytes : ByteArray) :
    AcceptedFrame config accepted frame (appendStdoutState bytes state) types := by
  exact source.afterFreshActivation (by exact Nat.le_refl _) (by exact Nat.le_refl _) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

#print axioms AcceptedWorld.appendStdout
#print axioms AcceptedFrame.appendStdout
end Goose.Proofs.ConstructionAcceptedExecution
