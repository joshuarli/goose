import Goose.Proofs.ConstructionAcceptedByteEvaluation
import Goose.Proofs.ConstructionAcceptedStaticBytes

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionExecutionOwnership

theorem FreshDestinationFrame.acceptedFrame {config : EvalConfig} {accepted : AcceptedModule config}
    {source : ConstructionSourceFrame} {before after : ExecutionState} {types : RootTypes}
    (frame : FreshDestinationFrame before after) (valid : AcceptedFrame config accepted source before types) :
    AcceptedFrame config accepted source after types := by
  have objects := congrArg ExecutionState.objects frame.outer
  have ordinals := congrArg ExecutionState.objectOrdinals frame.outer
  have acts := congrArg ExecutionState.nextAct frame.outer
  have scopes := congrArg ExecutionState.nextScope frame.outer
  refine ⟨valid.compatible, ?_, ?_, valid.aliases, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [acts] using valid.frontier
  · simpa only [scopes] using valid.scopeFrontier
  · intro var member
    obtain ⟨descriptor, root, value, declared, resolved, found, represented⟩ := valid.locals var member
    exact ⟨descriptor, root, value, declared, rootOf_transfer source.interpretation var before after root resolved,
      by rw [objects]; exact found, represented⟩
  · intro var member descriptor root declared resolved
    exact valid.localTypes var member descriptor root declared
      (rootOf_transfer source.interpretation var after before root resolved)
  · intro var uninitialized root resolved
    obtain ⟨absent, ordinal⟩ := valid.uninitializedLocals var uninitialized root
      (rootOf_transfer source.interpretation var after before root resolved)
    exact ⟨by rw [objects]; exact absent, by rw [ordinals]; exact ordinal⟩
  · intro global future within
    obtain ⟨absent, ordinal⟩ := valid.futureGlobals global future within
    exact ⟨by rw [objects]; exact absent, by rw [ordinals]; exact ordinal⟩
  · intro var member root value resolved found
    exact valid.direct var member root value (rootOf_transfer source.interpretation var after before root resolved)
      (by rw [objects] at found; exact found)
  · intro fuel var member roots annotated root location value resolved found read interior reference
    have prior := rootOf_transfer source.interpretation var after before root resolved
    have oldFound : before.objects.lookup root = some (.ref location) := by rw [objects] at found; exact found
    have priorRead := readLoc_directReference_transfer fuel config.layout location after before value interior
      (by rw [objects]) read reference
    exact valid.contents fuel var member roots annotated root location value prior oldFound priorRead interior reference

theorem evalValue_checkedByteOwner_world (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (before after : ExecutionState) (value : Value)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (bytes : List UInt8) (origin : Goose.Core.OriginId) (ty : Ty) (roots : List RootRef)
    (typingAfter : Nat) (rootsAfter : RState) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types)
    (checked : CheckedValue frame (.bytes (.varr (.int .u8)) bytes origin) ty roots typingAfter rootsAfter)
    (executed : evalValue (fuel + 2) config frame.interpretation.environment
      (.bytes (.varr (.int .u8)) bytes origin) before = .ok value after) :
    AcceptedWorld config frame.initialized after ambient types live regions pending ∧
      AcceptedFrame config accepted frame after types ∧
      AcceptedValue config.layout types frame.interpretation after ty roots value := by
  have typing := checked.typing
  cases h : frame.typingFuel with
  | zero => rw [h] at typing; change Except.error _ = Except.ok _ at typing; cases typing
  | succ typeFuel =>
    simp only [h, typeExpr, pure] at typing
    obtain ⟨⟨rfl, _⟩, _⟩ := typing
    obtain ⟨nextWorld, ⟨nextFrame⟩, stored, same, backed, storage, named, valueType⟩ :=
      evalValue_byteOwner_world fuel config frame.initialized frame.interpretation.environment bytes origin before after
        value ambient types live regions pending world executed
    subst value
    refine ⟨nextWorld, nextFrame.acceptedFrame source, ?_⟩
    refine ⟨.stored _ stored rfl valueType, .stored _ stored, .stored stored backed, ?_⟩
    intro location reference
    cases reference

#print axioms FreshDestinationFrame.acceptedFrame
#print axioms evalValue_checkedByteOwner_world

end Goose.Proofs.ConstructionAcceptedExecution
