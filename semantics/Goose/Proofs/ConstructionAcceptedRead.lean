import Goose.Proofs.ConstructionReadTyping

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst Loc)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionExecutionOwnership

def StorageDemandReady (interpretation : RootInterpretation) (liveRoots : RootInst → Prop)
    (roots : List RootRef) : Prop :=
  ∀ root, RootIn interpretation roots root → liveRoots root

theorem readLoc_demanded (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (before after : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (liveRoots : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorldCore config initialized before ambient types liveRoots regions pending)
    (interpretation : RootInterpretation) (roots : List RootRef)
    (ready : StorageDemandReady interpretation liveRoots roots)
    (location : Loc) (target : Ty) (value : Value)
    (rooted : RootIn interpretation roots location.root)
    (typed : LocationTyped types location target)
    (executed : readLoc fuel config.layout location before = .ok value after) :
    after = before ∧ ValueRepresentation target value ∧ PointerTypedValue types target value ∧
      ValueStorageBacked config.layout before value :=
  readLoc_typed fuel config.layout types before after liveRoots world.heap world.layouts world.backing
    location target value (ready location.root rooted) typed executed

#print axioms readLoc_demanded
end Goose.Proofs.ConstructionAcceptedExecution
