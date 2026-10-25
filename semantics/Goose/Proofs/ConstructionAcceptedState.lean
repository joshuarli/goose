import Goose.Proofs.ConstructionAcceptedSource
import Goose.Proofs.ConstructionRootedBackingPrefixes
import Goose.Proofs.ExitExecutionLiveCarriers

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst Loc)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

abbrev RootTypes := RootInst → Option Ty

inductive TypePath : Ty → List Nat → Ty → Prop
  | root (ty : Ty) : TypePath ty [] ty
  | element (owner element target : Ty) (index : Nat) (path : List Nat)
      (sequence : elementType owner = some element) (tail : TypePath element path target) :
      TypePath owner (index :: path) target
  | field (id : Nat) (fields : TyList) (index : Nat) (field target : Ty) (path : List Nat)
      (selected : fields.toList[index]? = some field) (tail : TypePath field path target) :
      TypePath (.structT id fields) (index :: path) target

def LocationTyped (types : RootTypes) (location : Loc) (ty : Ty) : Prop :=
  ∃ rootType, types location.root = some rootType ∧ TypePath rootType location.path ty

inductive PointerTypedValue (types : RootTypes) : Ty → Value → Prop
  | integer (ty : Goose.Core.IntTy) (value : Int) : PointerTypedValue types (.int ty) (.int ty value)
  | boolean (value : Bool) : PointerTypedValue types .bool (.bool value)
  | unit : PointerTypedValue types .unit .unit
  | reference (mutability : Goose.Core.Mutability) (ty : Ty) (location : Loc)
      (target : LocationTyped types location ty) : PointerTypedValue types (.ref mutability ty) (.ref location)
  | slice (mutability : Goose.Core.Mutability) (ty owner : Ty) (location : Loc) (start count : Nat)
      (target : LocationTyped types location owner) (sequence : elementType owner = some ty) :
      PointerTypedValue types (.slice mutability ty) (.slice location start count)
  | array (element : Ty) (count : Nat) (values : Array Value)
      (children : ∀ value ∈ values.toList, PointerTypedValue types element value) :
      PointerTypedValue types (.arr element count) (.fixed values)
  | record (id : Nat) (fields : TyList) (values : Array Value)
      (children : ∀ (index : Nat) (ty : Ty) (value : Value), fields.toList[index]? = some ty → values[index]? = some value →
        PointerTypedValue types ty value) : PointerTypedValue types (.structT id fields) (.record id values)
  | stored (ty : Ty) (value : StoredValue) : PointerTypedValue types ty (.stored value)

structure ReceivingRegion where
  destination : Nat
  mutableRoots : RootInst → Prop
  limit : Nat → Nat

structure ReceivingProtection (layout : LayoutEnv) (state : ExecutionState)
    (liveRoots : RootInst → Prop) (region : ReceivingRegion) : Prop where
  present : ∃ row, state.construction.destinations[region.destination]? = some row
  observations : RootedBackingObservations layout state
    (fun root => liveRoots root ∧ ¬ region.mutableRoots root) region.limit
  cutoff : ∀ row, state.construction.destinations[region.destination]? = some row →
    region.limit row.storage ≤ row.rollbackEnd
  landing : ∀ row, state.construction.destinations[region.destination]? = some row →
    region.limit row.storage ≤ row.capability.start

structure PendingCarrierFrame where
  channels : List Channel
  carriers : List Carrier

structure AcceptedWorld (config : EvalConfig) (initialized : Nat) (state : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (liveRoots : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) : Prop where
  ownership : OwnershipExecutionContext state ambient
  globals : GlobalRepresentations config.module initialized state
  globalLive : ∀ id, id < initialized → liveRoots (.global id)
  globalTypes : ∀ id descriptor, config.module.globals[id]? = some descriptor →
    types (.global id) = some descriptor.ty
  typeFrontier : ∀ act scope id ty, types (.local act scope id) = some ty →
    act < state.nextAct ∧ scope < state.nextScope
  heap : ∀ root ty value, types root = some ty → state.objects.lookup root = some value →
    ValueRepresentation ty value ∧ PointerTypedValue types ty value
  backing : RootedBackingState config.layout state liveRoots
  protections : ∀ region ∈ regions, ReceivingProtection config.layout state liveRoots region
  carriers : ∀ frame ∈ pending, CarriersLandingReady state frame.channels frame.carriers ∧
    ∀ carrier ∈ frame.carriers, CarrierResultBacking config.layout state carrier

structure AcceptedFrame (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (state : ExecutionState) (types : RootTypes) : Prop where
  compatible : SourceFrameCompatible accepted frame
  frontier : RootFrontier frame.interpretation state.nextAct
  aliases : AliasComplete frame.interpretation frame.source.aliases
  locals : LocalRepresentations state frame.interpretation.environment frame.typing.visible
  localTypes : ∀ id ∈ frame.typing.visible, ∀ descriptor root,
    frame.typing.variables[id]? = some descriptor →
    rootOf frame.interpretation.environment id state = .ok root state → types root = some descriptor.ty
  direct : LocalRootCorrespondence frame.interpretation frame.source.ctx frame.typing.visible state
  contents : ∀ fuel, ContentRootCorrespondence frame.interpretation frame.source.ctx
    frame.typing.visible fuel config.layout state

structure AcceptedValue (layout : LayoutEnv) (types : RootTypes) (interpretation : RootInterpretation)
    (state : ExecutionState) (ty : Ty) (roots : List RootRef) (value : Value) : Prop where
  represented : ValueRepresentation ty value
  pointers : PointerTypedValue types ty value
  backed : ValueStorageBacked layout state value
  direct : DirectValueRooted interpretation roots value

def declaredRootTypes (module : Module) : RootTypes
  | .global id => (module.globals[id]?).map (·.ty)
  | .local _ _ _ => none

theorem initial_acceptedWorld (config : EvalConfig) :
    AcceptedWorld config 0 .initial [] (declaredRootTypes config.module) (fun _ => False) [] [] := by
  refine ⟨initial_ownershipExecutionContext, ⟨Nat.zero_le _, ?_⟩, ?_, ?_, ?_, ?_,
    initial_rootedBackingState config.layout _, ?_, ?_⟩
  · intro id bound
    exact (Nat.not_lt_zero id bound).elim
  · intro id bound
    exact (Nat.not_lt_zero id bound).elim
  · intro id descriptor present
    simp only [declaredRootTypes, present, Option.map_some]
  · intro act scope id ty present
    cases present
  · intro root ty value typed present
    cases present
  · intro region present
    cases present
  · intro frame present
    cases present

#print axioms initial_acceptedWorld

end Goose.Proofs.ConstructionAcceptedExecution
