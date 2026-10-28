import Goose.Proofs.ConstructionAcceptedSource
import Goose.Proofs.ConstructionRootedBackingPrefixes
import Goose.Proofs.ExitExecutionLiveCarriers
import Goose.Proofs.ConstructionRootCorrespondenceLayout

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
  mutableDestinations : List Nat

structure ReceivingProtection (layout : LayoutEnv) (state : ExecutionState)
    (liveRoots : RootInst → Prop) (region : ReceivingRegion) : Prop where
  present : ∃ row, state.construction.destinations[region.destination]? = some row
  observations : RootedBackingObservations layout state
    (fun root => liveRoots root ∧ ¬ region.mutableRoots root) region.limit
  cutoff : ∀ row, state.construction.destinations[region.destination]? = some row →
    region.limit row.storage ≤ row.rollbackEnd
  landing : ∀ row, state.construction.destinations[region.destination]? = some row →
    region.limit row.storage ≤ row.capability.start
  authority : region.destination ∈ region.mutableDestinations
  authorityBound : ∀ id ∈ region.mutableDestinations, id < state.construction.destinations.size
  names : ∀ root, liveRoots root → ¬ region.mutableRoots root → ∀ value,
    state.objects.lookup root = some value → ∀ stored, StoredOccurrence value stored →
    ∀ id, stored.destination = some id → id ∉ region.mutableDestinations

structure PendingCarrierFrame where
  channels : List Channel
  carriers : List Carrier

structure AcceptedWorldCore (config : EvalConfig) (initialized : Nat) (state : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (liveRoots : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) : Prop where
  ownership : OwnershipExecutionContext state ambient
  globals : GlobalRepresentations config.module initialized state
  globalTypes : ∀ id descriptor, config.module.globals[id]? = some descriptor →
    types (.global id) = some descriptor.ty
  layouts : ∀ root ty, types root = some ty → LayoutConforms config.layout ty
  typeFrontier : ∀ act scope id ty, types (.local act scope id) = some ty →
    act < state.nextAct ∧ scope < state.nextScope
  syntheticFrontier : ∀ id ty, types (.global id) = some ty → config.module.globals.size ≤ id →
    id < config.module.globals.size + state.nextScope
  heap : ∀ root ty value, types root = some ty → state.objects.lookup root = some value →
    ValueRepresentation ty value ∧ PointerTypedValue types ty value
  objectsRegistered : ∀ root value, state.objects.lookup root = some value → ∃ ty, types root = some ty
  ordinalsRegistered : ∀ root ordinal, state.objectOrdinals.lookup root = some ordinal → ∃ ty, types root = some ty
  backing : RootedBackingState config.layout state liveRoots
  protections : ∀ region ∈ regions, ReceivingProtection config.layout state liveRoots region
  carriers : ∀ frame ∈ pending, CarriersLandingReady state frame.channels frame.carriers ∧
    ∀ carrier ∈ frame.carriers, CarrierResultBacking config.layout state carrier

structure AcceptedWorld (config : EvalConfig) (initialized : Nat) (state : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (liveRoots : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) : Prop extends
    AcceptedWorldCore config initialized state ambient types liveRoots regions pending where
  globalLive : ∀ id, id < initialized → liveRoots (.global id)

structure ReceivingWorld (config : EvalConfig) (initialized : Nat) (state : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (liveRoots : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (surrendered : List RootInst) : Prop extends
    AcceptedWorldCore config initialized state ambient types liveRoots regions pending where
  globalLive : ∀ id, id < initialized → RootInst.global id ∉ surrendered → liveRoots (.global id)

structure AcceptedFrame (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (state : ExecutionState) (types : RootTypes) : Prop where
  compatible : SourceFrameCompatible accepted frame
  frontier : RootFrontier frame.interpretation state.nextAct
  aliases : AliasComplete frame.interpretation frame.source.aliases
  locals : LocalRepresentations state frame.interpretation.environment frame.typing.visible
  localTypes : ∀ id ∈ frame.typing.visible, ∀ descriptor root,
    frame.typing.variables[id]? = some descriptor →
    rootOf frame.interpretation.environment id state = .ok root state → types root = some descriptor.ty
  uninitializedLocals : ∀ id, frame.rootCursor.nextVar ≤ id ∨ id ∈ frame.source.initializing → ∀ root,
    rootOf frame.interpretation.environment id state = .ok root state →
    state.objects.lookup root = none ∧ state.objectOrdinals.lookup root = none
  futureGlobals : ∀ id, frame.initialized ≤ id → id < config.module.globals.size →
    state.objects.lookup (.global id) = none ∧ state.objectOrdinals.lookup (.global id) = none
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

theorem initial_acceptedWorld (config : EvalConfig) (accepted : validate config.module = .ok ()) :
    AcceptedWorld config 0 .initial [] (declaredRootTypes config.module) (fun _ => False) [] [] := by
  refine ⟨⟨initial_ownershipExecutionContext, ⟨Nat.zero_le _, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    initial_rootedBackingState config.layout _, ?_, ?_⟩, ?_⟩
  · intro id bound
    exact (Nat.not_lt_zero id bound).elim
  · intro id descriptor present
    simp only [declaredRootTypes, present, Option.map_some]
  · intro root ty present
    cases root with
    | global id =>
      cases declared : config.module.globals[id]? with
      | none => simp only [declaredRootTypes, declared, Option.map_none, reduceCtorEq] at present
      | some descriptor =>
        have same : descriptor.ty = ty := by
          simpa only [declaredRootTypes, declared, Option.map_some, Option.some.injEq] using present
        subst ty
        exact validated_global_layoutConforms config.module id descriptor accepted declared
    | «local» act scope id => cases present
  · intro act scope id ty present
    cases present
  · intro id ty typed outside
    have absent : config.module.globals[id]? = none := Array.getElem?_eq_none_iff.mpr outside
    simp only [declaredRootTypes, absent, Option.map_none, reduceCtorEq] at typed
  · intro root ty value typed present
    cases present
  · intro root value present
    cases present
  · intro root ordinal present
    cases present
  · intro region present
    cases present
  · intro frame present
    cases present
  · intro id bound
    exact (Nat.not_lt_zero id bound).elim

theorem AcceptedWorld.synthetic_keys_fresh {config : EvalConfig} {initialized : Nat} {state : ExecutionState}
    {ambient : OwnershipAmbient} {types : RootTypes} {liveRoots : RootInst → Prop}
    {regions : List ReceivingRegion} {pending : List PendingCarrierFrame}
    (world : AcceptedWorld config initialized state ambient types liveRoots regions pending) (id : Nat)
    (future : config.module.globals.size + state.nextScope ≤ id) :
    state.objects.lookup (.global id) = none ∧ state.objectOrdinals.lookup (.global id) = none := by
  constructor
  · cases found : state.objects.lookup (.global id) with
    | none => rfl
    | some value =>
      obtain ⟨ty, registered⟩ := world.objectsRegistered (.global id) value found
      have bound := world.syntheticFrontier id ty registered (by omega)
      exact (Nat.not_lt_of_ge future bound).elim
  · cases found : state.objectOrdinals.lookup (.global id) with
    | none => rfl
    | some ordinal =>
      obtain ⟨ty, registered⟩ := world.ordinalsRegistered (.global id) ordinal found
      have bound := world.syntheticFrontier id ty registered (by omega)
      exact (Nat.not_lt_of_ge future bound).elim

theorem AcceptedWorld.local_keys_fresh {config : EvalConfig} {initialized : Nat} {state : ExecutionState}
    {ambient : OwnershipAmbient} {types : RootTypes} {liveRoots : RootInst → Prop}
    {regions : List ReceivingRegion} {pending : List PendingCarrierFrame}
    (world : AcceptedWorld config initialized state ambient types liveRoots regions pending) (act scope id : Nat)
    (future : state.nextAct ≤ act ∨ state.nextScope ≤ scope) :
    state.objects.lookup (.local act scope id) = none ∧ state.objectOrdinals.lookup (.local act scope id) = none := by
  constructor
  · cases found : state.objects.lookup (.local act scope id) with
    | none => rfl
    | some value =>
      obtain ⟨ty, registered⟩ := world.objectsRegistered (.local act scope id) value found
      have bound := world.typeFrontier act scope id ty registered
      rcases future with acts | scopes
      · exact (Nat.not_lt_of_ge acts bound.1).elim
      · exact (Nat.not_lt_of_ge scopes bound.2).elim
  · cases found : state.objectOrdinals.lookup (.local act scope id) with
    | none => rfl
    | some ordinal =>
      obtain ⟨ty, registered⟩ := world.ordinalsRegistered (.local act scope id) ordinal found
      have bound := world.typeFrontier act scope id ty registered
      rcases future with acts | scopes
      · exact (Nat.not_lt_of_ge acts bound.1).elim
      · exact (Nat.not_lt_of_ge scopes bound.2).elim

#print axioms initial_acceptedWorld
#print axioms AcceptedWorld.synthetic_keys_fresh
#print axioms AcceptedWorld.local_keys_fresh

end Goose.Proofs.ConstructionAcceptedExecution
