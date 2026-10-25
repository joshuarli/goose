import Goose.GIR.RootBounds
import Goose.Core.Demand

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR

structure AssignmentStoreOccurrence (env : PEnv) (root : DemandNode) (func : Func) (upper : Prov)
    (address value : ValueId) (origin : Option OriginId) where
  localEnv : PEnv
  access : localEnv.access = env.access
  path : List Nat
  place : Place
  expression : Expr
  sourceOrigin : OriginId
  origin_eq : origin = some sourceOrigin
  source : DemandNodeAt root path (.statement (.assign place expression sourceOrigin))
  before : RState
  placeRoots : List RootRef
  placeAfter : RState
  valueRoots : List RootRef
  after : RState
  placeReplay : rpPlace localEnv place before = .ok (placeRoots, placeAfter)
  valueReplay : rpExpr localEnv expression placeAfter = .ok (valueRoots, after)
  checked : checkStore localEnv place valueRoots = .ok ()
  addressBound : address < upper.vals.size
  valueBound : value < upper.vals.size
  addressRefined : GIR.RootsRefine func (rootsAt upper.vals address) placeRoots
  formalAddress : ∀ varId, place = .deref (.read (.var varId)) → localEnv.isRefSliceVar varId = true →
    rootsAt upper.vals address ⊆ [.param varId]
  valueRefined : GIR.RootsRefine func (rootsAt upper.vals value) valueRoots
  referenceTarget : ∃ varId, place = .deref (.read (.var varId)) ∧ localEnv.isRefSliceVar varId = true

structure RebindStoreOccurrence (env : PEnv) (root : DemandNode) (func : Func) (upper : Prov)
    (address value : ValueId) (origin : Option OriginId) where
  localEnv : PEnv
  access : localEnv.access = env.access
  path : List Nat
  varId : VarId
  expression : Expr
  sourceOrigin : OriginId
  origin_eq : origin = some sourceOrigin
  source : DemandNodeAt root path (.statement (.rebind varId expression sourceOrigin))
  before : RState
  valueRoots : List RootRef
  after : RState
  valueReplay : rpExpr localEnv expression before = .ok (valueRoots, after)
  checked : bindRootsV localEnv localEnv.scopes varId valueRoots = .ok ()
  addressBound : address < upper.vals.size
  valueBound : value < upper.vals.size
  addressRoots : rootsAt upper.vals address = [.local varId]
  valueRefined : GIR.RootsRefine func (rootsAt upper.vals value) valueRoots

def StoreOccurrence (env : PEnv) (root : DemandNode) (func : Func) (upper : Prov)
    (address value : ValueId) (origin : Option OriginId) : Prop :=
  Nonempty (AssignmentStoreOccurrence env root func upper address value origin) ∨
    Nonempty (RebindStoreOccurrence env root func upper address value origin)

variable {env other : PEnv} {root : DemandNode} {func : Func} {old next : Prov}
  {address value : ValueId} {origin : Option OriginId}

def AssignmentStoreOccurrence.retained
    (occurrence : AssignmentStoreOccurrence env root func old address value origin)
    (growth : old.vals.size ≤ next.vals.size)
    (retained : ∀ index, index < old.vals.size → rootsAt next.vals index = rootsAt old.vals index) :
    AssignmentStoreOccurrence env root func next address value origin :=
  { occurrence with
    addressBound := Nat.lt_of_lt_of_le occurrence.addressBound growth
    valueBound := Nat.lt_of_lt_of_le occurrence.valueBound growth
    addressRefined := by rw [retained address occurrence.addressBound]; exact occurrence.addressRefined
    formalAddress := by
      intro varId same reference
      rw [retained address occurrence.addressBound]
      exact occurrence.formalAddress varId same reference
    valueRefined := by rw [retained value occurrence.valueBound]; exact occurrence.valueRefined }

def RebindStoreOccurrence.retained
    (occurrence : RebindStoreOccurrence env root func old address value origin)
    (growth : old.vals.size ≤ next.vals.size)
    (retained : ∀ index, index < old.vals.size → rootsAt next.vals index = rootsAt old.vals index) :
    RebindStoreOccurrence env root func next address value origin :=
  { occurrence with
    addressBound := Nat.lt_of_lt_of_le occurrence.addressBound growth
    valueBound := Nat.lt_of_lt_of_le occurrence.valueBound growth
    addressRoots := by rw [retained address occurrence.addressBound]; exact occurrence.addressRoots
    valueRefined := by rw [retained value occurrence.valueBound]; exact occurrence.valueRefined }

theorem StoreOccurrence.retained (occurrence : StoreOccurrence env root func old address value origin)
    (growth : old.vals.size ≤ next.vals.size)
    (retained : ∀ index, index < old.vals.size → rootsAt next.vals index = rootsAt old.vals index) :
    StoreOccurrence env root func next address value origin := by
  rcases occurrence with assigned | rebound
  · obtain ⟨assigned⟩ := assigned
    exact Or.inl ⟨assigned.retained growth retained⟩
  · obtain ⟨rebound⟩ := rebound
    exact Or.inr ⟨rebound.retained growth retained⟩

theorem StoreOccurrence.access_eq (occurrence : StoreOccurrence env root func old address value origin)
    (same : env.access = other.access) : StoreOccurrence other root func old address value origin := by
  rcases occurrence with assigned | rebound
  · obtain ⟨assigned⟩ := assigned
    exact Or.inl ⟨{ assigned with access := assigned.access.trans same }⟩
  · obtain ⟨rebound⟩ := rebound
    exact Or.inr ⟨{ rebound with access := rebound.access.trans same }⟩

#print axioms StoreOccurrence.retained
#print axioms StoreOccurrence.access_eq

end Goose.Lower.Validation.ReplacementContentFlowSource
