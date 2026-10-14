import Goose.Construct.Destination
import Goose.Construct.Layout
import Goose.Core.Eval

namespace Goose.Construct
open Goose.Core

structure StoredValue where
  storage : StorageId
  start : Nat
  ty : Ty
  count : Nat
  destination : Option DestinationId := none
  deriving Repr

inductive Value
  | int (ty : IntTy) (value : Int)
  | bool (value : Bool)
  | unit
  | fixed (elements : Array Value)
  | record (id : StructId) (fields : Array Value)
  | ref (location : Loc)
  | slice (location : Loc) (start count : Nat)
  | stored (value : StoredValue)
  deriving Repr, Inhabited

inductive Carrier
  | register (value : Value)
  | completed (destination : DestinationId)
  deriving Repr

inductive Channel
  | register (ty : Ty)
  | construct (destination : DestinationId)
  deriving Repr

inductive ExecutionResult
  | done (outcome : Core.Outcome) (stdout : ByteArray) (construction : List ConstructionEvent)
  | timeout (stdout : ByteArray) (construction : List ConstructionEvent)
  | fault (kind : Core.FaultKind)

structure RuntimeActivation where
  implementation : ImplId
  act : ActId
  vars : Array LocalVar
  scopes : List (Nat × ScopeInst)
  channels : List Channel
  deriving Repr

structure ExecutionState where
  objects : List (RootInst × Value)
  construction : ConstructionState
  nextAct : Nat
  nextScope : Nat
  activations : List RuntimeActivation

def ExecutionState.initial : ExecutionState := ⟨[], .initial, 0, 0, []⟩

inductive ExecutionStep (α : Type)
  | ok (value : α) (state : ExecutionState)
  | stop (reason : Core.Stop) (state : ExecutionState)
  | escape (activation : ActId) (carriers : List Carrier) (state : ExecutionState)

abbrev EvalM (α : Type) := ExecutionState → ExecutionStep α

namespace EvalM
instance : Monad EvalM where
  pure value state := .ok value state
  bind action next state :=
    match action state with
    | .ok value state' => next value state'
    | .stop reason state' => .stop reason state'
    | .escape activation carriers state' => .escape activation carriers state'

def get : EvalM ExecutionState := fun state => .ok state state

def set (state : ExecutionState) : EvalM Unit := fun _ => .ok () state

def stop (reason : Core.Stop) : EvalM α := fun state => .stop reason state
end EvalM

def liftConstruction (origin : OriginId) (action : ConstructionM α) : EvalM α := fun state =>
  match action state.construction with
  | .ok value construction => .ok value { state with construction := construction }
  | .fault kind construction =>
      let reason := match kind with
        | .capacity => Core.Stop.abort .capacity origin
        | .storage => Core.Stop.fault .danglingRoot
        | .destination => Core.Stop.fault .unbound
        | .ownership | .protocol => Core.Stop.fault .flow
      .stop reason { state with construction := construction }

end Goose.Construct
