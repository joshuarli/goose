import Goose.Core.Memory

namespace Goose.Core

abbrev DestinationId := Nat
abbrev StorageId := Nat
abbrev NonlocalTargetId := Nat

inductive Request
  | register
  | value
  | elementRun
  deriving DecidableEq, Repr

def Request.tag : Request → String
  | .register => "register"
  | .value => "value"
  | .elementRun => "element_run"

def Request.ofTag? : String → Option Request
  | "register" => some .register
  | "value" => some .value
  | "element_run" => some .elementRun
  | _ => none

inductive RelocationReason
  | headerRemoval
  | exitValue
  deriving DecidableEq, Repr

def RelocationReason.tag : RelocationReason → String
  | .headerRemoval => "header-removal"
  | .exitValue => "exit-value"

inductive CopySource
  | storage (id : StorageId) (path : List Nat)
  | repeat (destination : DestinationId)
  deriving DecidableEq, Repr

inductive ConstructionEvent
  | begin (destination : DestinationId)
  | write (destination : DestinationId) (index : Nat)
  | publish (destination : DestinationId)
  | copy (source : CopySource) (destination : DestinationId)
  | relocate (destination : DestinationId) (reason : RelocationReason)
  | stage (destination : DestinationId)
  | abandon (destination : DestinationId)
  deriving DecidableEq, Repr

structure ResultDescriptor where
  ty : Ty
  request : Request
  namedLocal : Option VarId
  deriving DecidableEq, Repr

structure NonlocalTarget where
  first : ImplId
  rest : List ImplId
  deriving DecidableEq, Repr

def NonlocalTarget.members (target : NonlocalTarget) : List ImplId :=
  target.first :: target.rest

def NonlocalTarget.contains (target : NonlocalTarget) (implementation : ImplId) : Bool :=
  target.members.contains implementation

structure Destination where
  id : DestinationId
  receiver : Loc
  layout : Ty
  logicalType : Ty
  request : Request
  start : Nat
  owner : ActId
  deriving DecidableEq, Repr

inductive ResultChannel
  | register (receiver : Loc)
  | construct (destination : Destination)
  deriving DecidableEq, Repr

inductive Carrier
  | fixed (value : Val)
  | completed (destination : Destination) (count : Nat)

structure Activation where
  implementation : ImplId
  act : ActId
  vars : Array LocalVar
  scopes : List (Nat × ScopeInst)
  results : List ResultChannel

def nearestTarget? (target : NonlocalTarget) : List Activation → Option Activation
  | [] => none
  | activation :: outer =>
      if target.contains activation.implementation then some activation
      else nearestTarget? target outer

end Goose.Core
