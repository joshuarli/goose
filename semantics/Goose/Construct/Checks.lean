import Goose.Construct.TraceJson
import Goose.Construct.Exit

namespace Goose.Construct.Checks
open Goose.Core Goose.Construct

private def decodeTrace (input : String) : Except String (List ConstructionEvent) := do
  TraceJson.decodeConstruction (← Lean.Json.parse input)

private def events : List ConstructionEvent :=
  [.begin 0, .write 0 0, .copy (.storage 3 [1, 2]) 0,
   .copy (.repeat 0) 1, .relocate 0 .headerRemoval, .stage 0,
   .relocate 0 .exitValue, .publish 0, .begin 1, .abandon 1]

private def matchesTrace (input : String) (expected : List ConstructionEvent) : Bool :=
  match decodeTrace input with
  | .ok actual => actual == expected
  | .error _ => false

private def rejectsTrace (input : String) : Bool :=
  match decodeTrace input with
  | .ok _ => false
  | .error _ => true

#guard matchesTrace (TraceJson.construction events) events
#guard rejectsTrace "[\"construction\",[[\"relocate\",0,\"copy\"]]]"
#guard rejectsTrace "[\"construction\",[[\"stage\",0,\"unbounded\"]]]"
#guard rejectsTrace "[\"construction\",[[\"write\",0]]]"
#guard rejectsTrace "[\"construction\",[[\"begin\",-1]]]"
#guard Request.ofTag? "element_run" == some .elementRun
#guard Request.ofTag? "elements" == none

private def activation (implementation act : Nat) : Activation :=
  ⟨implementation, act, #[], [], []⟩

private def recursiveStack : List Activation :=
  [activation 2 4, activation 1 3, activation 2 2, activation 1 1]

#guard (nearestTarget? ⟨1, []⟩ recursiveStack).map (·.act) == some 3
#guard (planExit? ⟨1, []⟩ recursiveStack).map (·.catcher.act) == some 3
#guard (planExit? ⟨1, []⟩ recursiveStack).map (·.discarded.map (·.act)) == some [4]
#guard (planExit? ⟨1, []⟩ recursiveStack).map (·.outer.map (·.act)) == some [2, 1]
#guard (planExit? ⟨9, []⟩ recursiveStack).isNone

end Goose.Construct.Checks
