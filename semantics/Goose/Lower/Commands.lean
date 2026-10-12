import Goose.Core.Run
import Goose.GIR.Json
import Goose.GIR.Eval
import Goose.GIR.Validate
import Goose.Lower.CoreToGir

/-!
The `lower`, `gir-validate`, `gir-run` and `agree` commands as pure functions
from file bytes to one JSON line and an exit status, in the forms of the Core
commands (`Goose.Core.Run`).
-/

namespace Goose.Lower.Commands

/-- `lower`: validate a Core module, lower it and print the GIR-H module in
the wire encoding, without the line feed that `IO.println` adds again. -/
def lowerBytes (bs : ByteArray) : String × UInt32 :=
  match Core.Decode.decodeBytes bs with
  | .error msg => Core.Run.malformed msg
  | .ok m =>
    match Core.validate m with
    | .error r => Core.Run.rejected r
    | .ok () => ((GIR.Json.write (lower m)).dropEnd 1 |>.toString, 0)

/-- `gir-reencode`: read a GIR-H module and write it again, to check that the
decoder and the writer are inverse on the bytes the writer produces. -/
def girReencodeBytes (bs : ByteArray) : String × UInt32 :=
  match GIR.Json.decodeBytes bs with
  | .error msg => Core.Run.malformed msg
  | .ok m => ((GIR.Json.write m).dropEnd 1 |>.toString, 0)

def rejected (v : GIR.Violation) : String × UInt32 :=
  (s!"[\"rejected\",{Core.Run.quote v.code.tag},{Core.Run.quote v.message}]", 5)

/-- `gir-validate`. -/
def girValidateBytes (bs : ByteArray) : String × UInt32 :=
  match GIR.Json.decodeBytes bs with
  | .error msg => Core.Run.malformed msg
  | .ok m =>
    match GIR.validate m with
    | .error v => rejected v
    | .ok () => ("[\"ok\"]", 0)

def lineOf (m : GIR.Module) (org : Core.OriginId) : Nat :=
  match m.origins[org]? with
  | some o => o.line
  | none => 0

/-- A result in the output forms of `run`, with the line of an abort read from
the GIR module's origin table. -/
def render (m : GIR.Module) : Core.Result → String × UInt32
  | .done .returned out => (s!"[\"done\",[\"returned\"],{Core.Run.quote out}]", 0)
  | .done (.aborted k org) out =>
    (s!"[\"done\",[\"aborted\",{Core.Run.quote k.tag},{lineOf m org}],{Core.Run.quote out}]", 0)
  | .done (.exited code) out => (s!"[\"done\",[\"exited\",{code}],{Core.Run.quote out}]", 0)
  | .timeout out => (s!"[\"timeout\",{Core.Run.quote out}]", 3)
  | .fault k => (s!"[\"fault\",{Core.Run.quote k.tag}]", 4)

/-- `gir-run`. The fuel counts executed instructions, not Core evaluation steps. -/
def girRunBytes (s : Core.Run.Settings) (bs : ByteArray) : String × UInt32 :=
  match GIR.Json.decodeBytes bs with
  | .error msg => Core.Run.malformed msg
  | .ok m =>
    match (if s.validate then GIR.validate m else .ok ()) with
    | .error v => rejected v
    | .ok () => render m (GIR.run s.fuel s.profile m)

/-- One unit of Core fuel buys this many units of GIR fuel: a Core node becomes
several instructions, each of which costs one. -/
def girFuelFactor : Nat := 16

/-- `agree`: validate and run a Core module and a GIR module and compare. A
timeout on either side proves nothing, and a fault on either side is a
disagreement even when both fault alike. -/
def agreeBytes (s : Core.Run.Settings) (coreBytes girBytes : ByteArray) : String × UInt32 :=
  match Core.Decode.decodeBytes coreBytes, GIR.Json.decodeBytes girBytes with
  | .error msg, _ => Core.Run.malformed s!"core module: {msg}"
  | _, .error msg => Core.Run.malformed s!"gir module: {msg}"
  | .ok c, .ok g =>
    match (if s.validate then Core.validate c else .ok ()) with
    | .error r => Core.Run.rejected r
    | .ok () =>
      match (if s.validate then GIR.validate g else .ok ()) with
      | .error v => rejected v
      | .ok () =>
        let cr := Core.eval s.fuel s.profile c
        let gr := GIR.run (s.fuel * girFuelFactor) s.profile g
        match cr, gr with
        | .timeout _, _ | _, .timeout _ => ("[\"inconclusive\"]", 3)
        | _, _ =>
          let (cs, cst) := Core.Run.render c cr
          let (gs, gst) := render g gr
          if cst = 0 && gst = 0 && cs == gs then (s!"[\"agree\",{cs}]", 0)
          else (s!"[\"disagree\",{cs},{gs}]", 6)

end Goose.Lower.Commands
