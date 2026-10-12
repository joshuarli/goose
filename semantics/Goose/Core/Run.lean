import Goose.Core.Validate
import Goose.Core.Json
import Goose.Core.Eval

/-!
The `goose-semantics run` and `validate` commands as pure functions from file
bytes to one JSON line and an exit status.

Output is a tagged array, never an object:

* `["done",["returned"],OUT]`, `["done",["aborted",KIND,LINE],OUT]` and
  `["done",["exited",CODE],OUT]` with status 0, where `CODE` is a JSON
  integer;
* `["timeout",OUT]` with status 3;
* `["fault",KIND]` with status 4;
* `["malformed",MESSAGE]` with status 2;
* `["rejected",RULE,MESSAGE]` with status 5;
* `["ok"]` with status 0 for `validate`.
-/

namespace Goose.Core.Run

structure Settings where
  profile : NumProfile := .release
  fuel : Nat := 10000000
  validate : Bool := true

def quote (s : String) : String := (Lean.Json.str s).compress

def malformed (msg : String) : String × UInt32 :=
  (s!"[\"malformed\",{quote msg}]", 2)

def rejected (r : Rejection) : String × UInt32 :=
  (s!"[\"rejected\",{quote r.rule.tag},{quote r.message}]", 5)

def lineOf (m : Module) (org : OriginId) : Nat :=
  match m.origins[org]? with
  | some o => o.line
  | none => 0

def render (m : Module) : Result → String × UInt32
  | .done .returned out => (s!"[\"done\",[\"returned\"],{quote out}]", 0)
  | .done (.aborted k org) out =>
    (s!"[\"done\",[\"aborted\",{quote k.tag},{lineOf m org}],{quote out}]", 0)
  | .done (.exited code) out => (s!"[\"done\",[\"exited\",{code}],{quote out}]", 0)
  | .timeout out => (s!"[\"timeout\",{quote out}]", 3)
  | .fault k => (s!"[\"fault\",{quote k.tag}]", 4)

def runBytes (s : Settings) (bs : ByteArray) : String × UInt32 :=
  match Decode.decodeBytes bs with
  | .error msg => malformed msg
  | .ok m =>
    match (if s.validate then validate m else .ok ()) with
    | .error r => rejected r
    | .ok () => render m (eval s.fuel s.profile m)

def validateBytes (bs : ByteArray) : String × UInt32 :=
  match Decode.decodeBytes bs with
  | .error msg => malformed msg
  | .ok m =>
    match validate m with
    | .error r => rejected r
    | .ok () => ("[\"ok\"]", 0)

/-- Read a module file, refusing before reading anything larger than the limit. -/
def readModule (path : System.FilePath) : IO (Except String ByteArray) := do
  try
    let md ← path.metadata
    if md.byteSize.toNat > Decode.maxInputBytes then
      return .error s!"input of {md.byteSize} bytes exceeds {Decode.maxInputBytes}"
    return .ok (← IO.FS.readBinFile path)
  catch e =>
    return .error s!"cannot read {path}: {e}"

end Goose.Core.Run
