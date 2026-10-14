import Goose.Construct.Eval
import Goose.Construct.Json
import Goose.Construct.Validate
import Goose.Construct.TraceJson
import Goose.Core.Run

namespace Goose.Construct.Run

private def stdout (bytes : ByteArray) : String :=
  Goose.Core.Writer.arr (bytes.data.toList.map (fun byte => Goose.Core.Writer.nat byte.toNat))

private def construction (events : List Core.ConstructionEvent) : String :=
  Goose.Core.Writer.arr (events.map TraceJson.event)

private def originLine (module : Module) (origin : Core.OriginId) : Nat :=
  match module.origins[origin]? with
  | some origin => origin.line
  | none => 0

private def outcome (module : Module) : Core.Outcome → String
  | .returned => "[\"returned\"]"
  | .aborted kind origin =>
      s!"[\"aborted\",{Core.Run.quote kind.tag},{originLine module origin}]"
  | .exited code => s!"[\"exited\",{code}]"

def render (module : Module) : ExecutionResult → String × UInt32
  | .done result bytes events =>
      (s!"[\"done\",{outcome module result},{stdout bytes},{construction events}]", 0)
  | .timeout bytes events =>
      (s!"[\"timeout\",{stdout bytes},{construction events}]", 3)
  | .fault kind => (s!"[\"fault\",{Core.Run.quote kind.tag}]", 4)

def runBytes (settings : Core.Run.Settings) (bytes : ByteArray) : String × UInt32 :=
  match Decode.decodeBytes bytes with
  | .error message => Core.Run.malformed message
  | .ok module =>
      match (if settings.validate then validate module else .ok ()) with
      | .error rejection => Core.Run.rejected rejection
      | .ok () => render module (eval settings.fuel settings.profile module)

def validateBytes (bytes : ByteArray) : String × UInt32 :=
  match Decode.decodeBytes bytes with
  | .error message => Core.Run.malformed message
  | .ok module =>
      match validate module with
      | .error rejection => Core.Run.rejected rejection
      | .ok () => ("[\"ok\"]", 0)

end Goose.Construct.Run
