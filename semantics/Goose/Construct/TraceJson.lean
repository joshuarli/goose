import Goose.Core.Construction
import Goose.Core.Json
import Goose.Core.Writer

namespace Goose.Construct.TraceJson
open Goose.Core Lean

private def numbers (values : List Nat) : String :=
  Writer.arr (values.map Writer.nat)

def source : CopySource → String
  | .storage id path => Writer.rec "storage" [Writer.nat id, numbers path]
  | .repeat destination => Writer.rec "repeat" [Writer.nat destination]

def event : ConstructionEvent → String
  | .begin d => Writer.rec "begin" [Writer.nat d]
  | .write d i => Writer.rec "write" [Writer.nat d, Writer.nat i]
  | .publish d => Writer.rec "publish" [Writer.nat d]
  | .copy src d => Writer.rec "copy" [source src, Writer.nat d]
  | .relocate d reason => Writer.rec "relocate" [Writer.nat d, Writer.str reason.tag]
  | .stage d => Writer.rec "stage" [Writer.nat d, Writer.str "capacity-check"]
  | .abandon d => Writer.rec "abandon" [Writer.nat d]

def construction (events : List ConstructionEvent) : String :=
  Writer.rec "construction" [Writer.arr (events.map event)]

private def record (json : Json) : Except String (String × Array Json) := do
  let values ← Decode.asArr json "construction record"
  match values[0]? with
  | none => .error "construction record: empty record"
  | some tag => return (← Decode.asStr tag "construction tag", values.extract 1 values.size)

private def natural (json : Json) : Except String Nat :=
  Decode.asNat json "construction ordinal"

def decodeSource (json : Json) : Except String CopySource := do
  let (tag, fields) ← record json
  match tag, fields.toList with
  | "storage", [id, path] =>
      let ids ← Decode.asArr path "copy source path"
      return .storage (← natural id) (← ids.toList.mapM natural)
  | "repeat", [destination] => return .repeat (← natural destination)
  | _, _ => .error "copy source: unknown tag or wrong arity"

def decodeEvent (json : Json) : Except String ConstructionEvent := do
  let (tag, fields) ← record json
  match tag, fields.toList with
  | "begin", [d] => return .begin (← natural d)
  | "write", [d, i] => return .write (← natural d) (← natural i)
  | "publish", [d] => return .publish (← natural d)
  | "copy", [src, d] => return .copy (← decodeSource src) (← natural d)
  | "relocate", [d, reason] =>
      let reason ← Decode.asStr reason "relocation reason"
      let reason ← match reason with
        | "header-removal" => pure RelocationReason.headerRemoval
        | "exit-value" => pure RelocationReason.exitValue
        | _ => .error "relocation: unknown reason"
      return .relocate (← natural d) reason
  | "stage", [d, reason] =>
      if (← Decode.asStr reason "staging reason") != "capacity-check" then
        .error "stage: unknown reason"
      else return .stage (← natural d)
  | "abandon", [d] => return .abandon (← natural d)
  | _, _ => .error "construction event: unknown tag or wrong arity"

def decodeConstruction (json : Json) : Except String (List ConstructionEvent) := do
  let (tag, fields) ← record json
  match tag, fields.toList with
  | "construction", [events] =>
      let events ← Decode.asArr events "construction events"
      events.toList.mapM decodeEvent
  | _, _ => .error "construction trace: unknown tag or wrong arity"

end Goose.Construct.TraceJson
