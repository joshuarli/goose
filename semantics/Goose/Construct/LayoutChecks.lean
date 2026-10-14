import Goose.Construct.Layout

namespace Goose.Construct.LayoutChecks

private def module : Module := ⟨#[], #[], #[], #[], #[], 0, #[], #[], #[]⟩
private def bytes (values : List Nat) : ByteArray := ⟨(values.map UInt8.ofNat).toArray⟩

private def intervalMatches (result : Except LayoutFault (Nat × Nat)) (expected : Nat × Nat) : Bool :=
  match result with | .ok value => value == expected | .error _ => false

private def endsAt (ty : Ty) (input : ByteArray) (endOffset : Nat) : Bool :=
  match packedEnd 256 module ty input 0 with
  | .ok actual => actual == endOffset
  | .error _ => false

private def nestedBytes : ByteArray := bytes [2, 0, 0, 0, 2, 0, 0, 0, 0, 255, 1, 0, 0, 0, 128]

#guard endsAt (.varr (.varr (.int .u8))) nestedBytes 15
#guard intervalMatches (elementInterval 256 module nestedBytes ⟨4, 2, .varr (.int .u8)⟩ 0) (4, 10)
#guard intervalMatches (elementInterval 256 module nestedBytes ⟨4, 2, .varr (.int .u8)⟩ 1) (10, 15)
#guard intervalMatches (sampledInterval 256 module nestedBytes ⟨4, 2, .varr (.int .u8)⟩) (4, 15)
#guard endsAt (.arr (.varr (.int .u8)) 2) (bytes [2, 0, 0, 0, 0, 255, 1, 0, 0, 0, 128]) 11
#guard match elementInterval 256 module nestedBytes ⟨4, 2, .varr (.int .u8)⟩ 2 with
  | .error .bounds => true | _ => false
#guard match packedEnd 256 module (.varr (.int .u8)) (bytes [3, 0, 0, 0, 1, 2]) 0 with
  | .error .bounds => true | _ => false
#guard match readCount (bytes [1, 0, 0]) 0 with
  | .error .bounds => true | _ => false
#guard !endsAt (.limited (.varr (.int .u8)) 2) nestedBytes 15

end Goose.Construct.LayoutChecks
