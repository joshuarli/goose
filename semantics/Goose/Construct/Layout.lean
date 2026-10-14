import Goose.Construct.Syntax

namespace Goose.Construct

def fixedByteSize? (module : Module) : Ty → Option Nat
  | .int ty => some (ty.bits / 8)
  | .bool => some 1
  | .arr element count => (fixedByteSize? module element).map (count * ·)
  | .structT id fields => do
      if module.structType? id != some (.structT id fields) then none
      else (module.structs[id]?).map (·.byteSize)
  | _ => none

inductive LayoutFault
  | bounds
  | type
  | fuel
  deriving DecidableEq, Repr

def readCount (bytes : ByteArray) (start : Nat) : Except LayoutFault Nat := do
  if start + 4 > bytes.size then throw .bounds
  let mut count := 0
  for offset in [0:4] do
    let some byte := bytes.data[start + offset]? | throw .bounds
    count := count + byte.toNat * 2 ^ (8 * offset)
  pure count

mutual
def packedEnd : Nat → Module → Ty → ByteArray → Nat → Except LayoutFault Nat
  | 0, _, _, _, _ => .error .fuel
  | fuel + 1, module, ty, bytes, start => do
      match fixedByteSize? module ty with
      | some count =>
          if start + count > bytes.size then throw .bounds
          pure (start + count)
      | none => match ty with
        | .varr element =>
            let count ← readCount bytes start
            elementsEnd fuel module element count bytes (start + 4)
        | .arr element count => elementsEnd fuel module element count bytes start
        | _ => throw .type

def elementsEnd : Nat → Module → Ty → Nat → ByteArray → Nat → Except LayoutFault Nat
  | 0, _, _, _, _, _ => .error .fuel
  | _fuel + 1, _, _, 0, _, start => .ok start
  | fuel + 1, module, element, count + 1, bytes, start => do
      let next ← packedEnd fuel module element bytes start
      elementsEnd fuel module element count bytes next
end

structure SampledRun where
  byteStart : Nat
  count : Nat
  element : Ty
  deriving DecidableEq, Repr

def samplePacked (ty : Ty) (bytes : ByteArray) (start : Nat) : Except LayoutFault SampledRun :=
  match ty with
  | .varr element => do
      let count ← readCount bytes start
      pure ⟨start + 4, count, element⟩
  | .arr element count => pure ⟨start, count, element⟩
  | _ => .error .type

def elementInterval (fuel : Nat) (module : Module) (bytes : ByteArray)
    (run : SampledRun) (index : Nat) : Except LayoutFault (Nat × Nat) := do
  if index ≥ run.count then throw .bounds
  let start ← elementsEnd fuel module run.element index bytes run.byteStart
  let finish ← packedEnd fuel module run.element bytes start
  pure (start, finish)

def sampledInterval (fuel : Nat) (module : Module) (bytes : ByteArray)
    (run : SampledRun) : Except LayoutFault (Nat × Nat) := do
  let finish ← elementsEnd fuel module run.element run.count bytes run.byteStart
  pure (run.byteStart, finish)

end Goose.Construct
