import Goose.Core.Validate
import Goose.GIR.Validate
import Goose.Lower.CoreToGir

namespace Goose.Lower.Validation.Checks

open Goose.Core

def sliceTy : Ty := .slice .mutable (.int .i64)
def refSliceTy : Ty := .ref .mutable sliceTy

def emptyEntry : Impl :=
  { name := "main", params := #[], results := #[], vars := #[],
    body := .mk 0 [] none, summary := .unknown }

def sliceReceiver : Impl :=
  { name := "receiver", params := #[⟨0, .byRef⟩], results := #[],
    vars := #[⟨"p", refSliceTy, .immutable, 0, 0⟩],
    body := .mk 0 [] none, summary := .unknown }

def parameterSlice : Module :=
  { files := #["reference-slice.goose"], types := #[], globals := #[],
    impls := #[emptyEntry, sliceReceiver],
    contexts := #[⟨0, "main", [], [], []⟩,
      ⟨1, "receiver", [(0, [.param 0])], [], [(0, [.param 0])]⟩],
    entry := 0, origins := #[⟨0, 1, "test"⟩] }

def undeclaredSliceSlot : Module :=
  { parameterSlice with
    impls := #[{ emptyEntry with vars := sliceReceiver.vars }],
    contexts := #[⟨0, "main", [(0, [])], [], []⟩] }

def readonlyShrinkBorrow : Module :=
  let owner := Ty.growshrink (.int .i64)
  let main : Impl :=
    { emptyEntry with
      vars := #[⟨"r", .ref .readOnly owner, .immutable, 0, 0⟩],
      body := .mk 0 [.letS 0 (.ref .readOnly (.global 0)) 0] none }
  { files := #["readonly-shrink-borrow.goose"], types := #[],
    globals := #[⟨"g", owner, .immutable, .arrLit owner [], 0⟩],
    impls := #[main], contexts := #[⟨0, "main", [(0, [.global 0])], [], []⟩],
    entry := 0, origins := #[⟨0, 1, "test"⟩], profile := .shrink }

#guard match Core.validate parameterSlice, GIR.validate (lower parameterSlice) with
  | .ok _, .ok _ => true
  | _, _ => false

#guard match Core.validate undeclaredSliceSlot with
  | .ok _ => true
  | _ => false

#guard match GIR.validate (lower undeclaredSliceSlot) with
  | .error e => e.code == .v010 &&
      e.message == "function main: the slot of variable 0 has a type no variable may have"
  | _ => false

#guard match Core.validate readonlyShrinkBorrow with
  | .ok _ => true
  | _ => false

#guard match GIR.validate (lower readonlyShrinkBorrow) with
  | .ok _ => true
  | _ => false

end Goose.Lower.Validation.Checks
