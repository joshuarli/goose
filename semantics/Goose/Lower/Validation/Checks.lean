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

def readonlyReferenceLocal : Module :=
  let main : Impl :=
    { emptyEntry with
      vars := #[⟨"r", .ref .readOnly (.int .i64), .immutable, 0, 0⟩],
      body := .mk 0 [.letS 0 (.ref .mutable (.global 0)) 0] none }
  { files := #["readonly-reference-local.goose"], types := #[],
    globals := #[⟨"g", .int .i64, .mutable, .lit .i64 1, 0⟩],
    impls := #[main], contexts := #[⟨0, "main", [(0, [.global 0])], [], []⟩],
    entry := 0, origins := #[⟨0, 1, "test"⟩] }

def readonlyReferenceRebind : Module :=
  { readonlyReferenceLocal with
    impls := readonlyReferenceLocal.impls.modify 0 fun impl =>
      { impl with
        vars := impl.vars.modify 0 fun var => { var with kind := .mutable },
        body := .mk 0 [.letS 0 (.ref .readOnly (.global 0)) 0,
          .rebind 0 (.ref .mutable (.global 0)) 0] none } }

def readonlyReferenceResult : Module :=
  let receiver : Impl :=
    { emptyEntry with
      name := "receiver", results := #[.ref .readOnly (.int .i64)],
      body := .mk 0 [.ret (some (.ref .mutable (.global 0))) 0] none }
  { readonlyReferenceLocal with
    impls := #[emptyEntry, receiver],
    contexts := #[⟨0, "main", [], [], []⟩,
      ⟨1, "receiver", [], [[.global 0]], []⟩] }

def readonlySliceLocal : Module :=
  let owner := Ty.arr (.int .i64) 1
  let main : Impl :=
    { emptyEntry with
      vars := #[⟨"s", .slice .readOnly (.int .i64), .immutable, 0, 0⟩],
      body := .mk 0 [.letS 0 (.slice .mutable (.of (.global 0)) .omitted .omitted 0) 0] none }
  { files := #["readonly-slice-local.goose"], types := #[],
    globals := #[⟨"g", owner, .mutable, .arrLit owner [.lit .i64 1], 0⟩],
    impls := #[main], contexts := #[⟨0, "main", [(0, [.global 0])], [], []⟩],
    entry := 0, origins := #[⟨0, 1, "test"⟩] }

def specializedSummary : Module :=
  let summary : SummaryAnn := .known ⟨[.global 0], [], [], [], [], false, true⟩
  let receiver : Impl :=
    { name := "receiver", params := #[⟨0, .byRef⟩], results := #[],
      vars := #[⟨"p", .ref .mutable (.int .i64), .immutable, 0, 0⟩],
      body := .mk 0 [.print [.expr (.read (.deref (.read (.var 0))))] 0] none,
      summary }
  let main : Impl :=
    { emptyEntry with
      body := .mk 0 [.expr (.call 1 [.byRef .mutable (.global 0)] 0) 0] none,
      summary }
  { files := #["specialized-summary.goose"], types := #[],
    globals := #[⟨"g", .int .i64, .mutable, .lit .i64 1, 0⟩],
    impls := #[main, receiver],
    contexts := #[⟨0, "main", [], [], []⟩,
      ⟨1, "receiver", [(0, [.global 0])], [], []⟩],
    entry := 0, origins := #[⟨0, 1, "test"⟩] }

def specializedParameterSummary : Module :=
  { specializedSummary with
    impls := specializedSummary.impls.modify 1 fun impl =>
      { impl with summary := .known ⟨[.param 0], [], [], [], [], false, true⟩ } }

#guard match Core.validate parameterSlice, GIR.validate (lower parameterSlice) with
  | .ok _, .ok _ => true
  | _, _ => false

#guard match Core.validate undeclaredSliceSlot with
  | .error rejection => rejection.rule == .type &&
      rejection.message == "main: variable p has a type no variable may have"
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

#guard [(readonlyReferenceLocal,
      "function main: slot 0 is initialized with a value of another type"),
    (readonlyReferenceRebind,
      "function main: a store of a value of another type than the referent"),
    (readonlyReferenceResult,
      "function receiver: a returned value of another type than the result"),
    (readonlySliceLocal,
      "function main: slot 0 is initialized with a value of another type")].all fun (module, message) =>
  match Core.validate module, GIR.validate (lower module) with
  | .ok _, .error rejection => rejection.code == .v010 && rejection.message == message
  | _, _ => false

#guard match Core.validate specializedSummary, GIR.validate (lower specializedSummary) with
  | .ok _, .error rejection => rejection.code == .v050 &&
      rejection.message == "function receiver: receiver reads parameter 0, which its summary omits"
  | _, _ => false

#guard match Core.validate specializedParameterSummary,
    GIR.validate (lower specializedParameterSummary) with
  | .ok _, .ok _ => true
  | _, _ => false

end Goose.Lower.Validation.Checks
