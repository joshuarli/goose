import Goose.Core.Validate
import Goose.Core.Eval
import Goose.GIR.Validate
import Goose.GIR.Eval
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
    entry := 0, origins := #[⟨0, 1, "expr"⟩] }

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
    entry := 0, origins := #[⟨0, 1, "expr"⟩], profile := .shrink }

def readonlyReferenceLocal : Module :=
  let main : Impl :=
    { emptyEntry with
      vars := #[⟨"r", .ref .readOnly (.int .i64), .immutable, 0, 0⟩],
      body := .mk 0 [.letS 0 (.ref .mutable (.global 0)) 0] none }
  { files := #["readonly-reference-local.goose"], types := #[],
    globals := #[⟨"g", .int .i64, .mutable, .lit .i64 1, 0⟩],
    impls := #[main], contexts := #[⟨0, "main", [(0, [.global 0])], [], []⟩],
    entry := 0, origins := #[⟨0, 1, "expr"⟩] }

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
    entry := 0, origins := #[⟨0, 1, "expr"⟩] }

def readonlyFieldSlice : Module :=
  let arrayTy := Ty.arr (.int .i64) 2
  let fields := TyList.ofList [arrayTy]
  let structTy := Ty.structT 0 fields
  let main : Impl :=
    { emptyEntry with
      vars := #[⟨"s", .slice .mutable (.int .i64), .immutable, 0, 0⟩],
      body := .mk 0 [.letS 0 (.slice .mutable (.of (.field (.global 0) 0)) .omitted .omitted 0) 0,
        .print [.expr (.len (.val (.read (.var 0))))] 0] none }
  { files := #["readonly-field-slice.goose"], types := #[],
    globals := #[⟨"g", structTy, .immutable,
      .structLit structTy [.arrLit arrayTy [.lit .i64 7, .lit .i64 9]], 0⟩],
    impls := #[main], contexts := #[⟨0, "main", [(0, [.global 0])], [], []⟩],
    entry := 0, origins := #[⟨0, 1, "expr"⟩], profile := .shrink,
    structs := #[⟨16, #[⟨arrayTy, .immutable, .mutable, 0⟩]⟩] }


def resizableStructField : Module :=
  let fieldTy := Ty.growshrink (.int .i64)
  let structTy := Ty.structT 0 (.cons fieldTy .nil)
  let main : Impl :=
    { emptyEntry with
      vars := #[⟨"r", .ref .mutable fieldTy, .immutable, 0, 0⟩],
      body := .mk 0 [.letS 0 (.ref .mutable (.field (.global 0) 0)) 0] none }
  { files := #["resizable-struct-field.goose"], types := #[],
    globals := #[⟨"g", structTy, .immutable, .structLit structTy [.arrLit fieldTy []], 0⟩],
    impls := #[main], contexts := #[⟨0, "main", [(0, [.global 0])], [], []⟩],
    entry := 0, origins := #[⟨0, 1, "expr"⟩], profile := .shrink,
    structs := #[⟨8, #[⟨fieldTy, .immutable, .mutable, 0⟩]⟩] }

#guard match Core.validate resizableStructField with
  | .error error => error.message == "struct fields must be flat fixed values"
  | .ok _ => false

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
    entry := 0, origins := #[⟨0, 1, "expr"⟩] }

def specializedParameterSummary : Module :=
  { specializedSummary with
    impls := specializedSummary.impls.modify 1 fun impl =>
      { impl with summary := .known ⟨[.param 0], [], [], [], [], false, true⟩ } }

def specializedStorageSummary : Module :=
  let owner := Ty.growshrink (.int .i64)
  let target := Place.deref (.read (.var 0))
  let receiver : Impl :=
    { name := "receiver", params := #[⟨0, .byRef⟩], results := #[],
      vars := #[⟨"p", .ref .mutable owner, .immutable, 0, 0⟩],
      body := .mk 0 [.expr (.push target (.lit .i64 1) (some 0)) 0, .clear target 0] none,
      summary := .known ⟨[.global 0], [.global 0], [.global 0], [.global 0], [], false, false⟩ }
  let main : Impl :=
    { emptyEntry with body := .mk 0 [.expr (.call 1 [.byRef .mutable (.global 0)] 0) 0] none }
  { files := #["specialized-storage-summary.goose"], types := #[],
    globals := #[⟨"g", owner, .mutable, .arrLit owner [], 0⟩],
    impls := #[main, receiver],
    contexts := #[⟨0, "main", [], [], []⟩,
      ⟨1, "receiver", [(0, [.global 0])], [], []⟩],
    entry := 0, origins := #[⟨0, 1, "expr"⟩], profile := .shrink }

def specializedBindingSummary : Module :=
  { specializedSummary with
    impls := specializedSummary.impls.modify 0 (fun impl => { impl with summary := .unknown })
      |>.modify 1 fun impl =>
        { impl with
          vars := impl.vars.modify 0 fun var => { var with kind := .mutable },
          body := .mk 0 [.rebind 0 (.ref .mutable (.global 0)) 0] none,
          summary := .known ⟨[], [], [], [], [.param 0], false, false⟩ } }

def incorrectBindingSummary : Module :=
  { specializedBindingSummary with
    impls := specializedBindingSummary.impls.modify 1 fun impl =>
      { impl with summary := .known ⟨[], [], [], [], [.global 0], false, false⟩ } }

def omittedSpecializedRead : Module :=
  { specializedSummary with
    impls := specializedSummary.impls.modify 1 fun impl =>
      { impl with summary := .known ⟨[], [], [], [], [], false, true⟩ } }

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

#guard [readonlyReferenceLocal, readonlyReferenceRebind,
    readonlyReferenceResult, readonlySliceLocal].all fun module =>
  match Core.validate module, GIR.validate (lower module) with
  | .ok _, .ok _ => true
  | _, _ => false

#guard match Core.validate specializedSummary, GIR.validate (lower specializedSummary) with
  | .ok _, .ok _ => true
  | _, _ => false

#guard match Core.validate specializedParameterSummary,
    GIR.validate (lower specializedParameterSummary) with
  | .ok _, .ok _ => true
  | _, _ => false

#guard [specializedStorageSummary, specializedBindingSummary].all fun module =>
  match Core.validate module, GIR.validate (lower module) with
  | .ok _, .ok _ => true
  | _, _ => false

#guard [omittedSpecializedRead, incorrectBindingSummary].all fun module =>
  match Core.validate module, GIR.validate (lower module) with
  | .error source, .error lowered => source.rule == .summary && lowered.code == .v050
  | _, _ => false

#guard match (specializedStorageSummary.impls[1]?).map (fun impl : Core.Impl => impl.summary) with
  | some (Core.SummaryAnn.known complete) =>
    [{ complete with reads := [] }, { complete with writes := [] },
      { complete with grows := [] }, { complete with shrinks := [] }].all fun summary =>
      let module := { specializedStorageSummary with
        impls := specializedStorageSummary.impls.modify 1 fun impl =>
          { impl with summary := .known summary } }
      match Core.validate module, GIR.validate (lower module) with
      | .error source, .error lowered => source.rule == .summary && lowered.code == .v050
      | _, _ => false
  | _ => false

#guard match Core.validate readonlyFieldSlice, GIR.validate (lower readonlyFieldSlice) with
  | .ok _, .ok _ => true
  | _, _ => false

#guard [NumProfile.release, .debug].all fun profile =>
  match Core.eval 100 profile readonlyFieldSlice, GIR.run 300 profile (lower readonlyFieldSlice) with
  | .done .returned "2\n", .done .returned "2\n" => true
  | _, _ => false

end Goose.Lower.Validation.Checks
