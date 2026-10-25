import Goose.Construct.Eval
import Goose.Construct.Validate

set_option Elab.async false

namespace Goose.Proofs.ConstructionNoGrowAliasChecks
open Goose.Construct
private def array : Ty := .growshrink (.int .u8)
private def helper : Impl :=
  ⟨"helper", #[⟨0, .byRef⟩, ⟨1, .byRef⟩], #[],
    #[⟨"left", .ref .mutable array, .immutable, 0, 0⟩,
      ⟨"right", .ref .mutable array, .immutable, 0, 0⟩],
    .mk 0 [.assignWhole (.deref (.read (.var 0)))
      (.copy array (.deref (.read (.var 1))) 0) 0] none, .unknown⟩
private def entry : Impl :=
  ⟨"entry", #[], #[], #[⟨"owner", array, .mutable, 0, 0⟩],
    .mk 0 [.letS 0 (.arrLit array [.lit .u8 65] 0) 0,
      .expr (.call 1 [.byRef .mutable (.var 0), .byRef .mutable (.var 0)] 0) 0,
      .print [.view (.of (.var 0))] 0] none, .unknown⟩
def candidate : Module :=
  ⟨#["alias-whole.goose"], #[], #[], #[entry, helper],
    #[⟨0, "entry", [], [], []⟩,
      ⟨1, "helper", [(0, [.param 0]), (1, [.param 1])], [], []⟩],
    0, #[⟨0, 1, "expr"⟩], #[], #[]⟩
def accepted : Bool :=
  match validate candidate with | .ok () => true | .error _ => false

def output : Option (List UInt8 × List Goose.Core.ConstructionEvent) :=
  match eval 100 .release candidate with
  | .done .returned bytes events => some (bytes.data.toList, events)
  | _ => none

theorem aliased_whole_rejected : accepted = false := by decide +kernel

theorem aliased_whole_reads_cleared_receiver : output = some ([10],
    [.begin 0, .write 0 0, .publish 0, .begin 1, .copy (.storage 0 []) 1, .publish 1]) := by
  cbv

private def context (implementation count : Nat) : Context :=
  ⟨implementation, "helper", (List.range count).map fun index => (index, [.param index]), [], []⟩

private def function (array : Ty) (count : Nat) (body : Block) : Impl :=
  ⟨"helper", ((List.range count).map fun index => (⟨index, .byRef⟩ : Param)).toArray, #[],
    ((List.range count).map fun index => (⟨toString index, .ref .mutable array, .immutable, 0, 0⟩ : LocalVar)).toArray,
    body, .unknown⟩

private def pointee (index : Nat) : Place := .deref (.read (.var index))

private def initial (array : Ty) : Expr :=
  .arrLit array (if array == .growshrink (.int .u8) then [.lit .u8 65] else []) 0

private def program (array : Ty) (helper : Impl) (arguments : List Nat) : Module :=
  let entry : Impl := ⟨"entry", #[], #[],
    #[⟨"first", array, .mutable, 0, 0⟩, ⟨"second", array, .mutable, 0, 0⟩],
    .mk 0 [.letS 0 (initial array) 0, .letS 1 (initial array) 0,
      .expr (.call 1 (arguments.map fun index => .byRef .mutable (.var index)) 0) 0] none, .unknown⟩
  { candidate with impls := #[entry, helper], contexts := #[⟨0, "entry", [], [], []⟩, context 1 helper.params.size] }

private def accepts (module : Module) : Bool :=
  match validate module with | .ok () => true | .error _ => false

private def rejects (module : Module) (rule : Goose.Core.Rule) : Bool :=
  match validate module with | .ok () => false | .error reason => reason.rule == rule

private def wholeHelper : Impl :=
  function array 2 (.mk 0 [.assignWhole (pointee 0) (.copy array (pointee 1) 0) 0] none)

private def harmlessHelper : Impl :=
  function array 2 (.mk 0 [.expr (.read (.var 0)) 0, .expr (.read (.var 1)) 0] none)

#guard rejects (program array wholeHelper [0, 0]) .whole

theorem aliased_harmless_accepted : accepts (program array harmlessHelper [0, 0]) = true := by
  decide +kernel

theorem distinct_whole_accepted : accepts (program array wholeHelper [0, 1]) = true := by
  decide +kernel

private def forwarded (recursive : Bool) : Module :=
  let wrapper := function array 2 (.mk 0
    [.ifS (.bool false) (.mk 1
      [.expr (.call 2 [.byRef .mutable (pointee 1), .byRef .mutable (pointee 0)] 0) 0] none)
      (some (.mk 2 [.expr (.call 1 [.byRef .mutable (pointee 1), .byRef .mutable (pointee 0)] 0) 0] none)) 0] none)
  let base := program array wholeHelper [0, 0]
  let entry := { (base.impls[0]'(by simp [base, program])) with
    body := .mk 0
      [.letS 0 (initial array) 0, .letS 1 (initial array) 0,
      .expr (.call 2 [.byRef .mutable (.var 0), .byRef .mutable (.var 0)] 0) 0] none }
  let wrapper := if recursive then wrapper else function array 2 (.mk 0
    [.expr (.call 1 [.byRef .mutable (pointee 1), .byRef .mutable (pointee 0)] 0) 0] none)
  { base with impls := #[entry, wholeHelper, wrapper], contexts := #[⟨0, "entry", [], [], []⟩, context 1 2, context 2 2] }

#guard rejects (forwarded false) .whole
#guard rejects (forwarded true) .whole

private def independentAliases (separateContexts : Bool) : Module :=
  let helper := function array 3 (.mk 0 [.assignWhole (pointee 0) (.copy array (pointee 2) 0) 0] none)
  let base := program array helper [0, 0, 1]
  let secondContext := if separateContexts then 2 else 1
  let entry := { (base.impls[0]'(by simp [base, program])) with
    body := .mk 0
      [.letS 0 (initial array) 0, .letS 1 (initial array) 0,
      .expr (.call 1 [.byRef .mutable (.var 0), .byRef .mutable (.var 0), .byRef .mutable (.var 1)] 0) 0,
      .expr (.call secondContext [.byRef .mutable (.var 0), .byRef .mutable (.var 1), .byRef .mutable (.var 1)] 0) 0] none }
  { base with impls := #[entry, helper], contexts :=
    if separateContexts then #[⟨0, "entry", [], [], []⟩, context 1 3, context 1 3] else base.contexts }

#guard accepts (independentAliases false)
#guard accepts (independentAliases true)

private def arrays : Ty := .grow (.varr (.int .u8))
private def growingHelper : Impl := function arrays 2 (.mk 0
  [.expr (.push (pointee 0) (.blockE (.mk 1 [.expr (.push (pointee 1) (.bytes (.varr (.int .u8)) [65] 0) (some 0)) 0] (some (.bytes (.varr (.int .u8)) [66] 0))) 0) (some 0)) 0] none)

#guard rejects (program arrays growingHelper [0, 0]) .call
#guard accepts (program arrays growingHelper [0, 1])

private def discardedReferenceHelper : Impl := function array 2 (.mk 0
  [.assignWhole (pointee 0) (.blockE (.mk 1 [.expr (.read (.var 1)) 0]
    (some (.arrLit array [.lit .u8 66] 0))) 0) 0] none)

#guard rejects (program array discardedReferenceHelper [0, 0]) .whole
#guard accepts (program array discardedReferenceHelper [0, 1])

private def globalProgram (array : Ty) (helper : Impl) (same : Bool) : Module :=
  let base := program array helper [0]
  let argument : Place := if same then .global 0 else .var 0
  let entry := { (base.impls[0]'(by simp [base, program])) with
    body := .mk 0 [.letS 0 (initial array) 0, .letS 1 (initial array) 0,
    .expr (.call 1 [.byRef .mutable argument] 0) 0] none }
  { base with impls := #[entry, helper], globals := #[⟨"global", array, .mutable, initial array, 0⟩] }

private def withGlobal (helper : Impl) (same : Bool) : Module := globalProgram array helper same

private def globalHelper : Impl := function array 1 (.mk 0
  [.assignWhole (pointee 0) (.copy array (.global 0) 0) 0] none)

#guard rejects (withGlobal globalHelper true) .whole
#guard accepts (withGlobal globalHelper false)

private def emptySummary : SummaryAnn := .known ⟨[], [], [], [], [], [], [], [], false, false⟩
private def namedGlobal : Impl :=
  ⟨"name-global", #[], #[], #[], .mk 0 [.expr (.ref .mutable (.global 0)) 0] none, emptySummary⟩
private def namingHelper : Impl := function array 1 (.mk 0
  [.assignWhole (pointee 0) (.blockE (.mk 1 [.expr (.call 2 [] 0) 0]
    (some (.arrLit array [.lit .u8 66] 0))) 0) 0] none)
private def namedAccess (same : Bool) : Module :=
  let base := withGlobal namingHelper same
  { base with impls := base.impls.push namedGlobal, contexts := base.contexts.push (context 2 0) }

#guard rejects (namedAccess true) .whole
#guard accepts (namedAccess false)

private def unknownGlobal : Impl :=
  ⟨"unknown-global", #[], #[⟨array, .value, none⟩], #[],
    .mk 0 [] (some (.arrLit array [.lit .u8 66] 0)), .unknown⟩
private def unknownHelper : Impl := function array 1 (.mk 0
  [.assignWhole (pointee 0) (.call 2 [] 0) 0] none)
private def unknownAccess (same : Bool) : Module :=
  let base := withGlobal unknownHelper same
  { base with
    impls := base.impls.push unknownGlobal
    contexts := base.contexts.push ⟨2, "unknown-global", [], [[]], []⟩ }

#guard rejects (unknownAccess true) .whole
#guard accepts (unknownAccess false)

private def forwardedGrowth (recursive : Bool) : Module :=
  let base := program arrays growingHelper [0, 0]
  let recurse := if recursive then [.ifS (.bool false)
    (.mk 1 [.expr (.call 2 [.byRef .mutable (pointee 0), .byRef .mutable (pointee 1)] 0) 0] none) none 0] else []
  let wrapper := function arrays 2 (.mk 0 (recurse ++
    [.expr (.call 1 [.byRef .mutable (pointee 1), .byRef .mutable (pointee 0)] 0) 0]) none)
  let entry := { (base.impls[0]'(by simp [base, program])) with
    body := .mk 0 [.letS 0 (initial arrays) 0, .letS 1 (initial arrays) 0,
      .expr (.call 2 [.byRef .mutable (.var 0), .byRef .mutable (.var 0)] 0) 0] none }
  { base with
    impls := #[entry, growingHelper, wrapper]
    contexts := #[⟨0, "entry", [], [], []⟩, context 1 2, context 2 2] }

#guard rejects (forwardedGrowth false) .call
#guard rejects (forwardedGrowth true) .call

private def globalGrowingHelper : Impl := function arrays 1 (.mk 0
  [.expr (.push (pointee 0) (.blockE (.mk 1
    [.expr (.push (.global 0) (.bytes (.varr (.int .u8)) [65] 0) (some 0)) 0]
    (some (.bytes (.varr (.int .u8)) [66] 0))) 0) (some 0)) 0] none)

#guard rejects (globalProgram arrays globalGrowingHelper true) .call
#guard accepts (globalProgram arrays globalGrowingHelper false)

private def unknownBytes : Impl :=
  ⟨"unknown-bytes", #[], #[⟨.varr (.int .u8), .value, none⟩], #[],
    .mk 0 [] (some (.bytes (.varr (.int .u8)) [66] 0)), .unknown⟩
private def unknownGrowingHelper : Impl := function arrays 1 (.mk 0
  [.expr (.push (pointee 0) (.call 2 [] 0) (some 0)) 0] none)
private def unknownGrowth (same : Bool) : Module :=
  let base := globalProgram arrays unknownGrowingHelper same
  { base with
    impls := base.impls.push unknownBytes
    contexts := base.contexts.push ⟨2, "unknown-bytes", [], [[]], []⟩ }

#guard rejects (unknownGrowth true) .call
#guard accepts (unknownGrowth false)

private def initializedWhole (same : Bool) : Module :=
  let helper : Impl := ⟨"helper", #[⟨0, .byRef⟩, ⟨1, .byRef⟩], #[⟨array, .value, none⟩],
    wholeHelper.vars, .mk 0 [.assignWhole (pointee 0) (.copy array (pointee 1) 0) 0]
      (some (.arrLit array [.lit .u8 66] 0)),
    .known ⟨[.param 0, .param 1], [.param 0], [.param 0], [.param 0], [], [0], [], [], false, false⟩⟩
  let entry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, .unknown⟩
  let globals := #[⟨"first", array, .mutable, initial array, 0⟩,
    ⟨"second", array, .mutable, initial array, 0⟩]
  { candidate with
    impls := #[entry, helper]
    contexts := #[⟨0, "entry", [], [], []⟩, ⟨1, "helper", [(0, [.param 0]), (1, [.param 1])], [[]], []⟩]
    globals := globals.push ⟨"result", array, .mutable,
      .call 1 [.byRef .mutable (.global 0), .byRef .mutable (.global (if same then 0 else 1))] 0, 0⟩ }

#guard rejects (initializedWhole true) .whole
#guard accepts (initializedWhole false)

private def fixedPush : Module :=
  let owner : Ty := .grow (.int .u8)
  let entry : Impl := ⟨"entry", #[], #[], #[⟨"owner", owner, .mutable, 0, 0⟩],
    .mk 0 [.letS 0 (.arrLit owner [] 0) 0,
      .expr (.push (.var 0) (.blockE (.mk 1
        [.expr (.push (.var 0) (.lit .u8 65) (some 0)) 0]
        (some (.lit .u8 66))) 0) (some 0)) 0] none, .unknown⟩
  { candidate with impls := #[entry], contexts := #[⟨0, "entry", [], [], []⟩] }

#guard accepts fixedPush


private def staticForwarding : Module :=
  let slice : Ty := .slice .readOnly (.int .u8)
  let helper : Impl := ⟨"read-slice", #[⟨0, .byValue⟩], #[],
    #[⟨"source", slice, .immutable, 0, 0⟩], .mk 0 [.expr (.read (.var 0)) 0] none, .unknown⟩
  let wrapper : Impl := ⟨"forward-slice", #[⟨0, .byValue⟩], #[], helper.vars,
    .mk 0 [.expr (.call 1 [.byVal (.read (.var 0))] 0) 0] none, .unknown⟩
  let entry : Impl := ⟨"entry", #[], #[], #[],
    .mk 0 [.expr (.call 2 [.byVal (.bytes slice [65] 0)] 0) 0] none, .unknown⟩
  { candidate with
    impls := #[entry, helper, wrapper]
    contexts := #[⟨0, "entry", [], [], []⟩, context 1 1, context 2 1] }

#guard accepts staticForwarding

end Goose.Proofs.ConstructionNoGrowAliasChecks
