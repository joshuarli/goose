import Goose.GIR.AdmittedRegionsChecks

namespace Goose.Lower.Validation.AdmittedSourceInstructionsChecks

open Goose.Core Goose.GIR

set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

private def backing : Ty := .arr (.int .i64) 1
private def stopped : Expr :=
  .ifE (.bool false)
    (.mk 1 [.abort "stopped" 0] (some (.ref .readOnly (.global 0))))
    (.mk 2 [] (some (.ref .readOnly (.global 1))))
private def callee : Impl :=
  { name := "receiver", params := #[⟨0,.byRef⟩,⟨1,.byRef⟩], results := #[],
    vars := #[⟨"holder",.ref .readOnly (.slice .readOnly (.int .i64)),.immutable,0,0⟩,
      ⟨"dependency",.ref .readOnly backing,.immutable,0,0⟩],
    body := .mk 0 [] none, summary := .unknown }
private def main : Impl :=
  { name := "main", params := #[], results := #[],
    vars := #[⟨"holder",.slice .readOnly (.int .i64),.mutable,0,0⟩],
    body := .mk 0 [
      .letS 0 (.slice .readOnly (.of (.global 0)) .omitted .omitted 0) 0,
      .expr (.call 1 [.byRef .readOnly (.var 0),.byRef .readOnly (.deref stopped)] 0) 0] none,
    summary := .unknown }
private def source : Core.Module :=
  { files := #["stopped-content"], types := #[],
    globals := #[⟨"dead",backing,.immutable,.arrLit backing [.lit .i64 0],0⟩,
      ⟨"live",backing,.immutable,.arrLit backing [.lit .i64 1],0⟩],
    impls := #[main,callee],
    contexts := #[⟨0,"main",[(0,[.global 0,.global 1])],[],[]⟩,
      ⟨1,"receiver",[(0,[.param 0]),(1,[.global 0,.global 1])],[],[(0,[.param 1])]⟩],
    entry := 0, origins := #[⟨0,1,"expr"⟩] }

example : Core.validate source = .ok () := by cbv
#guard (GIR.validate (lower source)).isOk
#guard ((lower source).funcs[0]?).any fun func =>
  (func.roots.values.getD #[]).any fun row =>
    row.2.contains (.global 0) && row.2.contains (.global 1)
#guard !(GIR.validate { lower source with funcs := (lower source).funcs.map fun func =>
  { func with roots := { func.roots with values := none } } }).isOk

private def returning : Core.Module :=
  { source with
    impls := #[main, { callee with results := #[.slice .readOnly (.int .i64)], body := .mk 0 [] (some (.read (.deref (.read (.var 0))))) }],
    contexts := #[⟨0,"main",[(0,[.global 0,.global 1])],[],[]⟩,
      ⟨1,"receiver",[(0,[.param 0]),(1,[.global 0,.global 1])],[[.param 1]],[(0,[.param 1])]⟩] }
private def returningFunction : Func :=
  lowerContextAt returning ⟨0,"main",[(0,[.global 0,.global 1])],[],[]⟩ main
private def returningFlow : ReplacementFunctionFlow :=
  (replacementContentFlow (lower returning)).forFunction returningFunction
    (returningFunction.valueTypes (lower returning))
private def returningCalls : List (ValueId × List ValueId) :=
  (returningFunction.blocks.toList.flatMap (·.insts)).filterMap fun
    | .def value (.call _ arguments _) => some (value, arguments)
    | _ => none
example : Core.validate returning = .ok () := by cbv
#guard (GIR.validate (lower returning)).isOk
#guard returningCalls.any fun (value, arguments) =>
  ((arguments[1]?).bind returningFlow.value == some [.global 1]) &&
    returningFlow.value value == some [.global 0]

private def scalarExpression : Expr :=
  .ifE (.bool false) (.mk 1 [] (some (.lit .i64 0))) (.mk 2 [] (some (.lit .i64 1)))
private def scalarImpl : Impl :=
  { name := "main", params := #[], results := #[], vars := #[],
    body := .mk 0 [.expr scalarExpression 0] none, summary := .unknown }
private def scalar : Core.Module :=
  { source with impls := #[scalarImpl], contexts := #[⟨0,"main",[],[],[]⟩] }
example : Core.validate scalar = .ok () := by cbv
#guard (GIR.validate (lower scalar)).isOk
#guard ((lower scalar).funcs[0]?).any (·.roots.values.isNone)

private def unusedForwarder : Impl :=
  { name := "forward", params := #[⟨0,.byRef⟩], results := #[],
    vars := #[⟨"holder",.ref .mutable (.slice .readOnly (.int .i64)),.immutable,0,0⟩],
    body := .mk 0 [.expr (.call 2 [.byRef .mutable (.deref (.read (.var 0)))] 0) 0] none,
    summary := .unknown }
private def unusedTarget : Impl :=
  { unusedForwarder with name := "unused", body := .mk 0 [] none }
private def unusedForwarding : Core.Module :=
  { source with
    impls := #[scalarImpl,unusedForwarder,unusedTarget],
    contexts := #[⟨0,"main",[],[],[]⟩,⟨1,"forward",[(0,[.param 0])],[],[]⟩,
      ⟨2,"unused",[(0,[.param 0])],[],[]⟩] }
example : Core.validate unusedForwarding = .ok () := by cbv
#guard (GIR.validate (lower unusedForwarding)).isOk

private def specializedImpl : Impl :=
  { name := "specialized", params := #[⟨0,.byRef⟩,⟨1,.byRef⟩],
    results := #[.ref .readOnly backing],
    vars := #[⟨"a",.ref .readOnly backing,.immutable,0,0⟩,
      ⟨"b",.ref .readOnly backing,.immutable,0,0⟩],
    body := .mk 0 [] (some (.ifE (.bool false)
      (.mk 1 [.abort "stopped" 0] (some (.read (.var 0))))
      (.mk 2 [] (some (.read (.var 1)))))), summary := .unknown }
private def specialized : Core.Module :=
  { source with
    impls := #[{ main with vars := #[], body := .mk 0 [] none }, specializedImpl],
    contexts := #[⟨0,"main",[],[],[]⟩,
      ⟨1,"wide",[(0,[.global 0]),(1,[.global 1])],[[.global 0,.global 1]],[]⟩,
      ⟨1,"narrow",[(0,[.global 1]),(1,[.global 1])],[[.global 1]],[]⟩] }
example : Core.validate specialized = .ok () := by cbv
#guard (GIR.validate (lower specialized)).isOk
#guard ((lower specialized).funcs[1]?).any fun func =>
  (func.roots.values.getD #[]).any (·.2.contains (.global 0))
#guard ((lower specialized).funcs[2]?).any fun func =>
  (func.roots.values.getD #[]).all (! ·.2.contains (.global 0))

private def table : Json.Tables :=
  { types := #[], nGlobals := 1, nFuncs := 0, nOrigins := 0,
    nSlots := 1, nScopes := 0, nBlocks := 0, nValues := 2 }
private def decode (text : String) : Except String RootInfo := do
  Json.decRootInfo table 1 0 (← Lean.Json.parse text)

#guard (decode "[\"roots\",[],[],[],null,[]]").toOption.any fun roots =>
  roots.slots.isNone && roots.values == some #[] &&
    Json.wRootInfo roots == "[\"roots\",[],[],[],null,[]]"
#guard (decode "[\"roots\",[],[],[],[],[]]").toOption.any fun roots =>
  roots.slots == some #[] && roots.values == some #[] &&
    Json.wRootInfo roots == "[\"roots\",[],[],[],[],[]]"
#guard (decode "[\"roots\",[],[],[],null]").isOk == false
#guard (decode "[\"roots\",[],[],[],null,[[\"er\",1,[[\"r_global\",0]]]]]").toOption.any fun roots =>
  Json.wRootInfo roots == "[\"roots\",[],[],[],null,[[\"er\",1,[[\"r_global\",0]]]]]"
#guard (decode "[\"roots\",[],[],[],[],[[\"er\",2,[]]]]").isOk == false
#guard (decode "[\"roots\",[],[],[],[],[[\"er\",0,[]],[\"er\",0,[]]]]").isOk == false
#guard (decode "[\"roots\",[],[],[],[],[[\"er\",0,[[\"r_global\",1]]]]]").isOk == false
#guard (decode "[\"roots\",[],[],[],[],[[\"er\",0,[[\"r_param\",1]]]]]").isOk == false
#guard (decode "[\"roots\",[],[],[],[],[[\"er\",0,[[\"r_local\",1]]]]]").isOk == false

private def valueFunc : Func :=
  { name := "value", params := [], results := [], slots := #[], scopes := #[], blocks := #[],
    roots := { values := some #[(0,[.global 0])] }, summary := .unknown, org := none }
#guard valueFunc.admittedValues #[some (.data (.ref .readOnly backing))] ⟨#[],#[[.global 0]]⟩
#guard !valueFunc.admittedValues #[some (.data (.ref .readOnly backing))] ⟨#[],#[[.global 1]]⟩
#guard !valueFunc.admittedValues #[some (.data (.int .i64))] ⟨#[],#[[]]⟩
private def valuesOnly : GIR.Module :=
  { files := #[], globals := #[], entry := 0, origins := #[],
    funcs := #[{ valueFunc with results := [.ref .readOnly backing], roots := { results := #[[.global 0]], values := some #[] } }] }
#guard valuesOnly.declaredResultRoots == #[[]]

end Goose.Lower.Validation.AdmittedSourceInstructionsChecks
