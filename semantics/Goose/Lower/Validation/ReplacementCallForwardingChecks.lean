import Goose.Lower.CoreToGir
import Goose.Core.Validate
import Goose.GIR.Validate

namespace Goose.Lower.Validation.ReplacementCallForwardingChecks

open Goose.Core Goose.Lower Goose.GIR.ReplacementContentFlow.Model

private def source : Core.Module :=
  let owner := Ty.growshrink (.int .i64)
  let main : Impl :=
    { name := "main", params := #[], results := #[], vars := #[],
      body := .mk 0 [.assignWhole (.global 0) (.arrLit owner [.call 1 [] 0]) 0] none,
      summary := .unknown }
  let outer : Impl :=
    { name := "outer", params := #[], results := #[.int .i64], vars := #[],
      body := .mk 0 [] (some (.call 2 [.byRef .readOnly (.global 0)] 0)),
      summary := .known ⟨[], [], [], [], [], false, false⟩ }
  let inner : Impl :=
    { name := "inner", params := #[⟨0, .byRef⟩], results := #[.int .i64],
      vars := #[⟨"unused", .ref .readOnly owner, .immutable, 0, 0⟩],
      body := .mk 0 [] (some (.lit .i64 1)), summary := .known ⟨[], [], [], [], [], false, false⟩ }
  { files := #["call-touch"], types := #[], globals := #[⟨"p", owner, .mutable, .arrLit owner [], 0⟩],
    impls := #[main, outer, inner], contexts := #[⟨0, "main", [], [], []⟩,
      ⟨1, "outer", [], [[]], []⟩, ⟨2, "inner", [(0, [.global 0])], [[]], []⟩], entry := 0,
    origins := #[⟨0, 1, "expr"⟩], profile := .shrink }


private def sampled : Core.Module :=
  { source with impls := source.impls.modify 1 fun impl =>
    { impl with
      body := .mk 0 [] (some (.len (.of (.global 0)))),
      summary := .known ⟨[.global 0], [], [], [], [], false, false⟩ } }

private def contentsSample (dependent : Bool) : Core.Module :=
  let target := if dependent then 0 else 1
  let owner := Ty.growshrink (.int .i64)
  let slice := Ty.slice .readOnly (.int .i64)
  { source with
    globals := source.globals.push ⟨"other", owner, .mutable, .arrLit owner [], 0⟩,
    impls := source.impls.modify 0 (fun impl =>
      { impl with
        vars := #[⟨"slice", slice, .mutable, 0, 0⟩],
        body := .mk 0 [.letS 0 (.slice .readOnly (.of (.global target)) .omitted .omitted 0) 0,
          .assignWhole (.global 0) (.arrLit owner [.call 1 [.byRef .mutable (.var 0)] 0]) 0] none }) |>.modify 1 fun impl =>
      { impl with
        params := #[⟨0, .byRef⟩], vars := #[⟨"holder", .ref .mutable slice, .immutable, 0, 0⟩],
        body := .mk 0 [] (some (.len (.val (.read (.deref (.read (.var 0))))))),
        summary := .known ⟨[.param 0], [], [], [], [], false, false⟩ },
    contexts := source.contexts.modify 0 (fun context => { context with varRoots := [(0, [.global target])] }) |>.modify 1 fun context =>
      { context with varRoots := [(0, [.param 0])], contentRoots := [(0, [.global target])] } }



private def retainsContents (input : Core.Module) : Bool :=
  match (GIR.replacementContentFlow (lower input)).model with
  | none => false
  | some states => match states[1]? with
    | none => false
    | some state => match state.touched with
      | .known atoms => atoms.contains (.contents 0)
      | _ => false

#guard (Core.validate source).toBool
#guard (GIR.validate (lower source)).toBool
#guard match Core.validate sampled with | .error rejection => rejection.rule == .whole | _ => false
#guard match GIR.validate (lower sampled) with | .error rejection => rejection.code == .v060 | _ => false
#guard match Core.validate (contentsSample true) with | .error rejection => rejection.rule == .shrink | _ => false
#guard match GIR.validate (lower (contentsSample true)) with | .error rejection => rejection.code == .v060 | _ => false
#guard (Core.validate (contentsSample false)).toBool
#guard (GIR.validate (lower (contentsSample false))).toBool
#guard retainsContents (contentsSample true)
#guard retainsContents (contentsSample false)

end Goose.Lower.Validation.ReplacementCallForwardingChecks
