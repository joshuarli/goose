import Goose.Lower.CoreToGir
import Goose.Core.Validate
import Goose.GIR.ReplacementContentFlow

namespace Goose.GIR.ReplacementContentFlowAccessChecks

open Goose.Core Goose.Lower
set_option maxRecDepth 12000
set_option maxHeartbeats 3000000

private def stableReference (copy : Bool) : Core.Module :=
  let owner := Ty.growshrink (.int .i64)
  let main : Impl :=
    { name := "main", params := #[], results := #[],
      vars := #[⟨"q", .ref .readOnly owner, .immutable, 1, 0⟩],
      body := .mk 0 [.assignWhole (.global 0)
        (.arrLit owner [.blockE (.mk 1 [.letS 0 (.call 1 [] 0) 0] (some (.lit .i64 0)))]) 0] none,
      summary := .unknown }
  let callee : Impl :=
    { name := "address", params := #[], results := #[.ref .readOnly owner], vars := if copy then #[⟨"r", .ref .readOnly owner, .immutable, 0, 0⟩] else #[],
      body := if copy then .mk 0 [.letS 0 (.ref .readOnly (.global 0)) 0] (some (.read (.var 0)))
        else .mk 0 [] (some (.ref .readOnly (.global 0))),
      summary := .known ⟨[], [], [], [], [], false, false⟩ }
  { files := #["owner-return"], types := #[],
    globals := #[⟨"p", owner, .mutable, .arrLit owner [], 0⟩],
    impls := #[main, callee], contexts := #[⟨0,"main",[(0,[.global 0])],[],[]⟩,
      ⟨1,"address",if copy then [(0,[.global 0])] else [],[[.global 0]],[]⟩], entry := 0,
    origins := #[⟨0,1,"expr"⟩], profile := .shrink }

private def stableReferenceQuery (copy : Bool) : Option (List RootRef) := do
  let m := lower (stableReference copy)
  let f ← m.funcs[0]?
  ((replacementContentFlow m).forFunction f (f.valueTypes m)).call 1 []

#guard (Core.validate (stableReference false)).toBool
#guard (Core.validate (stableReference true)).toBool

#guard stableReferenceQuery false == some []
#guard stableReferenceQuery true == some []

private def interiorReturn (dependent consume : Bool) : Core.Module :=
  let owner := Ty.growshrink (.int .i64)
  let slice := Ty.slice .readOnly (.int .i64)
  let target := if dependent then 0 else 1
  let main : Impl :=
    { name := "main", params := #[], results := #[],
      vars := #[⟨"s", slice, .mutable, 0, 0⟩, ⟨"q", slice, .immutable, 1, 0⟩],
      body := .mk 0 [.letS 0 (.slice .readOnly (.of (.global target)) .omitted .omitted 0) 0,
        .assignWhole (.global 0) (.arrLit owner [.blockE (.mk 1
          [.letS 1 (.call 1 [.byRef .readOnly (.var 0)] 0) 0]
          (some (if consume then .len (.val (.read (.var 1))) else .lit .i64 0)))]) 0] none,
      summary := .unknown }
  let callee : Impl :=
    { name := "load", params := #[⟨0, .byRef⟩], results := #[slice],
      vars := #[⟨"holder", .ref .readOnly slice, .immutable, 0, 0⟩],
      body := .mk 0 [] (some (.read (.deref (.read (.var 0))))),
      summary := .known ⟨[.param 0], [], [], [], [], false, false⟩ }
  { files := #["interior-copy"], types := #[],
    globals := #[⟨"p", owner, .mutable, .arrLit owner [], 0⟩,
      ⟨"other", owner, .mutable, .arrLit owner [], 0⟩],
    impls := #[main, callee],
    contexts := #[⟨0,"main",[(0,[.global target]),(1,[.global target])],[],[]⟩,
      ⟨1,"load",[(0,[.param 0])],[[.global target]],[(0,[.global target])]⟩],
    entry := 0, origins := #[⟨0,1,"expr"⟩], profile := .shrink }

#guard match Core.validate (interiorReturn true false) with
  | .error rejection => rejection.rule == .shrink
  | _ => false
#guard (Core.validate (interiorReturn false false)).toBool
#guard (Core.validate (interiorReturn false true)).toBool

end Goose.GIR.ReplacementContentFlowAccessChecks
