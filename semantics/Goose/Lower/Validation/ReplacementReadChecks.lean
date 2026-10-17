import Goose.Lower.CoreToGir
import Goose.Core.Validate
import Goose.GIR.Validate

namespace Goose.Lower.Validation.ReplacementReadChecks

open Goose Goose.Core Goose.Lower

private def ownerCopy (dependent : Bool) : Core.Module :=
  let owner := Ty.growshrink (.int .i64)
  let main : Impl :=
    { name := "main", params := #[], results := #[],
      vars := #[⟨"p", owner, .mutable, 0, 0⟩,
        ⟨"q", .ref .mutable owner, .immutable, 0, 0⟩,
        ⟨"r", .ref .mutable owner, .immutable, 1, 0⟩],
      body := .mk 0 [.letS 0 (.arrLit owner []) 0,
        .letS 1 (.ref .mutable (if dependent then .var 0 else .global 0)) 0,
        .assignWhole (.var 0) (.arrLit owner [.blockE (.mk 1 [.letS 2 (.read (.var 1)) 0] (some (.lit .i64 0)))]) 0] none,
      summary := .unknown }
  let roots := if dependent then [RootRef.local 0] else [.global 0]
  { files := #["owner-copy"], types := #[],
    globals := #[⟨"other", owner, .mutable, .arrLit owner [], 0⟩], impls := #[main],
    contexts := #[⟨0, "main", [(1, roots), (2, roots)], [], []⟩], entry := 0,
    origins := #[⟨0, 1, "expr"⟩], profile := .shrink }

#guard match Core.validate (ownerCopy true) with
  | .error rejection => rejection.rule == .whole
  | _ => false
#guard match GIR.validate (lower (ownerCopy true)) with
  | .error rejection => rejection.code == .v060
  | _ => false
#guard (Core.validate (ownerCopy false)).toBool
#guard (GIR.validate (lower (ownerCopy false))).toBool

end Goose.Lower.Validation.ReplacementReadChecks
