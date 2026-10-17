import Goose.Lower.Validation.ReplacementContentFlowSourceChecks
import Goose.GIR.Validate

namespace Goose.Lower.Validation.ReplacementContentFlowAdmissionChecks

open Goose.Core Goose.GIR
open ReplacementContentFlowSourceChecks

private def replacementProbe (module : Core.Module) : Core.Module :=
  let owner := Ty.growshrink (.int .i64)
  { module with
    profile := .shrink,
    globals := module.globals.push ⟨"probe", .int .i64, .immutable, .lit .i64 7, 0⟩,
    impls := module.impls.modify 0 fun impl =>
      { impl with
        vars := #[⟨"p", owner, .mutable, 0, 0⟩],
        body := .mk 0 [.letS 0 (.arrLit owner []) 0,
          .assignWhole (.var 0) (.arrLit owner [.read (.global module.globals.size)]) 0] none } }

#guard (Core.validate (replacementProbe recursiveReference)).toBool
#guard (GIR.validate (lower (replacementProbe recursiveReference))).toBool
#guard (Core.validate (replacementProbe contentCrossParameter)).toBool
#guard (GIR.validate (lower (replacementProbe contentCrossParameter))).toBool
#guard (Core.validate (replacementProbe aliasedContentWrite)).toBool
#guard (GIR.validate (lower (replacementProbe aliasedContentWrite))).toBool

end Goose.Lower.Validation.ReplacementContentFlowAdmissionChecks
