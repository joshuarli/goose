import Goose.Lower.Validation.Checks
import Goose.Lower.Validation.SummaryPreservationRootRefinement

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

set_option maxRecDepth 12000
set_option maxHeartbeats 2000000

def specializedContentResult : Core.Module :=
  let slice := Ty.slice .mutable (.int .i64)
  let receiver : Impl :=
    { name := "receiver", params := #[⟨0, .byRef⟩, ⟨1, .byRef⟩], results := #[slice],
      vars := #[⟨"storage", .ref .mutable slice, .immutable, 0, 0⟩,
        ⟨"root", .ref .readOnly (.int .i64), .immutable, 0, 0⟩],
      body := .mk 0 [] (some (.read (.deref (.read (.var 0))))),
      summary := .known ⟨[.param 0], [], [], [], [], false, false⟩ }
  { files := #["specialized-content-result.goose"], types := #[],
    globals := #[⟨"global", .int .i64, .mutable, .lit .i64 0, 0⟩],
    impls := #[Checks.emptyEntry, receiver],
    contexts := #[⟨0, "main", [], [], []⟩,
      ⟨1, "receiver", [(0, [.param 0]), (1, [.param 1, .global 0])],
        [[.param 1]], [(0, [.param 1])]⟩],
    entry := 0, origins := #[⟨0, 1, "expr"⟩] }

theorem specializedContentResult_core_accepted :
    Core.validate specializedContentResult = .ok () := by
  cbv

theorem specializedContentResult_gir_accepted :
    GIR.validate (lower specializedContentResult) = .ok () := by
  cbv

def specializedContentFunction : GIR.Func :=
  lowerContextAt specializedContentResult
    (specializedContentResult.contexts[1]'(by decide))
    (specializedContentResult.impls[1]'(by decide))

theorem specializedContentResult_expands_global :
    RootRef.global 0 ∈ specializedContentFunction.expandParameterRoot (.param 1) := by
  decide

theorem specializedContentResult_literal_root_not_represented :
    ¬ RootsRepresent specializedContentFunction [.param 1] [.param 1] := by
  intro represented
  have impossible := represented (.param 1) (by simp) (.global 0)
    specializedContentResult_expands_global
  simp at impossible


theorem specializedContentResult_literal_root_refines :
    RootsRefine specializedContentFunction [.param 1] [.param 1] :=
  RootsRefine.refl _ _

end Goose.Lower.Validation.SummaryPreservation
