import Goose.Lower.Validation.Checks

namespace Goose.Lower.Validation.SummaryPreservation.CallAnnotationChecks

open Goose.Core Goose.GIR

set_option maxRecDepth 12000
set_option maxHeartbeats 2000000

def specializedCallerContent : Core.Module :=
  let slice := Ty.slice .mutable (.int .i64)
  let caller : Impl :=
    { name := "caller", params := #[⟨0, .byRef⟩, ⟨1, .byRef⟩], results := #[],
      vars := #[⟨"holder", .ref .mutable slice, .immutable, 0, 0⟩,
        ⟨"root", .ref .readOnly (.int .i64), .immutable, 0, 0⟩],
      body := .mk 0 [.expr (.call 2 [.byVal (.bool true), .byVal (.read (.deref (.read (.var 0))))] 0) 0] none,
      summary := .unknown }
  let callee : Impl :=
    { name := "callee", params := #[⟨0, .byValue⟩, ⟨1, .byValue⟩], results := #[],
      vars := #[⟨"unused", .bool, .immutable, 0, 0⟩, ⟨"slice", slice, .immutable, 0, 0⟩],
      body := .mk 0 [] none, summary := .known ⟨[], [], [], [], [], false, false⟩ }
  { files := #["specialized-caller-content.goose"], types := #[],
    globals := #[⟨"first", .int .i64, .mutable, .lit .i64 0, 0⟩,
      ⟨"second", .int .i64, .mutable, .lit .i64 0, 0⟩],
    impls := #[Checks.emptyEntry, caller, callee],
    contexts := #[⟨0, "main", [], [], []⟩,
      ⟨1, "caller", [(0, [.param 0]), (1, [.param 1, .global 0])], [], [(0, [.param 1])]⟩,
      ⟨2, "callee", [(1, [.param 1, .global 1])], [], []⟩],
    entry := 0, origins := #[⟨0, 1, "expr"⟩] }

theorem specializedCallerContent_core_accepted : Core.validate specializedCallerContent = .ok () := by cbv

#guard (GIR.validate (lower specializedCallerContent)).toBool

#print axioms specializedCallerContent_core_accepted

end Goose.Lower.Validation.SummaryPreservation.CallAnnotationChecks
