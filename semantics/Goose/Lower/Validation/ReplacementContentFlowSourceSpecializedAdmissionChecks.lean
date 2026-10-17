import Goose.Lower.Validation.ReplacementContentFlowSourceAdmissionChecks

namespace Goose.Lower.Validation.ReplacementContentFlowSourceSpecializedAdmissionChecks

open Goose.Core Goose.GIR
open ReplacementContentFlowSourceAdmissionChecks
set_option maxRecDepth 12000
set_option maxHeartbeats 3000000

def specializedGlobalWidened : Core.Module :=
  { widenedLocalReturned with
    globals := selfGlobal.globals
    contexts := #[⟨0,"main",[],[],[]⟩,
      ⟨1,"wrapper",[(0,[.param 0]),(1,[.global 0]),(2,[.global 1]),(3,[.global 0,.global 1])],
        [],[(0,[.global 0,.global 1])]⟩,
      ⟨2,"callee",[(0,[.param 0]),(1,[.global 0,.global 1])],[[.param 1]],[(0,[.param 1])]⟩] }

theorem specializedGlobalWidened_accepted : Core.validate specializedGlobalWidened = .ok () := by cbv

def specializedGlobalWidenedEntry : Func := lowerContextAt specializedGlobalWidened
  (specializedGlobalWidened.contexts[0]'(by decide))
  (specializedGlobalWidened.impls[0]'(by decide))

theorem specializedGlobalWidened_actual_entry :
    (lower specializedGlobalWidened).funcs[0]? = some specializedGlobalWidenedEntry := by cbv

#guard ((replacementContentFlow (lower specializedGlobalWidened)).forFunction specializedGlobalWidenedEntry
    (specializedGlobalWidenedEntry.valueTypes (lower specializedGlobalWidened))).value 0 == some []

end Goose.Lower.Validation.ReplacementContentFlowSourceSpecializedAdmissionChecks
