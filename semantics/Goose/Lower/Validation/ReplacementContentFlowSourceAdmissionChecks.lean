import Goose.Core.Validate
import Goose.Lower.CoreToGir
import Goose.GIR.ReplacementContentFlow

namespace Goose.Lower.Validation.ReplacementContentFlowSourceAdmissionChecks

open Goose.Core Goose.GIR
set_option maxRecDepth 12000
set_option maxHeartbeats 3000000

def widenedLocal : Core.Module :=
  { files := #["widened-local.goose"], types := #[], globals := #[],
    impls := #[
      { name := "main", params := #[], results := #[], vars := #[],
        body := .mk 0 [.expr (.lit .i64 0) 0] none, summary := .unknown },
      { name := "wrapper", params := #[⟨0,.byRef⟩,⟨1,.byValue⟩,⟨2,.byValue⟩], results := #[],
        vars := #[⟨"holder",.ref .mutable (.slice .mutable .bool),.immutable,0,0⟩,
                  ⟨"a",.slice .mutable .bool,.immutable,0,0⟩,
                  ⟨"b",.slice .mutable .bool,.immutable,0,0⟩,
                  ⟨"wide",.slice .mutable .bool,.immutable,0,0⟩],
        body := .mk 0 [.letS 3 (.read (.var 1)) 0,
          .expr (.call 2 [.byRef .mutable (.deref (.read (.var 0))), .byVal (.read (.var 3))] 0) 0] none,
        summary := .unknown },
      { name := "callee", params := #[⟨0,.byRef⟩,⟨1,.byValue⟩], results := #[],
        vars := #[⟨"holder",.ref .mutable (.slice .mutable .bool),.immutable,0,0⟩,
                  ⟨"value",.slice .mutable .bool,.immutable,0,0⟩],
        body := .mk 0 [] none, summary := .unknown }],
    contexts := #[⟨0,"main",[],[],[]⟩,
      ⟨1,"wrapper",[(0,[.param 0]),(1,[.param 1]),(2,[.param 2]),(3,[.param 1,.param 2])],[],[(0,[.param 1,.param 2])]⟩,
      ⟨2,"callee",[(0,[.param 0]),(1,[.param 1])],[],[(0,[.param 1])]⟩],
    entry := 0, origins := #[⟨0,1,"call"⟩] }

theorem widenedLocal_accepted : Core.validate widenedLocal = .ok () := by cbv

def widenedLocalEntry : Func := lowerContextAt widenedLocal
  (widenedLocal.contexts[0]'(by decide)) (widenedLocal.impls[0]'(by decide))

theorem widenedLocal_actual_entry : (lower widenedLocal).funcs[0]? = some widenedLocalEntry := by cbv

#guard ((replacementContentFlow (lower widenedLocal)).forFunction widenedLocalEntry
    (widenedLocalEntry.valueTypes (lower widenedLocal))).value 0 == some []

def widenedLocalReturned : Core.Module :=
  { widenedLocal with
    impls := widenedLocal.impls.set! 2
      { name := "callee", params := #[⟨0,.byRef⟩,⟨1,.byValue⟩], results := #[.slice .mutable .bool],
        vars := #[⟨"holder",.ref .mutable (.slice .mutable .bool),.immutable,0,0⟩,
                  ⟨"value",.slice .mutable .bool,.immutable,0,0⟩],
        body := .mk 0 [] (some (.read (.deref (.read (.var 0))))), summary := .unknown }
    contexts := widenedLocal.contexts.set! 2
      ⟨2,"callee",[(0,[.param 0]),(1,[.param 1])],[[.param 1]],[(0,[.param 1])]⟩ }

theorem widenedLocalReturned_accepted : Core.validate widenedLocalReturned = .ok () := by cbv

def widenedLocalReturnedEntry : Func := lowerContextAt widenedLocalReturned
  (widenedLocalReturned.contexts[0]'(by decide)) (widenedLocalReturned.impls[0]'(by decide))

theorem widenedLocalReturned_actual_entry : (lower widenedLocalReturned).funcs[0]? = some widenedLocalReturnedEntry := by cbv

#guard ((replacementContentFlow (lower widenedLocalReturned)).forFunction widenedLocalReturnedEntry
    (widenedLocalReturnedEntry.valueTypes (lower widenedLocalReturned))).value 0 == some []

def selfGlobal : Core.Module :=
  { files := #["self-global.goose"], types := #[],
    globals := #[⟨"g0",.grow .bool,.mutable,.arrLit (.grow .bool) [],0⟩,
                 ⟨"g1",.grow .bool,.mutable,.arrLit (.grow .bool) [],0⟩],
    impls := #[
      { name := "main", params := #[], results := #[], vars := #[],
        body := .mk 0 [.expr (.lit .i64 0) 0] none, summary := .unknown },
      { name := "wrapper", params := #[⟨0,.byRef⟩,⟨1,.byValue⟩], results := #[],
        vars := #[⟨"holder",.ref .mutable (.slice .mutable .bool),.immutable,0,0⟩,
                  ⟨"value",.slice .mutable .bool,.immutable,0,0⟩],
        body := .mk 0 [.expr (.call 2 [.byVal (.lit .i64 0),
          .byVal (.read (.deref (.read (.var 0))))] 0) 0] none,
        summary := .unknown },
      { name := "callee", params := #[⟨0,.byValue⟩,⟨1,.byValue⟩], results := #[],
        vars := #[⟨"dummy",.int .i64,.immutable,0,0⟩,
                  ⟨"value",.slice .mutable .bool,.immutable,0,0⟩],
        body := .mk 0 [] none, summary := .unknown }],
    contexts := #[⟨0,"main",[],[],[]⟩,
      ⟨1,"wrapper",[(0,[.param 0]),(1,[.global 1])],[],[(0,[.param 1])]⟩,
      ⟨2,"callee",[(1,[.param 1,.global 0])],[],[]⟩],
    entry := 0, origins := #[⟨0,1,"call"⟩] }

theorem selfGlobal_accepted : Core.validate selfGlobal = .ok () := by cbv

def entry : Func := lowerContextAt selfGlobal
  (selfGlobal.contexts[0]'(by decide)) (selfGlobal.impls[0]'(by decide))

theorem selfGlobal_actual_entry : (lower selfGlobal).funcs[0]? = some entry := by cbv

#guard ((replacementContentFlow (lower selfGlobal)).forFunction entry
    (entry.valueTypes (lower selfGlobal))).value 0 == some []

end Goose.Lower.Validation.ReplacementContentFlowSourceAdmissionChecks
