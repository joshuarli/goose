import Goose.Core.Validate
import Goose.Lower.CoreToGir
import Goose.GIR.ReplacementContentFlow

namespace Goose.Lower.Validation.ReplacementContentFlowSourceChecks

open Goose.Core Goose.GIR

set_option maxRecDepth 12000
set_option maxHeartbeats 3000000

def recursiveReference : Core.Module :=
  { files := #["recursive-reference.goose"], types := #[], globals := #[],
    impls := #[
      { name := "main", params := #[], results := #[], vars := #[],
        body := .mk 0 [.expr (.lit .i64 0) 0] none, summary := .unknown },
      { name := "recursive", params := #[], results := #[.ref .readOnly (.int .i64)], vars := #[],
        body := .mk 0 [] (some (.call 1 [] 0)), summary := .unknown }],
    contexts := #[⟨0,"main",[],[],[]⟩,⟨1,"recursive",[],[[]],[]⟩], entry := 0,
    origins := #[⟨0,1,"call"⟩] }

theorem recursiveReference_accepted : Core.validate recursiveReference = .ok () := by cbv

def recursiveReferenceEntry : Func :=
  lowerContextAt recursiveReference
    (recursiveReference.contexts[0]'(by decide))
    (recursiveReference.impls[0]'(by decide))

theorem recursiveReference_actual_entry : (lower recursiveReference).funcs[0]? = some recursiveReferenceEntry := by
  cbv

#guard ((replacementContentFlow (lower recursiveReference)).forFunction recursiveReferenceEntry
      (recursiveReferenceEntry.valueTypes (lower recursiveReference))).value 0 == some []

end Goose.Lower.Validation.ReplacementContentFlowSourceChecks

namespace Goose.Lower.Validation.ReplacementContentFlowSourceChecks
open Goose.Core Goose.GIR
set_option maxRecDepth 12000
set_option maxHeartbeats 3000000

def contentCrossParameter : Core.Module :=
  { files := #["cross-parameter.goose"], types := #[],
    globals := #[],
    impls := #[
      { name := "main", params := #[], results := #[], vars := #[],
        body := .mk 0 [.expr (.lit .i64 0) 0] none, summary := .unknown },
      { name := "wrapper", params := #[⟨0,.byRef⟩,⟨1,.byRef⟩], results := #[],
        vars := #[⟨"a",.ref .mutable (.slice .mutable .bool),.immutable,0,0⟩,
                  ⟨"b",.ref .mutable (.slice .mutable .bool),.immutable,0,0⟩],
        body := .mk 0 [.expr (.call 2 [.byRef .mutable (.deref (.read (.var 0))),
                                      .byRef .mutable (.deref (.read (.var 1)))] 0) 0] none,
        summary := .unknown },
      { name := "callee", params := #[⟨0,.byRef⟩,⟨1,.byRef⟩], results := #[],
        vars := #[⟨"a",.ref .mutable (.slice .mutable .bool),.immutable,0,0⟩,
                  ⟨"b",.ref .mutable (.slice .mutable .bool),.immutable,0,0⟩],
        body := .mk 0 [] none, summary := .unknown }],
    contexts := #[⟨0,"main",[],[],[]⟩,
      ⟨1,"wrapper",[(0,[.param 0]),(1,[.param 1])],[],[(0,[.param 1]),(1,[])]⟩,
      ⟨2,"callee",[(0,[.param 0]),(1,[.param 1])],[],[(0,[.param 1]),(1,[])]⟩],
    entry := 0, origins := #[⟨0,1,"call"⟩] }

theorem contentCrossParameter_accepted : Core.validate contentCrossParameter = .ok () := by cbv

def contentCrossParameterEntry : Func :=
  lowerContextAt contentCrossParameter
    (contentCrossParameter.contexts[0]'(by decide))
    (contentCrossParameter.impls[0]'(by decide))

theorem contentCrossParameter_actual_entry :
    (lower contentCrossParameter).funcs[0]? = some contentCrossParameterEntry := by cbv

#guard ((replacementContentFlow (lower contentCrossParameter)).forFunction contentCrossParameterEntry
      (contentCrossParameterEntry.valueTypes (lower contentCrossParameter))).value 0 == some []
end Goose.Lower.Validation.ReplacementContentFlowSourceChecks

namespace Goose.Lower.Validation.ReplacementContentFlowSourceChecks
open Goose.Core Goose.GIR
set_option maxRecDepth 12000
set_option maxHeartbeats 3000000

def aliasedContentWrite : Core.Module :=
  { files := #["aliased-content.goose"], types := #[], globals := #[],
    impls := #[
      { name := "main", params := #[], results := #[], vars := #[],
        body := .mk 0 [.expr (.lit .i64 0) 0] none, summary := .unknown },
      { name := "writer", params := #[⟨0,.byRef⟩,⟨1,.byRef⟩,⟨2,.byValue⟩], results := #[],
        vars := #[⟨"a",.ref .mutable (.slice .mutable .bool),.immutable,0,0⟩,
                  ⟨"b",.ref .mutable (.slice .mutable .bool),.immutable,0,0⟩,
                  ⟨"value",.slice .mutable .bool,.immutable,0,0⟩],
        body := .mk 0 [.assign (.deref (.read (.var 0))) (.read (.var 2)) 0] none,
        summary := .unknown }],
    contexts := #[⟨0,"main",[],[],[]⟩,
      ⟨1,"writer",[(0,[.param 0]),(1,[.param 1]),(2,[.param 2])],[],[(0,[.param 2]),(1,[])]⟩],
    entry := 0, origins := #[⟨0,1,"assign"⟩] }

theorem aliasedContentWrite_accepted : Core.validate aliasedContentWrite = .ok () := by cbv

def aliasedContentWriteEntry : Func :=
  lowerContextAt aliasedContentWrite
    (aliasedContentWrite.contexts[0]'(by decide))
    (aliasedContentWrite.impls[0]'(by decide))

theorem aliasedContentWrite_actual_entry :
    (lower aliasedContentWrite).funcs[0]? = some aliasedContentWriteEntry := by cbv

#guard ((replacementContentFlow (lower aliasedContentWrite)).forFunction aliasedContentWriteEntry
      (aliasedContentWriteEntry.valueTypes (lower aliasedContentWrite))).value 0 == some []
end Goose.Lower.Validation.ReplacementContentFlowSourceChecks
