import Goose.Lower.Validation.Checks

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core

set_option maxRecDepth 12000
set_option maxHeartbeats 2000000

def contentElementStore : Module :=
  let reference := Ty.ref .mutable (.slice .mutable (.int .i64))
  let elements := View.val (.read (.deref (.read (.var 0))))
  let target := Place.elem elements (.lit .i64 0) 0
  let receiver : Impl :=
    { name := "receiver", params := #[⟨0, .byRef⟩, ⟨1, .byRef⟩], results := #[],
      vars := #[⟨"left", reference, .immutable, 0, 0⟩, ⟨"right", reference, .immutable, 0, 0⟩],
      body := .mk 0 [.assign target (.lit .i64 1) 0] none,
      summary := .known ⟨[.param 0], [.param 1], [], [], [], true, false⟩ }
  { files := #["content-element-store.goose"], types := #[], globals := #[],
    impls := #[Checks.emptyEntry, receiver],
    contexts := #[⟨0, "main", [], [], []⟩,
      ⟨1, "receiver", [(0, [.param 0]), (1, [.param 1])], [],
        [(0, [.param 1]), (1, [])]⟩],
    entry := 0, origins := #[⟨0, 1, "expr"⟩] }

theorem contentElementStore_core_accepted : Core.validate contentElementStore = .ok () := by
  cbv

theorem contentElementStore_gir_accepted :
    GIR.validate (lower contentElementStore) = .ok () := by
  cbv

def sliceVariableStore : Module :=
  { contentElementStore with
    impls := contentElementStore.impls.modify 1 fun impl =>
      { impl with
        body := .mk 0 [.assign (.deref (.read (.var 0)))
          (.read (.deref (.read (.var 1)))) 0] none,
        summary := .known ⟨[.param 1], [.param 0], [], [], [.param 0], false, false⟩ },
    contexts := contentElementStore.contexts.modify 1 fun context =>
      { context with contentRoots := [(0, []), (1, [])] } }

def undeclaredSliceVariableStore : Module :=
  { sliceVariableStore with
    impls := sliceVariableStore.impls.modify 1 fun impl =>
      { impl with summary := .known ⟨[.param 1], [.param 0], [], [], [], false, false⟩ } }

theorem sliceVariableStore_core_accepted : Core.validate sliceVariableStore = .ok () := by
  cbv

theorem sliceVariableStore_gir_accepted : GIR.validate (lower sliceVariableStore) = .ok () := by
  cbv

theorem undeclaredSliceVariableStore_core_rejected :
    (match Core.validate undeclaredSliceVariableStore with
    | .error _ => true
    | .ok _ => false) = true := by
  cbv

theorem undeclaredSliceVariableStore_gir_rejected :
    (match GIR.validate (lower undeclaredSliceVariableStore) with
    | .error rejection => rejection.code == .v050
    | .ok _ => false) = true := by
  cbv

end Goose.Lower.Validation.SummaryPreservation
