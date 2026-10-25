import Goose.Construct.Validate
import Goose.Construct.Eval
set_option Elab.async false
namespace Goose.Proofs.ConstructionRootCorrespondence.InitializationBoundary
open Goose.Construct
private def summary : SummaryAnn := .known ⟨[], [], [], [], [], [], [], [], false, false⟩
private def entry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, summary⟩
private def helper : Impl := ⟨"constant", #[], #[⟨.int .i64, .register, none⟩],
  #[⟨"future", .ref .readOnly (.int .i64), .immutable, 0, 0⟩],
  .mk 0 [.letS 0 (.ref .readOnly (.global 1)) 0] (some (.lit .i64 7)), summary⟩
private def program : Module := ⟨#["initializer-helper.goose"], #[.int .i64],
  #[⟨"answer", .int .i64, .immutable, .call 1 [] 0, 0⟩,
    ⟨"later", .int .i64, .immutable, .lit .i64 9, 0⟩], #[entry, helper],
  #[⟨0, "entry", [], [], []⟩, ⟨1, "constant", [(0, [.global 1])], [[]], []⟩],
  0, #[⟨0, 17, "call"⟩], #[], #[]⟩
private def prefixObservation : Option (Int × Bool) :=
  match initGlobals 64 ⟨.release, program⟩ [0] .initial with
  | .ok () state => match state.objects.lookup (.global 0) with
      | some (.int .i64 value) => some (value, (state.objects.lookup (.global 1)).isNone)
      | _ => none
  | _ => none

private def helperTyping (globalLimit : Nat) : TypingEnv := {
  module := program
  implementation := some helper
  variables := helper.vars
  visible := []
  scope := 0
  loops := 0
  use := .result
  request := .value
  resultRequests := [.register]
  globalLimit := globalLimit }

theorem dead_future_reference_validated : validate program = .ok () := by cbv

theorem first_global_initialized_without_future_storage : prefixObservation = some (7, true) := by cbv

theorem helper_full_module_typing : typeBlock 64 (helperTyping 2) helper.body 0 = .ok ([.int .i64], 1) := by cbv

theorem helper_prefix_typing_rejected : typeBlock 64 (helperTyping 0) helper.body 0 =
    .error ⟨.root, "global is not initialized at this point"⟩ := by cbv

end Goose.Proofs.ConstructionRootCorrespondence.InitializationBoundary
