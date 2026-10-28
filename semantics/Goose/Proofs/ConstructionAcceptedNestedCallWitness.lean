import Goose.Construct.Validate
import Goose.Construct.Eval
import Goose.Proofs.ConstructionAcceptedLocalRead

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

private def nestedCallSummary : SummaryAnn := .known ⟨[], [], [], [], [], [], [], [], false, false⟩
private def nestedCallEntry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, nestedCallSummary⟩
private def nestedCallInner : Impl := ⟨"inner", #[], #[⟨.int .i64, .register, none⟩],
  #[⟨"value", .int .i64, .immutable, 0, 0⟩],
  .mk 0 [.letS 0 (.lit .i64 7) 0] (some (.read (.var 0))), nestedCallSummary⟩
private def nestedCallOuter : Impl := ⟨"outer", #[], #[⟨.int .i64, .register, none⟩], #[],
  .mk 0 [] (some (.call 2 [] 0)), nestedCallSummary⟩
private def nestedCallModule : Module := ⟨#["nested-call.goose"], #[.int .i64],
  #[⟨"answer", .int .i64, .immutable, .call 1 [] 0, 0⟩],
  #[nestedCallEntry, nestedCallOuter, nestedCallInner],
  #[⟨0, "entry", [], [], []⟩, ⟨1, "outer", [], [[]], []⟩, ⟨2, "inner", [], [[]], []⟩],
  0, #[⟨0, 1, "call"⟩], #[], #[]⟩
private def nestedCallObservation : Option Int :=
  match runModule 100 ⟨.release, nestedCallModule⟩ .initial with
  | .ok () state => match state.objects.lookup (.global 0) with
    | some (.int .i64 value) => some value
    | _ => none
  | _ => none

theorem validated_global_noDirectLocalRead (module : Module) (global localId : Nat) (descriptor : Global)
    (accepted : validate module = .ok ()) (present : module.globals[global]? = some descriptor) :
    descriptor.init ≠ .read (.var localId) := by
  intro shape
  obtain ⟨ty, after, typed, _⟩ := validated_global_initializer_typing module global descriptor accepted present
  rw [shape] at typed
  obtain ⟨_, visible, _, _, _, _⟩ := typeExpr_localRead_descriptor 4096
    { module := module, implementation := none, variables := #[], visible := [], scope := 0, loops := 0,
      globalLimit := global } localId 0 after ty typed
  simp at visible

theorem nestedCall_validated : validate nestedCallModule = .ok () := by cbv

theorem nestedCall_result : nestedCallObservation = some 7 := by decide +kernel

#print axioms validated_global_noDirectLocalRead
#print axioms nestedCall_validated
#print axioms nestedCall_result
end Goose.Proofs.ConstructionAcceptedExecution
