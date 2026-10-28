import Goose.Proofs.ConstructionAcceptedByteCallModule

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

private def byteCallWitnessEntry : Impl :=
  ⟨"entry", #[], #[], #[⟨"result", .varr (.int .u8), .immutable, 0, 0⟩],
    .mk 0 [.letS 0 (.call 1 [] 0) 0] none, .unknown⟩

private def byteCallWitnessHelper : Impl :=
  ⟨"helper", #[], #[⟨.varr (.int .u8), .value, none⟩], #[],
    .mk 0 [] (some (.bytes (.varr (.int .u8)) [65, 66] 0)), .unknown⟩

private def byteCallWitnessModule : Module :=
  ⟨#["byte-return.goose"], #[], #[], #[byteCallWitnessEntry, byteCallWitnessHelper],
    #[⟨0, "entry", [], [], []⟩, ⟨1, "helper", [], [[]], []⟩], 0, #[⟨0, 1, "call"⟩], #[], #[]⟩

private def byteCallWitnessConfig : EvalConfig := ⟨.release, byteCallWitnessModule⟩

theorem byteCallWitness_validated : validate byteCallWitnessModule = .ok () := by cbv

private def byteCallWitnessBytes : Option (List UInt8) :=
  match runModule 80 byteCallWitnessConfig .initial with
  | .ok () state => (state.construction.storage[0]?).map (fun storage => storage.bytes.data.toList)
  | _ => none

theorem byteCallWitness_result : byteCallWitnessBytes = some [2, 0, 0, 0, 65, 66] := by decide +kernel

theorem byteCallWitness_allFuel (fuel : Nat) :
    ∃ initialized ambient types live regions,
      AcceptedWorld byteCallWitnessConfig initialized
        (Goose.Proofs.Exit.stepState (runModule fuel byteCallWitnessConfig .initial)) ambient types live regions [] ∧
      (match runModule fuel byteCallWitnessConfig .initial with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  apply acceptedByteCallModule_allFuel fuel byteCallWitnessConfig (acceptedModule byteCallWitnessConfig byteCallWitness_validated)
    ⟨0, "entry", [], [], []⟩ byteCallWitnessEntry ⟨1, "helper", [], [[]], []⟩ byteCallWitnessHelper
    0 1 0 [65, 66] 0 0
  · intro id inside
    simp [byteCallWitnessConfig, byteCallWitnessModule] at inside
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · simp [byteCallWitnessHelper]
  · decide

#print axioms byteCallWitness_validated
#print axioms byteCallWitness_result
#print axioms byteCallWitness_allFuel
end Goose.Proofs.ConstructionAcceptedExecution
