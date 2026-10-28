import Goose.Construct.Validate
import Goose.Proofs.OwnershipAmbientContinuations

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

def nestedEmptyCallWitness : Module :=
  ⟨#["nested-empty-call.goose"], #[],
    #[⟨"counter", .int .i64, .mutable, .bin .add (.lit .i64 2) (.lit .i64 3) 0, 0⟩,
      ⟨"global-bytes", .varr (.int .u8), .immutable, .bytes (.varr (.int .u8)) [71] 0, 0⟩],
    #[⟨"entry", #[], #[], #[⟨"bytes", .varr (.int .u8), .immutable, 0, 0⟩,
        ⟨"number", .int .i64, .immutable, 0, 0⟩],
      .mk 0 [.letS 0 (.bytes (.varr (.int .u8)) [65] 0) 0, .letS 1 (.lit .i64 7) 0]
        (some (.call 1 [.byVal (.lit .i64 3),
          .byVal (.blockE (.mk 1 [.assign (.global 0) (.lit .i64 8) 0] (some (.lit .i64 4))) 0),
          .byVal (.blockE (.mk 2 [] (some (.blockE (.mk 3
            [.assign (.global 0) (.bin .add (.read (.global 0)) (.lit .i64 1) 0) 0]
            (some (.lit .i64 2))) 0))) 0)] 0)), .unknown⟩,
      ⟨"helper", #[⟨0, .byValue⟩, ⟨1, .byValue⟩, ⟨2, .byValue⟩], #[],
        #[⟨"first", .int .i64, .immutable, 0, 0⟩, ⟨"second", .int .i64, .immutable, 0, 0⟩,
          ⟨"third", .int .i64, .immutable, 0, 0⟩, ⟨"bytes", .varr (.int .u8), .immutable, 0, 0⟩,
          ⟨"flag", .bool, .immutable, 0, 0⟩],
        .mk 0 [.letS 3 (.bytes (.varr (.int .u8)) [66] 0) 0, .letS 4 (.bool false) 0] none, .unknown⟩],
    #[⟨0, "entry", [], [], []⟩, ⟨1, "helper", [], [], []⟩], 0, #[⟨0, 1, "call"⟩], #[], #[]⟩

theorem nestedEmptyCallWitness_validation : validate nestedEmptyCallWitness = .ok () := by cbv

theorem nestedEmptyCallWitness_effects :
    match runModule 100 ⟨.release, nestedEmptyCallWitness⟩ .initial with
    | .ok _ after => after.objects.lookup (.global 0) = some (.int .i64 9)
    | _ => False := by cbv

#print axioms nestedEmptyCallWitness_validation
#print axioms nestedEmptyCallWitness_effects
end Goose.Proofs.ConstructionAcceptedExecution
