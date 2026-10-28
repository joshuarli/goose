import Goose.Construct.Validate
import Goose.Proofs.OwnershipAmbientContinuations

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

def nestedGlobalReturnWitness : Module :=
  ⟨#["nested-global-return.goose"], #[],
    #[⟨"counter", .int .i64, .mutable, .bin .add (.lit .i64 2) (.lit .i64 3) 0, 0⟩,
      ⟨"global-bytes", .varr (.int .u8), .immutable, .bytes (.varr (.int .u8)) [71] 0, 0⟩],
    #[⟨"entry", #[], #[], #[⟨"bytes", .varr (.int .u8), .immutable, 0, 0⟩,
        ⟨"number", .int .i64, .immutable, 0, 0⟩, ⟨"result", .int .i64, .immutable, 0, 0⟩],
      .mk 0 [.letS 0 (.bytes (.varr (.int .u8)) [65] 0) 0, .letS 1 (.lit .i64 7) 0,
        .letS 2 (.call 1 [.byVal (.lit .i64 3), .byVal (.blockE (.mk 1 [.assign (.global 0) (.lit .i64 8) 0]
          (some (.lit .i64 4))) 0), .byVal (.blockE (.mk 2 [] (some (.blockE (.mk 3 [.assign (.global 0) (.bin .add (.read (.global 0)) (.lit .i64 1) 0) 0]
          (some (.lit .i64 2))) 0))) 0)] 0) 0] none, .unknown⟩,
      ⟨"helper", #[⟨0, .byValue⟩, ⟨1, .byValue⟩, ⟨2, .byValue⟩], #[⟨.int .i64, .register, none⟩],
        #[⟨"first", .int .i64, .immutable, 0, 0⟩, ⟨"second", .int .i64, .immutable, 0, 0⟩,
          ⟨"third", .int .i64, .immutable, 0, 0⟩],
        .mk 0 [.assign (.global 0) (.bin .add (.read (.global 0)) (.read (.var 2)) 0) 0]
          (some (.bin .add (.bin .sub (.read (.var 1)) (.read (.var 0)) 0) (.read (.var 2)) 0)), .unknown⟩],
    #[⟨0, "entry", [], [], []⟩, ⟨1, "helper", [], [[]], []⟩], 0, #[⟨0, 1, "call"⟩], #[], #[]⟩

theorem nestedGlobalReturnWitness_validation : validate nestedGlobalReturnWitness = .ok () := by cbv

theorem nestedGlobalReturnWitness_effects :
    match runModule 80 ⟨.release, nestedGlobalReturnWitness⟩ .initial with
    | .ok _ after => after.objects.lookup (.global 0) = some (.int .i64 11)
    | _ => False := by cbv

theorem nestedGlobalReturnWitness_registerResult :
    match initGlobals 80 ⟨.release, nestedGlobalReturnWitness⟩ [0, 1] .initial with
    | .ok _ initialized =>
      let activation : RuntimeActivation := ⟨0, initialized.nextAct,
        #[⟨"bytes", .varr (.int .u8), .immutable, 0, 0⟩, ⟨"number", .int .i64, .immutable, 0, 0⟩,
          ⟨"result", .int .i64, .immutable, 0, 0⟩], [], []⟩
      let activated := { initialized with nextAct := initialized.nextAct + 1, activations := activation :: initialized.activations }
      let scopeState := ownershipResultScopeState activation 0 activated
      let environment := { activation with scopes := [(0, activated.nextScope)] }
      match execStmts 50 ⟨.release, nestedGlobalReturnWitness⟩ environment
        [.letS 0 (.bytes (.varr (.int .u8)) [65] 0) 0, .letS 1 (.lit .i64 7) 0] scopeState with
      | .ok (.normal .unit) afterPrefix =>
        match invokeCall 50 ⟨.release, nestedGlobalReturnWitness⟩ environment 1
          [.byVal (.lit .i64 3), .byVal (.blockE (.mk 1 [.assign (.global 0) (.lit .i64 8) 0] (some (.lit .i64 4))) 0),
            .byVal (.blockE (.mk 2 [] (some (.blockE (.mk 3 [.assign (.global 0) (.bin .add (.read (.global 0)) (.lit .i64 1) 0) 0] (some (.lit .i64 2))) 0))) 0)] [.register (.int .i64)] 0 afterPrefix with
        | .ok [.register (.int .i64 3)] after => after.objects.lookup (.global 0) = some (.int .i64 11)
        | _ => False
      | _ => False
    | _ => False := by cbv

#print axioms nestedGlobalReturnWitness_validation
#print axioms nestedGlobalReturnWitness_effects
#print axioms nestedGlobalReturnWitness_registerResult
end Goose.Proofs.ConstructionAcceptedExecution
