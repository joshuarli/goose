import Goose.Construct.Validate
import Goose.Construct.Eval

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

def scalarTwoArgumentWitness : Module :=
  ⟨#["two-arguments.goose"], #[],
    #[⟨"counter", .int .i64, .mutable, .lit .i64 5, 0⟩],
    #[⟨"entry", #[], #[], #[],
      .mk 0 [.print [.expr (.call 1 [
        .byVal (.blockE (.mk 1 [.assign (.global 0) (.lit .i64 8) 0] (some (.lit .i64 3))) 0),
        .byVal (.read (.global 0))] 0)] 0] none, .unknown⟩,
      ⟨"helper", #[⟨0, .byValue⟩, ⟨1, .byValue⟩], #[⟨.int .i64, .register, none⟩],
        #[⟨"first", .int .i64, .immutable, 0, 0⟩, ⟨"second", .int .i64, .immutable, 0, 0⟩],
        .mk 0 [] (some (.bin .sub (.read (.var 1)) (.read (.var 0)) 0)), .unknown⟩],
    #[⟨0, "entry", [], [], []⟩, ⟨1, "helper", [], [[]], []⟩], 0, #[⟨0, 1, "call"⟩], #[], #[]⟩

theorem scalarTwoArgumentWitness_validation : validate scalarTwoArgumentWitness = .ok () := by cbv

theorem scalarTwoArgumentWitness_effects :
    match runModule 80 ⟨.release, scalarTwoArgumentWitness⟩ .initial with
    | .ok _ after => after.construction.stdout = "5\n".toUTF8 ∧
        after.objects.lookup (.global 0) = some (.int .i64 8)
    | _ => False := by cbv

theorem scalarTwoArgumentWitness_argumentOrder :
    match initGlobals 80 ⟨.release, scalarTwoArgumentWitness⟩ [0] .initial with
    | .ok _ initialized =>
      evalValue 20 ⟨.release, scalarTwoArgumentWitness⟩ ⟨0, 0, #[], [], []⟩ (.read (.global 0)) initialized =
        .ok (.int .i64 5) initialized ∧
      match evalArguments 20 ⟨.release, scalarTwoArgumentWitness⟩ ⟨0, 0, #[], [], []⟩
          #[⟨"first", .int .i64, .immutable, 0, 0⟩, ⟨"second", .int .i64, .immutable, 0, 0⟩]
          [⟨0, .byValue⟩, ⟨1, .byValue⟩]
          [.byVal (.blockE (.mk 1 [.assign (.global 0) (.lit .i64 8) 0] (some (.lit .i64 3))) 0),
            .byVal (.read (.global 0))] initialized with
      | .ok [.int .i64 3, .int .i64 8] after => after.objects.lookup (.global 0) = some (.int .i64 8)
      | _ => False
    | _ => False := by cbv

#print axioms scalarTwoArgumentWitness_argumentOrder
#print axioms scalarTwoArgumentWitness_validation
#print axioms scalarTwoArgumentWitness_effects
end Goose.Proofs.ConstructionAcceptedExecution
