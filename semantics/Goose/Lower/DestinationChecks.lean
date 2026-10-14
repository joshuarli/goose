import Goose.Core.Validate
import Goose.Core.Eval
import Goose.GIR.Validate
import Goose.GIR.Eval
import Goose.Lower.CoreToGir

namespace Goose.Lower.DestinationChecks

open Goose.Core

def source : Module :=
  let main : Impl :=
    { name := "main", params := #[], results := #[],
      vars := #[⟨"r", .ref .readOnly (.int .i64), .mutable, 0, 0⟩,
        ⟨"s", .slice .readOnly (.int .i64), .immutable, 0, 0⟩],
      body := .mk 0 [.letS 0 (.ref .mutable (.global 0)) 0,
        .rebind 0 (.ref .mutable (.global 0)) 0,
        .letS 1 (.slice .mutable (.of (.global 1)) .omitted .omitted 0) 0,
        .print [.expr (.read (.deref (.read (.var 0)))), .text " ",
          .expr (.len (.val (.read (.var 1)))), .text " ",
          .expr (.read (.deref (.call 1 [] 0)))] 0] none,
      summary := .unknown }
  let receiver : Impl :=
    { name := "receiver", params := #[], results := #[.ref .readOnly (.int .i64)],
      vars := #[], body := .mk 0 [.ret (some (.ref .mutable (.global 0))) 0] none,
      summary := .unknown }
  { files := #["readonly-destinations.goose"], types := #[],
    globals := #[⟨"scalar", .int .i64, .mutable, .lit .i64 7, 0⟩,
      ⟨"array", .arr (.int .i64) 1, .mutable, .arrLit (.arr (.int .i64) 1) [.lit .i64 9], 0⟩],
    impls := #[main, receiver], contexts := #[⟨0, "main", [(0, [.global 0]), (1, [.global 1])], [], []⟩,
      ⟨1, "receiver", [], [[.global 0]], []⟩], entry := 0, origins := #[⟨0, 1, "readonly"⟩] }

#guard [source, { source with profile := .shrink }].all fun module =>
  match Core.validate module, GIR.validate (lower module) with
  | .ok _, .ok _ => true
  | _, _ => false

#guard [source, { source with profile := .shrink }].all fun module =>
  [NumProfile.release, .debug].all fun profile =>
    match Core.eval 100 profile module, GIR.run 300 profile (lower module) with
    | .done .returned "7 1 7\n", .done .returned "7 1 7\n" => true
    | _, _ => false

end Goose.Lower.DestinationChecks
