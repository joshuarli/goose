import Goose.Lower.Flow

namespace Goose.Lower.LegacyDestinationChecks

open Goose.Core

example : stmtOk (.letS 0 (.bool true) 0) = false := by decide

example : stmtOk (.rebind 0 (.bool true) 0) = false := by decide

example : stmtReturnOk (.ret (some (.bool true)) 0) = false := by decide

private def malformed : Core.Module :=
  let main : Impl :=
    { name := "main", params := #[], results := #[],
      vars := #[⟨"r", .ref .mutable .bool, .mutable, 0, 0⟩,
        ⟨"frozen", .ref .readOnly .bool, .mutable, 0, 0⟩],
      body := .mk 0 [.letS 0 (.bool true) 0, .letS 1 (.read (.var 0)) 0] none, summary := .unknown }
  { files := #[], types := #[], globals := #[], impls := #[main],
    contexts := #[⟨0, "main", [], [], []⟩], entry := 0, origins := #[] }
#guard match Core.eval 20 .release malformed with | .done .returned "" => true | _ => false
#guard match GIR.run 50 .release (lower malformed) with | .fault _ => true | _ => false

end Goose.Lower.LegacyDestinationChecks
