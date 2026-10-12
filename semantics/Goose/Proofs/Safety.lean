import Goose.Core.Guarantees

/-!
The statement of the campaign's central safety theorem, not its proof.

`ThSafe01` is the target: acceptance by `validate` and nothing else implies
that `eval` never meets a fault, at any fuel, in either numeric profile. It is
stated here so that its exact form is fixed; it is not proved, and no theorem
in this tree concludes it. See `coverage.json` for what is proved toward it
(`Goose.Proofs.Memory`: the memory operations every evaluation rule is built
from keep typed locations typed and the live-reference invariant true) and for
what is missing: the induction on fuel over the fourteen evaluation functions,
which needs, at every syntactic form, an inversion of the typing pass and of
the root pass and the preservation of a frame invariant across scope entry,
scope exit and calls.
-/

namespace Goose.Proofs.Safety
open Goose.Core

/-- `TH-SAFE-01`: the target statement. -/
def ThSafe01 : Prop :=
  ∀ m : Module, validate m = .ok () → FaultFree m

end Goose.Proofs.Safety
