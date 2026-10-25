import Goose.Construct.Layout

set_option Elab.async false

namespace Goose.Proofs.ConstructionRepresentation
open Goose.Construct

theorem elementsEnd_fixed (layout : LayoutEnv) (bytes : ByteArray) (element : Ty) (width : Nat)
    (fixed : fixedByteSize? layout element = some width) (count start : Nat)
    (bounded : start + count * width ≤ bytes.size) :
    elementsEnd (count + 1) layout element count bytes start = .ok (start + count * width) := by
  induction count generalizing start with
  | zero => simp only [Nat.zero_mul, Nat.add_zero, elementsEnd]
  | succ count ih =>
      have one : ¬start + width > bytes.size := by
        rw [Nat.succ_mul] at bounded
        omega
      have step : packedEnd (count + 1) layout element bytes start = .ok (start + width) := by
        simp only [packedEnd, fixed, one, ↓reduceIte, pure, Except.pure]
      rw [elementsEnd, step]
      have rest : (start + width) + count * width ≤ bytes.size := by
        simpa only [Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using bounded
      simpa only [bind, Except.bind, Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (start + width) rest

#print axioms elementsEnd_fixed

end Goose.Proofs.ConstructionRepresentation
