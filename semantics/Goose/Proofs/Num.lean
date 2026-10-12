import Goose.Core.Num

/-!
Each integer primitive of `Goose.Core` against its row of the numeric rules,
stated over mathematical integers.

The theorems below cover range, congruence, the exact arithmetic result,
division and remainder, shift counts, and conversions. For the bitwise
operations and `bitnot` they prove only that the result is in range; their
values are checked by the evaluated examples at the end of the file.
-/

namespace Goose.Proofs.Num

open Goose.Core

theorem inRange_iff (t : IntTy) (x : Int) :
    t.inRange x = true ↔ t.minVal ≤ x ∧ x ≤ t.maxVal := by
  simp [IntTy.inRange]

/-! ### `wrap` -/

theorem wrap_inRange (t : IntTy) (x : Int) : t.inRange (wrap t x) = true := by
  rw [inRange_iff]
  cases t <;> simp [wrap, IntTy.minVal, IntTy.maxVal, IntTy.signed, IntTy.bits] <;> omega

theorem wrap_congr (t : IntTy) (x : Int) : ((2 : Int) ^ t.bits) ∣ wrap t x - x := by
  cases t <;> simp [wrap, IntTy.maxVal, IntTy.signed, IntTy.bits] <;> omega

theorem wrap_of_inRange (t : IntTy) (x : Int) (h : t.inRange x = true) : wrap t x = x := by
  rw [inRange_iff] at h
  revert h
  cases t <;> simp [wrap, IntTy.minVal, IntTy.maxVal, IntTy.signed, IntTy.bits] <;> omega

/-! ### Checked arithmetic -/

theorem checked_release (t : IntTy) (r : Int) :
    checked .release t r = .ok (wrap t r) := by
  unfold checked
  split
  · rename_i h; rw [wrap_of_inRange t r h]
  · simp

theorem checked_unsigned (p : NumProfile) (t : IntTy) (r : Int) (h : t.signed = false) :
    checked p t r = .ok (wrap t r) := by
  unfold checked
  split
  · rename_i h'; rw [wrap_of_inRange t r h']
  · simp [h]

theorem checked_debug_signed (t : IntTy) (r : Int) (h : t.signed = true) :
    checked .debug t r = if t.inRange r then .ok r else .error .intOverflow := by
  unfold checked
  split
  · simp_all
  · simp [*]

theorem checked_inRange (p : NumProfile) (t : IntTy) (r v : Int)
    (h : checked p t r = .ok v) : t.inRange v = true := by
  unfold checked at h
  split at h
  · cases h; assumption
  · split at h
    · cases h
    · cases h; exact wrap_inRange t r

section arith

variable (t : IntTy) (a b : Int)

theorem add_release : evalBin .release .add t a b = .ok (wrap t (a + b)) :=
  checked_release t _
theorem sub_release : evalBin .release .sub t a b = .ok (wrap t (a - b)) :=
  checked_release t _
theorem mul_release : evalBin .release .mul t a b = .ok (wrap t (a * b)) :=
  checked_release t _
theorem neg_release : evalUn .release .neg t a = .ok (wrap t (-a)) :=
  checked_release t _

variable (p : NumProfile) (hu : t.signed = false)
include hu

theorem add_unsigned : evalBin p .add t a b = .ok (wrap t (a + b)) :=
  checked_unsigned p t _ hu
theorem sub_unsigned : evalBin p .sub t a b = .ok (wrap t (a - b)) :=
  checked_unsigned p t _ hu
theorem mul_unsigned : evalBin p .mul t a b = .ok (wrap t (a * b)) :=
  checked_unsigned p t _ hu
theorem neg_unsigned : evalUn p .neg t a = .ok (wrap t (-a)) :=
  checked_unsigned p t _ hu

end arith

section debug

variable (t : IntTy) (a b : Int) (hs : t.signed = true)
include hs

theorem add_debug_signed : evalBin .debug .add t a b =
    if t.inRange (a + b) then .ok (a + b) else .error .intOverflow :=
  checked_debug_signed t _ hs
theorem sub_debug_signed : evalBin .debug .sub t a b =
    if t.inRange (a - b) then .ok (a - b) else .error .intOverflow :=
  checked_debug_signed t _ hs
theorem mul_debug_signed : evalBin .debug .mul t a b =
    if t.inRange (a * b) then .ok (a * b) else .error .intOverflow :=
  checked_debug_signed t _ hs
theorem neg_debug_signed : evalUn .debug .neg t a =
    if t.inRange (-a) then .ok (-a) else .error .intOverflow :=
  checked_debug_signed t _ hs

end debug

/-! ### Division and remainder -/

theorem div_zero (p : NumProfile) (t : IntTy) (a : Int) :
    evalBin p .div t a 0 = .error .divZero := by
  simp [evalBin]

theorem div_inRange (p : NumProfile) (t : IntTy) (a b : Int) (hb : b ≠ 0)
    (h : t.inRange (Int.tdiv a b) = true) : evalBin p .div t a b = .ok (Int.tdiv a b) := by
  simp [evalBin, hb, h]

theorem div_i64_min (p : NumProfile) :
    evalBin p .div .i64 IntTy.i64.minVal (-1) = .error .divOverflow := by
  cases p <;> rfl

theorem div_narrow_min_debug (t : IntTy) (hs : t.signed = true) (h64 : t ≠ .i64) :
    evalBin .debug .div t t.minVal (-1) = .error .intOverflow := by
  cases t <;> first | rfl | (exfalso; exact h64 rfl) | (exfalso; simp [IntTy.signed] at hs)

theorem div_narrow_min_release (t : IntTy) (hs : t.signed = true) (h64 : t ≠ .i64) :
    evalBin .release .div t t.minVal (-1) = .ok t.minVal := by
  cases t <;> first | rfl | (exfalso; exact h64 rfl) | (exfalso; simp [IntTy.signed] at hs)

theorem mod_zero (p : NumProfile) (t : IntTy) (a : Int) :
    evalBin p .mod t a 0 = .error .divZero := by
  simp [evalBin]

theorem mod_spec (p : NumProfile) (t : IntTy) (a b : Int) (hb : b ≠ 0) :
    ∃ r, evalBin p .mod t a b = .ok r ∧ 0 ≤ r ∧ r < (b.natAbs : Int) ∧
      ∃ q, a = q * b + r := by
  refine ⟨a % b, by simp [evalBin, hb], Int.emod_nonneg a hb, ?_, a / b, ?_⟩
  · have := Int.emod_lt a hb
    omega
  · have := Int.emod_add_mul_ediv a b
    rw [Int.mul_comm] at this
    omega

theorem mod_inRange (p : NumProfile) (t : IntTy) (a b r : Int)
    (ha : t.inRange a = true) (hb : t.inRange b = true) (hne : b ≠ 0)
    (h : evalBin p .mod t a b = .ok r) : t.inRange r = true := by
  simp [evalBin, hne] at h
  subst h
  rw [inRange_iff] at *
  have h1 := Int.emod_nonneg a hne
  have h2 := Int.emod_lt a hne
  revert ha hb h1 h2
  cases t <;> simp [IntTy.minVal, IntTy.maxVal, IntTy.signed, IntTy.bits] <;> omega

/-! ### Shifts -/

/-- The shift count after masking to `0..bits-1`. -/
def shiftCount (t : IntTy) (b : Int) : Nat := (b % (t.bits : Int)).toNat

theorem shl_eq (p : NumProfile) (t : IntTy) (a b : Int) :
    evalBin p .shl t a b = .ok (wrap t (a * (2 : Int) ^ shiftCount t b)) := rfl

theorem shr_eq (p : NumProfile) (t : IntTy) (a b : Int) :
    evalBin p .shr t a b = .ok (a / (2 : Int) ^ shiftCount t b) := by
  simp [evalBin, shiftCount, Int.shiftRight_eq_div_pow]

theorem shift_count_only (p : NumProfile) (op : BinOp) (t : IntTy) (a b c : Int)
    (hop : op = .shl ∨ op = .shr) (h : b % (t.bits : Int) = c % (t.bits : Int)) :
    evalBin p op t a b = evalBin p op t a c := by
  rcases hop with rfl | rfl <;> simp [evalBin, h]

theorem shr_inRange (p : NumProfile) (t : IntTy) (a b v : Int)
    (ha : t.inRange a = true) (h : evalBin p .shr t a b = .ok v) : t.inRange v = true := by
  rw [shr_eq] at h
  cases h
  have hk : (0 : Int) < 2 ^ shiftCount t b := Int.pow_pos (by decide)
  rw [inRange_iff] at *
  obtain ⟨hlo, hhi⟩ := ha
  have hmin : t.minVal ≤ 0 := by cases t <;> decide
  have hmax : 0 ≤ t.maxVal := by cases t <;> decide
  generalize (2 : Int) ^ shiftCount t b = k at hk
  constructor
  · by_cases h0 : 0 ≤ a
    · have := Int.ediv_nonneg h0 (Int.le_of_lt hk)
      omega
    · have : a ≤ a / k := by
        rw [Int.le_ediv_iff_mul_le hk]
        have : 0 ≤ (k - 1) * (-a) := Int.mul_nonneg (by omega) (by omega)
        rw [Int.sub_mul, Int.mul_neg, Int.mul_neg, Int.one_mul] at this
        rw [Int.mul_comm]
        omega
      omega
  · by_cases h0 : 0 ≤ a
    · have := Int.ediv_le_self k h0
      omega
    · have : a / k ≤ 0 := (Int.ediv_le_iff_le_mul hk).2 (by omega)
      omega

/-! ### Bitwise operations -/

theorem ofBits_inRange (t : IntTy) (v : BitVec t.bits) : t.inRange (ofBits t v) = true := by
  have h1 := BitVec.le_toInt v
  have h2 : v.toInt < 2 ^ (t.bits - 1) := BitVec.toInt_lt
  have h3 := v.isLt
  rw [inRange_iff]
  revert h1 h2 h3
  cases t <;> simp [ofBits, IntTy.minVal, IntTy.maxVal, IntTy.signed, IntTy.bits] <;> omega

theorem bitwise_inRange (p : NumProfile) (op : BinOp) (t : IntTy) (a b v : Int)
    (hop : op = .bitand ∨ op = .bitor ∨ op = .bitxor)
    (h : evalBin p op t a b = .ok v) : t.inRange v = true := by
  rcases hop with rfl | rfl | rfl <;>
  · simp only [evalBin, Except.ok.injEq] at h
    subst h
    exact ofBits_inRange _ _

theorem bitnot_inRange (p : NumProfile) (t : IntTy) (a v : Int)
    (h : evalUn p .bitnot t a = .ok v) : t.inRange v = true := by
  simp only [evalUn, Except.ok.injEq] at h
  subst h
  exact ofBits_inRange _ _

/-! ### Conversions -/

theorem widen_id (p : NumProfile) (src dst : IntTy) (a : Int) :
    evalConv p .widen src dst a = .ok a := rfl

theorem asUnchecked_wrap (p : NumProfile) (src dst : IntTy) (a : Int) :
    evalConv p .asUnchecked src dst a = .ok (wrap dst a) := rfl

theorem as_release_wrap (src dst : IntTy) (a : Int) :
    evalConv .release .as src dst a = .ok (wrap dst a) := by
  by_cases h : dst.inRange a = true
  · simp [evalConv, h, wrap_of_inRange dst a h]
  · simp [evalConv, h]

theorem as_debug (src dst : IntTy) (a : Int) :
    evalConv .debug .as src dst a =
      if dst.inRange a then .ok a else .error .castRange := by
  by_cases h : dst.inRange a = true <;> simp [evalConv, h]

/-! ### Every returned value is in range -/

theorem evalUn_inRange (p : NumProfile) (op : UnOp) (t : IntTy) (a v : Int)
    (h : evalUn p op t a = .ok v) : t.inRange v = true := by
  cases op
  · exact checked_inRange p t _ v h
  · exact bitnot_inRange p t a v h

theorem evalBin_inRange (p : NumProfile) (op : BinOp) (t : IntTy) (a b v : Int)
    (ha : t.inRange a = true) (hb : t.inRange b = true)
    (h : evalBin p op t a b = .ok v) : t.inRange v = true := by
  cases op
  case add => exact checked_inRange p t _ v h
  case sub => exact checked_inRange p t _ v h
  case mul => exact checked_inRange p t _ v h
  case div =>
    by_cases hb0 : b = 0
    · simp [evalBin, hb0] at h
    · by_cases hr : t.inRange (Int.tdiv a b) = true
      · simp only [evalBin, hb0, hr, ite_true, ite_false, Except.ok.injEq] at h
        subst h; exact hr
      · by_cases h64 : t = .i64
        · subst h64; simp [evalBin, hb0, hr] at h
        · have h' : checked p t (Int.tdiv a b) = .ok v := by
            simpa [evalBin, hb0, hr, h64] using h
          exact checked_inRange p t _ v h'
  case mod =>
    by_cases hb0 : b = 0
    · subst hb0; simp [evalBin] at h
    · exact mod_inRange p t a b v ha hb hb0 h
  case bitand => exact bitwise_inRange p .bitand t a b v (by simp) h
  case bitor => exact bitwise_inRange p .bitor t a b v (by simp) h
  case bitxor => exact bitwise_inRange p .bitxor t a b v (by simp) h
  case shl =>
    rw [shl_eq] at h; cases h; exact wrap_inRange t _
  case shr => exact shr_inRange p t a b v ha h

/-- `widen` is only produced where the value is representable in the target, so
that is a hypothesis here rather than something the evaluator re-checks. -/
theorem evalConv_inRange (p : NumProfile) (k : ConvKind) (src dst : IntTy) (a v : Int)
    (hw : k = .widen → dst.inRange a = true)
    (h : evalConv p k src dst a = .ok v) : dst.inRange v = true := by
  cases k
  · simp only [evalConv, Except.ok.injEq] at h; subst h; exact hw rfl
  · by_cases hr : dst.inRange a = true
    · simp only [evalConv, hr, ite_true, Except.ok.injEq] at h; subst h; exact hr
    · cases p
      · have hr' : dst.inRange a = false := by simpa using hr
        simp only [evalConv, hr', Bool.false_eq_true, ite_false, Except.ok.injEq] at h
        subst h; exact wrap_inRange dst a
      · simp [evalConv, hr] at h
  · simp only [evalConv, Except.ok.injEq] at h; subst h; exact wrap_inRange dst a

/-! ### Evaluated examples -/

private def allTys : List IntTy := [.i8, .i16, .i32, .i64, .u8, .u16, .u32, .u64]
private def sTys : List IntTy := [.i8, .i16, .i32, .i64]
private def uTys : List IntTy := [.u8, .u16, .u32, .u64]

private def same : Except NumAbort Int → Except NumAbort Int → Bool
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false

private def bin (p : NumProfile) (op : BinOp) (t : IntTy) (a b : Int)
    (e : Except NumAbort Int) : Bool := same (evalBin p op t a b) e

/-- Signed wrap-around at the extremes of every signed width, release then debug. -/
example : sTys.all (fun t =>
    bin .release .add t t.maxVal 1 (.ok t.minVal) && bin .debug .add t t.maxVal 1 (.error .intOverflow) &&
    bin .release .add t t.minVal (-1) (.ok t.maxVal) && bin .debug .add t t.minVal (-1) (.error .intOverflow) &&
    bin .release .sub t t.minVal 1 (.ok t.maxVal) && bin .debug .sub t t.minVal 1 (.error .intOverflow) &&
    bin .release .sub t t.maxVal (-1) (.ok t.minVal) && bin .debug .sub t t.maxVal (-1) (.error .intOverflow) &&
    bin .release .sub t 0 t.minVal (.ok t.minVal) && bin .debug .sub t 0 t.minVal (.error .intOverflow) &&
    bin .release .mul t t.minVal (-1) (.ok t.minVal) && bin .debug .mul t t.minVal (-1) (.error .intOverflow) &&
    bin .release .mul t t.maxVal t.maxVal (.ok 1) && bin .debug .mul t t.maxVal t.maxVal (.error .intOverflow) &&
    bin .release .mul t t.minVal t.minVal (.ok 0) && bin .debug .mul t t.minVal t.minVal (.error .intOverflow)) = true := by
  decide

/-- Operations that stay in range are identical in both profiles. -/
example : sTys.all (fun t => [NumProfile.release, .debug].all (fun p =>
    bin p .add t 0 0 (.ok 0) && bin p .add t t.minVal t.maxVal (.ok (-1)) &&
    bin p .add t t.maxVal (-1) (.ok (t.maxVal - 1)) && bin p .add t t.minVal 0 (.ok t.minVal) &&
    bin p .sub t t.minVal (-1) (.ok (t.minVal + 1)) && bin p .sub t (-1) (-1) (.ok 0) &&
    bin p .sub t 0 t.maxVal (.ok (-t.maxVal)) &&
    bin p .mul t t.minVal 0 (.ok 0) && bin p .mul t t.maxVal (-1) (.ok (-t.maxVal)) &&
    bin p .mul t (-1) (-1) (.ok 1) && bin p .mul t t.minVal 1 (.ok t.minVal))) = true := by
  decide

/-- Unsigned `+ - *` wrap modulo `2^w` in every profile. -/
example : uTys.all (fun t => [NumProfile.release, .debug].all (fun p =>
    bin p .add t t.maxVal 1 (.ok 0) && bin p .add t t.maxVal t.maxVal (.ok (t.maxVal - 1)) &&
    bin p .add t 0 0 (.ok 0) &&
    bin p .sub t 0 1 (.ok t.maxVal) && bin p .sub t 0 t.maxVal (.ok 1) && bin p .sub t 0 0 (.ok 0) &&
    bin p .mul t t.maxVal t.maxVal (.ok 1) && bin p .mul t t.maxVal 0 (.ok 0) &&
    bin p .mul t t.maxVal 2 (.ok (t.maxVal - 1)))) = true := by
  decide

example : (sTys.all fun t =>
    same (evalUn .release .neg t t.minVal) (.ok t.minVal) &&
    same (evalUn .debug .neg t t.minVal) (.error .intOverflow) &&
    same (evalUn .release .neg t t.maxVal) (.ok (-t.maxVal)) &&
    same (evalUn .debug .neg t t.maxVal) (.ok (-t.maxVal)) &&
    same (evalUn .debug .neg t 0) (.ok 0) && same (evalUn .debug .neg t (-1)) (.ok 1)) = true := by
  decide

example : (allTys.all fun t =>
    same (evalUn .debug .bitnot t 0) (if t.signed then .ok (-1) else .ok t.maxVal) &&
    same (evalUn .release .bitnot t t.maxVal) (.ok (if t.signed then t.minVal else 0)) &&
    same (evalUn .release .bitnot t t.minVal) (.ok (if t.signed then t.maxVal else t.maxVal))) = true := by
  decide

example : (allTys.all fun t =>
    bin .debug .bitand t t.maxVal 0 (.ok 0) && bin .debug .bitor t t.maxVal 0 (.ok t.maxVal) &&
    bin .debug .bitxor t t.maxVal t.maxVal (.ok 0) &&
    bin .debug .bitxor t t.minVal t.maxVal (.ok (if t.signed then -1 else t.maxVal)) &&
    bin .debug .bitand t t.maxVal t.minVal (.ok (if t.signed then 0 else 0)) &&
    bin .debug .bitor t t.minVal t.maxVal (.ok (if t.signed then -1 else t.maxVal))) = true := by
  decide

/-- Division is truncating; a zero divisor aborts in both profiles. -/
example : (allTys.all fun t => [NumProfile.release, .debug].all fun p =>
    bin p .div t t.maxVal 0 (.error .divZero) && bin p .div t 0 0 (.error .divZero) &&
    bin p .div t t.minVal 0 (.error .divZero) &&
    bin p .mod t t.maxVal 0 (.error .divZero) && bin p .mod t 0 0 (.error .divZero) &&
    bin p .mod t t.minVal 0 (.error .divZero) &&
    bin p .div t t.maxVal 1 (.ok t.maxVal) && bin p .div t 0 1 (.ok 0) &&
    bin p .div t t.maxVal t.maxVal (.ok 1)) = true := by
  decide

example : (sTys.all fun t => [NumProfile.release, .debug].all fun p =>
    bin p .div t (-7) 2 (.ok (-3)) && bin p .div t 7 (-2) (.ok (-3)) &&
    bin p .div t (-7) (-2) (.ok 3) && bin p .div t t.maxVal (-1) (.ok (-t.maxVal)) &&
    bin p .div t t.minVal 1 (.ok t.minVal) && bin p .div t (-1) (-1) (.ok 1)) = true := by
  decide

/-- `i64.min / -1` aborts with `divOverflow`; narrower minimums are ordinary overflow. -/
example : bin .release .div .i64 IntTy.i64.minVal (-1) (.error .divOverflow) = true := by decide
example : bin .debug .div .i64 IntTy.i64.minVal (-1) (.error .divOverflow) = true := by decide
example : bin .release .div .i8 (-128) (-1) (.ok (-128)) = true := by decide
example : bin .debug .div .i8 (-128) (-1) (.error .intOverflow) = true := by decide
example : ([IntTy.i8, .i16, .i32].all fun t =>
    bin .release .div t t.minVal (-1) (.ok t.minVal) &&
    bin .debug .div t t.minVal (-1) (.error .intOverflow)) = true := by decide

/-- Remainder is Euclidean and never overflows. -/
example : bin .release .mod .i64 (-5) 3 (.ok 1) = true := by decide
example : bin .debug .mod .i64 5 (-3) (.ok 2) = true := by decide
example : bin .debug .mod .i8 (-5) (-3) (.ok 1) = true := by decide
example : bin .debug .mod .i8 5 3 (.ok 2) = true := by decide
example : bin .debug .mod .i64 IntTy.i64.minVal (-1) (.ok 0) = true := by decide
example : bin .release .mod .i64 IntTy.i64.minVal (-1) (.ok 0) = true := by decide
example : (sTys.all fun t => [NumProfile.release, .debug].all fun p =>
    bin p .mod t t.minVal (-1) (.ok 0) && bin p .mod t t.minVal t.maxVal (.ok (t.maxVal - 1)) &&
    bin p .mod t t.maxVal t.minVal (.ok t.maxVal) && bin p .mod t (-1) t.minVal (.ok (t.maxVal + 1 + t.minVal - 1 + (-t.minVal)))) = true := by
  decide

/-- Shift counts are reduced modulo the width; `>>` on signed types is arithmetic. -/
example : bin .debug .shr .i8 (-128) 9 (.ok (-64)) = true := by decide
example : bin .release .shr .i8 (-128) 9 (.ok (-64)) = true := by decide
example : (allTys.all fun t => [NumProfile.release, .debug].all fun p =>
    let w : Int := t.bits
    bin p .shl t 1 0 (.ok 1) && bin p .shr t t.maxVal 0 (.ok t.maxVal) &&
    bin p .shl t 1 w (.ok 1) && bin p .shl t 1 (w + 1) (.ok 2) &&
    bin p .shr t t.maxVal w (.ok t.maxVal) && bin p .shr t t.maxVal (w + 1) (.ok (t.maxVal / 2)) &&
    bin p .shl t 1 (w - 1) (.ok (if t.signed then t.minVal else t.maxVal / 2 + 1)) &&
    bin p .shr t t.maxVal (w - 1) (.ok (if t.signed then 0 else 1)) &&
    bin p .shl t t.maxVal 1 (.ok (if t.signed then -2 else t.maxVal - 1))) = true := by
  decide
example : (sTys.all fun t => [NumProfile.release, .debug].all fun p =>
    let w : Int := t.bits
    bin p .shl t 1 (-1) (.ok t.minVal) && bin p .shr t t.minVal (-1) (.ok (-1)) &&
    bin p .shr t (-1) (-1) (.ok (-1)) && bin p .shr t t.maxVal (-1) (.ok 0) &&
    bin p .shr t t.minVal (w - 1) (.ok (-1)) && bin p .shr t t.minVal w (.ok t.minVal) &&
    bin p .shr t t.minVal (w + 1) (.ok (t.minVal / 2)) &&
    bin p .shl t t.minVal 1 (.ok 0) && bin p .shl t (-1) (w - 1) (.ok t.minVal)) = true := by
  decide

/-- Conversions. -/
private def conv (p : NumProfile) (k : ConvKind) (src dst : IntTy) (a : Int)
    (e : Except NumAbort Int) : Bool := same (evalConv p k src dst a) e

example : conv .release .as .i64 .u8 300 (.ok 44) = true := by decide
example : conv .debug .as .i64 .u8 300 (.error .castRange) = true := by decide
example : conv .release .asUnchecked .i64 .u8 300 (.ok 44) = true := by decide
example : conv .debug .asUnchecked .i64 .u8 300 (.ok 44) = true := by decide
example : conv .release .as .i64 .u64 (-1) (.ok 18446744073709551615) = true := by decide
example : conv .debug .as .i64 .u64 (-1) (.error .castRange) = true := by decide
example : conv .debug .asUnchecked .i64 .u64 (-1) (.ok 18446744073709551615) = true := by decide
example : conv .release .as .u64 .i64 18446744073709551615 (.ok (-1)) = true := by decide
example : conv .debug .as .i64 .i8 127 (.ok 127) = true := by decide
example : conv .debug .as .i64 .i8 128 (.error .castRange) = true := by decide
example : conv .release .as .i64 .i8 128 (.ok (-128)) = true := by decide
example : conv .release .as .i64 .i8 (-129) (.ok 127) = true := by decide
example : conv .debug .as .i64 .i8 (-128) (.ok (-128)) = true := by decide
example : conv .debug .widen .i8 .i64 (-128) (.ok (-128)) = true := by decide

end Goose.Proofs.Num
