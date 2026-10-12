namespace Goose.Core

/-- The fixed-width integer types. -/
inductive IntTy | i8 | i16 | i32 | i64 | u8 | u16 | u32 | u64
  deriving DecidableEq, Repr, Inhabited

def IntTy.bits : IntTy → Nat
  | .i8 | .u8 => 8
  | .i16 | .u16 => 16
  | .i32 | .u32 => 32
  | .i64 | .u64 => 64

def IntTy.signed : IntTy → Bool
  | .i8 | .i16 | .i32 | .i64 => true
  | .u8 | .u16 | .u32 | .u64 => false

def IntTy.minVal (t : IntTy) : Int :=
  if t.signed then -((2 : Int) ^ (t.bits - 1)) else 0

def IntTy.maxVal (t : IntTy) : Int :=
  if t.signed then (2 : Int) ^ (t.bits - 1) - 1 else (2 : Int) ^ t.bits - 1

def IntTy.inRange (t : IntTy) (x : Int) : Bool :=
  decide (t.minVal ≤ x) && decide (x ≤ t.maxVal)

/-- The value of type `t` congruent to `x` modulo `2^bits`. -/
def wrap (t : IntTy) (x : Int) : Int :=
  let r := x % ((2 : Int) ^ t.bits)
  if t.signed && decide (r > t.maxVal) then r - (2 : Int) ^ t.bits else r

/-- Debug profiles abort on signed overflow and narrowing casts; release wraps. -/
inductive NumProfile | release | debug
  deriving DecidableEq, Repr

inductive NumAbort | divZero | divOverflow | intOverflow | castRange
  deriving DecidableEq, Repr

inductive UnOp | neg | bitnot
inductive BinOp | add | sub | mul | div | mod | bitand | bitor | bitxor | shl | shr
inductive CmpOp | eq | ne | lt | le | gt | ge
inductive ConvKind | widen | as | asUnchecked

/-- Reinterpret the two's-complement pattern of `x` at width `t.bits`. -/
def toBits (t : IntTy) (x : Int) : BitVec t.bits := BitVec.ofInt t.bits x

/-- Read a bit pattern back at the signedness of `t`. -/
def ofBits (t : IntTy) (v : BitVec t.bits) : Int :=
  if t.signed then v.toInt else (v.toNat : Int)

/-- A result of an operation that wraps for unsigned types and for signed
types in release, and aborts with `intOverflow` for signed types in debug. -/
def checked (p : NumProfile) (t : IntTy) (r : Int) : Except NumAbort Int :=
  if t.inRange r then .ok r
  else if t.signed && p == .debug then .error .intOverflow
  else .ok (wrap t r)

def evalUn (p : NumProfile) (op : UnOp) (t : IntTy) (a : Int) : Except NumAbort Int :=
  match op with
  | .neg => checked p t (-a)
  | .bitnot => .ok (ofBits t (~~~ toBits t a))

def evalBin (p : NumProfile) (op : BinOp) (t : IntTy) (a b : Int) : Except NumAbort Int :=
  match op with
  | .add => checked p t (a + b)
  | .sub => checked p t (a - b)
  | .mul => checked p t (a * b)
  | .div =>
    if b = 0 then .error .divZero
    else
      let r := Int.tdiv a b
      if t.inRange r then .ok r
      else if t == .i64 then .error .divOverflow
      else checked p t r
  | .mod => if b = 0 then .error .divZero else .ok (a % b)
  | .bitand => .ok (ofBits t (toBits t a &&& toBits t b))
  | .bitor => .ok (ofBits t (toBits t a ||| toBits t b))
  | .bitxor => .ok (ofBits t (toBits t a ^^^ toBits t b))
  | .shl => .ok (wrap t (a * (2 : Int) ^ (b % (t.bits : Int)).toNat))
  | .shr => .ok (a >>> (b % (t.bits : Int)).toNat)

def evalCmp (op : CmpOp) (a b : Int) : Bool :=
  match op with
  | .eq => decide (a = b)
  | .ne => decide (a ≠ b)
  | .lt => decide (a < b)
  | .le => decide (a ≤ b)
  | .gt => decide (a > b)
  | .ge => decide (a ≥ b)

def evalConv (p : NumProfile) (k : ConvKind) (_src dst : IntTy) (a : Int) :
    Except NumAbort Int :=
  match k with
  | .widen => .ok a
  | .as =>
    if dst.inRange a then .ok a
    else match p with
      | .debug => .error .castRange
      | .release => .ok (wrap dst a)
  | .asUnchecked => .ok (wrap dst a)

end Goose.Core
