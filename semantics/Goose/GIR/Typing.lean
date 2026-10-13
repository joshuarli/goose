import Goose.GIR.Syntax

/-!
The type of the value each GIR-H instruction defines, from the types of its
operands. The validator uses it to check operand types and the lowering uses it
to give every block parameter and every join a type, so the two cannot disagree
about what an instruction yields.

Mutability is not checked here: an instruction that needs a mutable reference
accepts either, and the storage check rejects a read-only one.
-/

namespace Goose.GIR

open Goose.Core

/-- What typing an instruction may consult. `vals` is indexed by value id. -/
structure TyEnv where
  slots : Array Slot
  /-- Type and kind of each global. -/
  globals : Array (Ty × VarKind)
  /-- Parameter and result types of each function. -/
  sigs : Array (List Ty × List Ty)
  vals : Array (Option VTy)

abbrev TyR := Except String

def tyErr (msg : String) : TyR α := .error msg

def TyEnv.valTy (env : TyEnv) (v : ValueId) : TyR VTy :=
  match env.vals[v]? with
  | some (some t) => .ok t
  | _ => tyErr s!"value %{v} has no type"

def TyEnv.dataTy (env : TyEnv) (v : ValueId) : TyR Ty := do
  match (← env.valTy v) with
  | .data t => pure t
  | .view .. => tyErr s!"value %{v} is a view where a data value is required"

def TyEnv.intTy (env : TyEnv) (v : ValueId) : TyR IntTy := do
  match (← env.dataTy v) with
  | .int t => pure t
  | _ => tyErr s!"value %{v} is not an integer"

def TyEnv.refTy (env : TyEnv) (v : ValueId) : TyR (Mutability × Ty) := do
  match (← env.dataTy v) with
  | .ref m t => pure (m, t)
  | _ => tyErr s!"value %{v} is not a reference"

def TyEnv.viewTy (env : TyEnv) (v : ValueId) : TyR (Mutability × Ty) := do
  match (← env.valTy v) with
  | .view m t => pure (m, t)
  | _ => tyErr s!"value %{v} is not a view"

def Mutability.ofKind : VarKind → Mutability
  | .mutable => .mutable
  | .immutable => .readOnly

def TyEnv.boundTy (env : TyEnv) : Bnd → TyR Unit
  | .omitted => pure ()
  | .val v | .fromEnd v => do let _ ← env.intTy v

/-- The array element type a reference to an array points at. -/
def arrayElem? : Ty → Option Ty
  | .arr e _ => some e
  | .grow e => some e
  | _ => none

def Op.resultTy (env : TyEnv) : Op → TyR VTy
  | .constInt t n =>
    if t.inRange n then pure (.data (.int t)) else tyErr s!"constant {n} out of range for its type"
  | .constBool _ => pure (.data .bool)
  | .constUnit => pure (.data .unit)
  | .bin _ t a b _ => do
    unless (← env.intTy a) = t && (← env.intTy b) = t do tyErr "integer operation on operands of another type"
    pure (.data (.int t))
  | .un op t a _ => do
    unless (← env.intTy a) = t do tyErr "integer operation on an operand of another type"
    if (op matches .neg) && !t.signed then tyErr "negation of an unsigned integer"
    pure (.data (.int t))
  | .cmp _ t a b => do
    unless (← env.intTy a) = t && (← env.intTy b) = t do tyErr "comparison of operands of another type"
    pure (.data .bool)
  | .boolCmp op a b => do
    unless (← env.dataTy a) = .bool && (← env.dataTy b) = .bool do tyErr "boolean comparison of non-booleans"
    unless op matches .eq | .ne do tyErr "booleans are only compared for equality"
    pure (.data .bool)
  | .boolNot a => do
    unless (← env.dataTy a) = .bool do tyErr "boolean not of a non-boolean"
    pure (.data .bool)
  | .conv k src dst a _ => do
    unless (← env.intTy a) = src do tyErr "conversion of an operand of another type"
    if k matches .widen then
      unless dst.minVal ≤ src.minVal ∧ src.maxVal ≤ dst.maxVal do
        tyErr "a widening that does not preserve every value"
    pure (.data (.int dst))
  | .next t a => do
    unless (← env.intTy a) = t do tyErr "increment of an operand of another type"
    pure (.data (.int t))
  | .slotAddr s =>
    match env.slots[s]? with
    | some sl => pure (.data (.ref (Mutability.ofKind sl.kind) sl.ty))
    | none => tyErr s!"slot {s} outside the slot table"
  | .globalAddr g =>
    match env.globals[g]? with
    | some (t, k) => pure (.data (.ref (Mutability.ofKind k) t))
    | none => tyErr s!"global {g} outside the global table"
  | .refElem v i => do
    let (m, t) ← env.viewTy v
    let _ ← env.intTy i
    pure (.data (.ref m t))
  | .refFreeze r => do
    let (_, t) ← env.refTy r
    pure (.data (.ref .readOnly t))
  | .load r => do
    let (_, t) ← env.refTy r
    pure (.data t)
  | .snapshot mode r => do
    let (m, t) ← env.refTy r
    match arrayElem? t with
    | some e => pure (.view (if mode == .owner then .mutable else m) e)
    | none => tyErr "snapshot of a reference to something that is not an array"
  | .sliceView s => do
    match (← env.dataTy s) with
    | .slice m e => pure (.view m e)
    | _ => tyErr "view of a value that is not a slice"
  | .viewLen v => do
    let _ ← env.viewTy v
    pure (.data (.int .i64))
  | .viewSlice m v lo hi _ => do
    let (vm, e) ← env.viewTy v
    unless vm.atLeast m do tyErr "a mutable slice of a read-only view"
    env.boundTy lo
    env.boundTy hi
    pure (.data (.slice m e))
  | .arrayLen r => do
    let (_, t) ← env.refTy r
    if (arrayElem? t).isSome then pure (.data (.int .i64))
    else tyErr "length of a reference to something that is not an array"
  | .indexChecked v i _ => do
    let (m, e) ← env.viewTy v
    let _ ← env.intTy i
    pure (.data (.ref m e))
  | .push r v _ => do
    let (_, t) ← env.refTy r
    match t with
    | .grow e =>
      unless (← env.dataTy v) = e do tyErr "a pushed element of another type than the array's"
      pure (.data (.ref .mutable e))
    | _ => tyErr "push to a reference that does not point at a grow-only array"
  | .call f args _ => do
    let some (ps, rs) := env.sigs[f]? | tyErr s!"call of function {f}, outside the function table"
    unless ps.length = args.length do
      tyErr s!"call of function {f} with {args.length} arguments, expected {ps.length}"
    for (p, a) in ps.zip args do
      unless (← env.dataTy a).passableTo p do tyErr s!"argument %{a} is not accepted by its parameter"
    match rs with
    | [] => pure (.data .unit)
    | [t] => pure (.data t)
    | _ => tyErr s!"function {f} has several results"
  | .arrLit t vs => do
    match t with
    | .arr e k =>
      unless vs.length = k do tyErr s!"array literal of {vs.length} elements for a type of {k}"
      for v in vs do
        unless (← env.dataTy v) = e do tyErr "array element of another type than the array's"
      pure (.data t)
    | .grow e =>
      for v in vs do
        unless (← env.dataTy v) = e do tyErr "array element of another type than the array's"
      pure (.data t)
    | _ => tyErr "array literal of a type that is not an array"
  | .arrFill t v => do
    match t with
    | .arr e _ =>
      unless (← env.dataTy v) = e do tyErr "fill value of another type than the elements"
      pure (.data t)
    | _ => tyErr "fill of a type that is not a fixed array"

end Goose.GIR

namespace Goose.GIR

open Goose.Core

/-- The typing environment of function `f` of module `m`, without value types. -/
def Module.tyEnv (m : Module) (f : Func) : TyEnv :=
  { slots := f.slots
    globals := m.globals.map fun g => (g.ty, g.kind)
    sigs := m.funcs.map fun h => (h.params, h.results)
    vals := #[] }

/-- The type of every value of `f`, found by typing instructions until nothing
changes, so that a value used before its definition in table order still gets a
type. A value whose type cannot be derived stays `none`. -/
def Func.valueTypes (m : Module) (f : Func) : Array (Option VTy) :=
  let base := m.tyEnv f
  let n := f.numValues
  let start := f.blocks.foldl (fun a b =>
    b.params.foldl (fun a (v, t) => if v < n then a.set! v (some t) else a) a)
    (Array.replicate n none)
  let step (vals : Array (Option VTy)) : Array (Option VTy) × Bool :=
    f.blocks.foldl (fun acc b => b.insts.foldl (fun (vals, ch) i =>
      match i with
      | .def r op =>
        if r < n && (vals[r]?.getD none).isNone then
          match op.resultTy { base with vals } with
          | .ok t => (vals.set! r (some t), true)
          | .error _ => (vals, ch)
        else (vals, ch)
      | _ => (vals, ch)) acc) (vals, false)
  let rec go : Nat → Array (Option VTy) → Array (Option VTy)
    | 0, vals => vals
    | k + 1, vals =>
      let (vals', ch) := step vals
      if ch then go k vals' else vals'
  go (n + 1) start

end Goose.GIR
