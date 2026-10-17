import Goose.GIR.Syntax

/-!
The type of the value each GIR-H instruction defines, from the types of its
operands. The validator uses it to check operand types and the lowering uses it
to give every block parameter and every join a type, so the two cannot disagree
about what an instruction yields.

Storage capabilities are checked separately: field reference types retain the
declared binding permission, while the storage check intersects it with owner
provenance. A declaration cannot grant writes through a read-only borrow.
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
  structs : Array StructDef := #[]
  /-- The profile controls whether a resizable owner can be mutably borrowed
  through its contents even when its variable binding is immutable. -/
  profile : ArtifactProfile := .pilot
  /-- An absent capability is used only by standalone typing environments. -/
  contentsWritable : ValueId → Option Bool := fun _ => none

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

private def addressMutability (profile : ArtifactProfile) (kind : VarKind) (ty : Ty) : Mutability :=
  match ty with
  | .grow _ => .mutable
  | .growshrink _ => if profile == .shrink then .mutable else Mutability.ofKind kind
  | _ => Mutability.ofKind kind

def TyEnv.boundTy (env : TyEnv) : Bnd → TyR Unit
  | .omitted => pure ()
  | .val v | .fromEnd v => do let _ ← env.intTy v

/-- The array element type a reference to an array points at. -/
def arrayElem? : Ty → Option Ty
  | .arr e _ | .grow e | .growshrink e | .limited e _ => some e
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
    | some sl => pure (.data (.ref (addressMutability env.profile sl.kind sl.ty) sl.ty))
    | none => tyErr s!"slot {s} outside the slot table"
  | .globalAddr g =>
    match env.globals[g]? with
    | some (t, k) => pure (.data (.ref (addressMutability env.profile k t) t))
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
    | some e =>
      let writable := (env.contentsWritable r).getD (mode == .owner || m == .mutable)
      pure (.view (if writable then .mutable else .readOnly) e)
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
  | .indexChecked v i _ | .indexProven v i => do
    let (m, e) ← env.viewTy v
    let _ ← env.intTy i
    pure (.data (.ref m e))
  | .push r v _ => do
    let (_, t) ← env.refTy r
    match t.ownerElem? with
    | some e =>
      unless (← env.dataTy v) = e do tyErr "a pushed element of another type than the array's"
      pure (.data (.ref .mutable e))
    | none => tyErr "push to a reference that does not point at an owner array"
  | .pop r _ => do
    let (_, t) ← env.refTy r
    match t.ownerElem? with
    | some e => pure (.data e)
    | none => tyErr "pop from a reference that does not point at an owner array"
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
    | .grow e | .growshrink e =>
      for v in vs do
        unless (← env.dataTy v) = e do tyErr "array element of another type than the array's"
      pure (.data t)
    | .limited e capacity =>
      unless vs.length ≤ capacity do tyErr "limited array literal exceeds its capacity"
      for v in vs do
        unless (← env.dataTy v) = e do tyErr "array element of another type than the array's"
      pure (.data t)
    | _ => tyErr "array literal of a type that is not an array"
  | .structLit t vs => do
    let .structT sid fs := t | tyErr "struct constructor of another type"
    let some d := env.structs[sid]? | tyErr "struct id outside descriptor table"
    unless fs == TyList.ofList (d.fields.toList.map (·.ty)) do tyErr "nominal struct payload differs from descriptor"
    unless vs.length == d.fields.size do tyErr "struct initializer count differs from fields"
    for (v, f) in vs.zip d.fields.toList do
      unless (← env.dataTy v) == f.ty do tyErr "struct initializer has another field type"
    pure (.data t)
  | .fieldAddr owner i => do
    let (_, t) ← env.refTy owner
    let .structT sid fs := t | tyErr "field selection of another type"
    let some d := env.structs[sid]? | tyErr "struct id outside descriptor table"
    unless fs == TyList.ofList (d.fields.toList.map (·.ty)) do tyErr "nominal struct payload differs from descriptor"
    let some f := d.fields[i]? | tyErr "field index outside descriptor"
    pure (.data (.ref (Mutability.ofKind f.binding) f.ty))
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
private def Module.baseTyEnv (m : Module) (f : Func) : TyEnv :=
  { slots := f.slots
    globals := m.globals.map fun g => (g.ty, g.kind)
    sigs := m.funcs.map fun h => (h.params, h.results)
    vals := #[]
    structs := m.structs
    profile := m.profile }

/-- Binding and contents capabilities are intersected over every incoming CFG
edge. Starting at the top permits owned references through loops; entry
parameters and every defining operation constrain the descending fixed point. -/
def Func.permissionsFromTables (globalKinds : Array VarKind) (structs : Array StructDef)
    (f : Func) (vt : Array (Option VTy)) : Array (Bool × Bool) := Id.run do
  let typed (v : ValueId) : Bool × Bool := match vt[v]? with
    | some (some (.data (.ref mu _))) => (mu == .mutable, mu == .mutable)
    | some (some (.view mu _)) => (mu == .mutable, mu == .mutable)
    | _ => (false, false)
  let capAt (caps : Array (Bool × Bool)) (v : ValueId) := caps[v]?.getD (false, false)
  let meet (a b : Bool × Bool) := (a.1 && b.1, a.2 && b.2)
  let start := Array.replicate f.numValues (true, true)
  let round (caps : Array (Bool × Bool)) := Id.run do
    let mut next := caps
    if let some entry := f.blocks[0]? then
      for (v, _) in entry.params do next := next.set! v (meet (capAt next v) (typed v))
    for b in f.blocks do
      for i in b.insts do
        match i with
        | .def v op =>
          let c := match op with
            | .slotAddr s => match f.slots[s]? with
              | some sl => (sl.kind == .mutable, true)
              | none => (false, false)
            | .globalAddr g => match globalKinds[g]? with
              | some kind => (kind == .mutable, true)
              | none => (false, false)
            | .refFreeze _ => (false, false)
            | .fieldAddr owner field =>
              match vt[owner]? with
              | some (some (.data (.ref _ (.structT sid _)))) =>
                match (structs[sid]?).bind (fun d => d.fields[field]?) with
                | some fd => ((capAt caps owner).2 && fd.binding == .mutable,
                    (capAt caps owner).2 && fd.contents == .mutable)
                | none => (false, false)
              | _ => (false, false)
            | .snapshot _ owner =>
              let writable := (capAt caps owner).2
              (writable, writable)
            | .refElem owner _ | .indexChecked owner _ _ | .indexProven owner _ =>
              ((capAt caps owner).2, (capAt caps owner).2)
            | _ => typed v
          next := next.set! v (meet (capAt next v) c)
        | .term term =>
          let edges := match term with
            | .br target args => [(target, args)]
            | .condbr _ t ta e ea => [(t, ta), (e, ea)]
            | _ => []
          for (target, args) in edges do
            if let some dest := f.blocks[target]? then
              for ((v, _), arg) in dest.params.zip args do
                next := next.set! v (meet (capAt next v) (capAt caps arg))
        | _ => pure ()
    return next
  let rec fix : Nat → Array (Bool × Bool) → Array (Bool × Bool)
    | 0, _ => Array.replicate f.numValues (false, false)
    | fuel + 1, caps =>
      let next := round caps
      if next == caps then caps else fix fuel next
  return fix (2 * f.numValues + 2) start

def Func.permissions (m : Module) (f : Func) (vt : Array (Option VTy)) : Array (Bool × Bool) :=
  f.permissionsFromTables (m.globals.map (·.kind)) m.structs vt

/-- The type of every value of `f`, found by typing instructions until nothing
changes, so that a value used before its definition in table order still gets a
type. Snapshot types are revisited when their owner contents capability becomes
known. A value whose type cannot be derived stays `none`. -/
def Func.valueTypes (m : Module) (f : Func) : Array (Option VTy) :=
  let base := m.baseTyEnv f
  let n := f.numValues
  let start := f.blocks.foldl (fun a b =>
    b.params.foldl (fun a (v, t) => if v < n then a.set! v (some t) else a) a)
    (Array.replicate n none)
  let step (vals : Array (Option VTy)) : Array (Option VTy) × Bool :=
    let caps := f.permissions m vals
    f.blocks.foldl (fun acc b => b.insts.foldl (fun (vals, ch) i =>
      match i with
      | .def r op =>
        if r < n then
          match op.resultTy { base with vals, contentsWritable := fun v => caps[v]?.map (·.2) } with
          | .ok t => (vals.set! r (some t), ch || vals[r]? != some (some t))
          | .error _ => (vals, ch)
        else (vals, ch)
      | _ => (vals, ch)) acc) (vals, false)
  let rec go : Nat → Array (Option VTy) → Array (Option VTy)
    | 0, vals => vals
    | k + 1, vals =>
      let (vals', ch) := step vals
      if ch then go k vals' else vals'
  go (2 * n + 2) start

/-- Function typing retains the effective contents capabilities even when a
field reference's whole-binding type is read-only. -/
def Module.tyEnv (m : Module) (f : Func) : TyEnv :=
  let vals := f.valueTypes m
  let caps := f.permissions m vals
  { m.baseTyEnv f with contentsWritable := fun v => caps[v]?.map (·.2) }

end Goose.GIR
