import Goose.Construct.GIR.Syntax



namespace Goose.Construct.GIR

open Goose.Core (Mutability VarKind IntTy Request ConstructionRequest)


structure TyEnv where
  slots : Array Slot
  
  globals : Array (Ty × VarKind)
  
  sigs : Array (List Ty × List ResultDescriptor)
  vals : Array (Option VTy)
  structs : Array StructDef := #[]
  
  results : List ResultDescriptor := []
  targets : Array (List ResultDescriptor) := #[]
  
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
  | _ => tyErr s!"value %{v} is not ordinary data"

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

private def addressMutability (kind : VarKind) (ty : Ty) : Mutability :=
  match ty with
  | .grow _ => .mutable
  | .growshrink _ => .mutable
  | _ => Mutability.ofKind kind

def TyEnv.boundTy (env : TyEnv) : Bnd → TyR Unit
  | .omitted => pure ()
  | .val v | .fromEnd v => do let _ ← env.intTy v


def arrayElem? : Ty → Option Ty
  | .arr e _ | .varr e | .grow e | .growshrink e | .limited e _ => some e
  | _ => none

def carrierType (result : ResultDescriptor) : VTy :=
  match result.request with
  | .register => .data result.ty
  | .value => .built result.ty .value
  | .elementRun => .built result.ty .elementRun

def destinationType? (result : ResultDescriptor) : Option VTy :=
  match result.request with
  | .register => none
  | .value => some (.dest result.ty .value)
  | .elementRun => some (.dest result.ty .elementRun)

def resultPack (results : List ResultDescriptor) : VTy :=
  match results with
  | [] => .data .unit
  | [r] => carrierType r
  | rs => .pack rs

def TyEnv.checkCall (env : TyEnv) (callee : FnId) (args destinations : List ValueId) : TyR (List ResultDescriptor) := do
  let some (params, results) := env.sigs[callee]? | tyErr "callee outside function table"
  unless params.length == args.length do tyErr "call source argument count mismatch"
  for (param, arg) in params.zip args do
    let actual ← env.dataTy arg
    let expected := if param.nonfixed then Ty.ref .mutable param else param
    unless actual.passesTo expected do tyErr "call source argument type mismatch"
  let expected := results.filterMap destinationType?
  unless expected.length == destinations.length do tyErr "call result destination count mismatch"
  for (expected, arg) in expected.zip destinations do
    unless (← env.valTy arg) == expected do tyErr "call destination type/request mismatch"
  pure results

def TyEnv.destTy (env : TyEnv) (v : ValueId) : TyR (Ty × ConstructionRequest) := do
  match ← env.valTy v with
  | .dest t r => pure (t,r)
  | _ => tyErr "expected open destination"

def TyEnv.builtTy (env : TyEnv) (v : ValueId) : TyR (Ty × ConstructionRequest) := do
  match ← env.valTy v with
  | .built t r => pure (t,r)
  | _ => tyErr "expected completion carrier"

def TyEnv.namedResult (env : TyEnv) (slot : SlotId) : TyR ResultDescriptor :=
  match env.results.find? (fun result => result.namedLocal == some slot) with
  | some r => pure r
  | none => tyErr "slot is not a named result alias"

def TyEnv.resultDestination (_env : TyEnv) (results : List ResultDescriptor) (position : Nat) : TyR VTy := do
  let some descriptor := results[position]? | tyErr "result position outside descriptors"
  let some ty := destinationType? descriptor | tyErr "result has no construction destination"
  pure ty

def Op.resultTy (env : TyEnv) : Op → TyR VTy
  | .bytes _ _ => pure (.data (.slice .readOnly (.int .u8)))
  | .result pack position => do
    let .pack results ← env.valTy pack | tyErr "result projection requires result pack"
    let some descriptor := results[position]? | tyErr "result projection position outside pack"
    pure (carrierType descriptor)
  | .destOpen receiver logical request count _ => do
    unless logical.nonfixed && logical.constructible do tyErr "destination logical type must be constructible nonfixed"
    if let some count := count then let _ ← env.intTy count
    let (receiving, expectedRequest) ← match receiver with
      | .slot slot => do
          let some slot := env.slots[slot]? | tyErr "destination slot outside table"
          pure (slot.ty, ConstructionRequest.value)
      | .global global => do
          let some (ty, _) := env.globals[global]? | tyErr "destination global outside table"
          pure (ty, ConstructionRequest.value)
      | .arg callee position => do
          let some (params, _) := env.sigs[callee]? | tyErr "argument destination callee outside table"
          let some ty := params[position]? | tyErr "argument destination position outside signature"
          unless ty.nonfixed do tyErr "argument destination requires nonfixed parameter"
          pure (ty, ConstructionRequest.value)
      | .push reference => do
          let (_, owner) ← env.refTy reference
          unless owner.growing do tyErr "push receiver does not grow"
          let some element := owner.element? | tyErr "push receiver has no element"
          pure (element, ConstructionRequest.value)
      | .append reference => do
          let (_, owner) ← env.refTy reference
          unless owner.growing do tyErr "append receiver does not grow"
          pure (owner, ConstructionRequest.elementRun)
      | .whole reference => do
          let (_, owner) ← env.refTy reference
          unless owner.growing do tyErr "whole receiver is not resizable"
          pure (owner, ConstructionRequest.value)
    unless request == expectedRequest && logical.adaptsTo receiving do tyErr "destination receiving layout/type/request mismatch"
    pure (.dest logical request)
  | .destChild parent element _ => do
    let (ty, _) ← env.destTy parent
    unless ty.element? == some element && element.nonfixed do tyErr "destination child type mismatch"
    pure (.dest element .value)
  | .destFinish destination _ => do
    let (ty, request) ← env.destTy destination
    pure (.built ty request)
  | .destNamed slot _ => do
    let result ← env.namedResult slot
    pure (carrierType result)
  | .resultExitDest position _ => env.resultDestination env.results position
  | .targetDest target position _ => do
    let some results := env.targets[target]? | tyErr "target outside table"
    env.resultDestination results position
  | .destAbandonNamed slot replacement _ => do
    let result ← env.namedResult slot
    unless (← env.valTy replacement) == carrierType result do tyErr "named replacement result mismatch"
    let .built ty request := carrierType result | tyErr "named result must be nonfixed"
    pure (.cancelled ty request)
  | .destArg built _ => do
    let (ty, request) ← env.builtTy built
    unless request == .value do tyErr "constructed source argument must be a value"
    pure (.data (.ref .mutable ty))
  | .destAbandon carrier _ => do
    match ← env.valTy carrier with
    | .dest ty request | .built ty request => pure (.cancelled ty request)
    | _ => tyErr "abandon requires destination or completion"
  | .destValue destination _ => do
    let (ty, request) ← env.destTy destination
    unless request == .elementRun do tyErr "dest_value requires element_run"
    pure (.dest ty .value)
  | .destRelocate built reason _ => do
    let (ty, request) ← env.builtTy built
    if reason == .headerRemoval then
      unless request == .value do tyErr "header removal requires value completion"
      pure (.built ty .elementRun)
    else pure (.built ty request)
  | .destStage destination _ => do
    let (ty, request) ← env.destTy destination
    pure (.dest ty request)
  | .destFit built _ => do
    let (ty, request) ← env.builtTy built
    pure (.built ty request)
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
    | some sl => pure (.data (.ref (addressMutability sl.kind sl.ty) sl.ty))
    | none => tyErr s!"slot {s} outside the slot table"
  | .globalAddr g =>
    match env.globals[g]? with
    | some (t, k) => pure (.data (.ref (addressMutability k t) t))
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
    if t.nonfixed then tyErr "nonfixed load would detach storage"
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
    match t.element? with
    | some e =>
      unless e.flat do tyErr "nonfixed push requires destination protocol"
      unless (← env.dataTy v) = e do tyErr "a pushed element of another type than the array's"
      pure (.data (.ref .mutable e))
    | none => tyErr "push to a reference that does not point at an owner array"
  | .pop r _ => do
    let (_, t) ← env.refTy r
    unless t matches .growshrink _ | .limited .. do tyErr "pop requires shrinkable owner"
    match t.element? with
    | some e => pure (.data e)
    | none => tyErr "pop from a reference that does not point at an owner array"
  | .call f args _ => do
    let results ← env.checkCall f args []
    unless results.all (fun r => r.request == .register) do tyErr "nonfixed results require call_construct"
    pure (resultPack results)
  | .callConstruct f args destinations _ => do
    let results ← env.checkCall f args destinations
    unless results.any (fun r => r.request != .register) do tyErr "call_construct requires nonfixed result"
    pure (resultPack results)
  | .arrLit t vs => do
    if t.nonfixed then tyErr "nonfixed literals require receiving destination"
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

end Goose.Construct.GIR

namespace Goose.Construct.GIR

open Goose.Core (Mutability VarKind IntTy Request ConstructionRequest)


private def Module.baseTyEnv (m : Module) (f : Func) : TyEnv :=
  { slots := f.slots
    globals := m.globals.map fun g => (g.ty, g.kind)
    sigs := m.funcs.map fun h => (h.params, h.results)
    vals := #[]
    structs := m.structs
    results := f.results
    targets := m.targets.map fun target => (m.funcs[target.first]?).map (·.results) |>.getD [] }


def Func.permissions (m : Module) (f : Func) (vt : Array (Option VTy)) : Array (Bool × Bool) := Id.run do
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
            | .globalAddr g => match m.globals[g]? with
              | some gl => (gl.kind == .mutable, true)
              | none => (false, false)
            | .refFreeze _ => (false, false)
            | .fieldAddr owner field =>
              match vt[owner]? with
              | some (some (.data (.ref _ (.structT sid _)))) =>
                match (m.structs[sid]?).bind (fun d => d.fields[field]?) with
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


def Module.tyEnv (m : Module) (f : Func) : TyEnv :=
  let vals := f.valueTypes m
  let caps := f.permissions m vals
  { m.baseTyEnv f with contentsWritable := fun v => caps[v]?.map (·.2) }

end Goose.Construct.GIR
