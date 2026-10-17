import Goose.GIR.Effects
import Goose.GIR.Evidence
import Goose.Core.Demand

/-!
`validate` for GIR-H: the checks that stand between an exported or lowered
module and the interpreter, run in the order of their codes. A module is judged
by the first code at which any function fails, so a module that fails a later
check is known to pass every earlier one.

| Code | Checks |
|---|---|
| `GIR-V001` | entry, global initializers, symbol and value-id tables, summaries' targets |
| `GIR-V010` | operand and result types, arity |
| `GIR-V020` | one terminator per block, edge arguments, reachability, dominance |
| `GIR-V030` | slot addresses inside their scope, stores through mutable references, loadable and storable types |
| `GIR-V040` | scope enter and leave balance on every path and nest as the scope tree; `ret` with no scope entered |
| `GIR-V050` | summaries closed over the body |
| `GIR-V060` | whole-owner replacement starts from proven empty storage |
| `GIR-V080` | every proven index follows from its fact certificate |
| `GIR-V100` | origins on every operation that can abort or stands for a statement |

Acceptance does not establish that references stay valid: that is carried from
Core by the lowering, and the checks here know nothing about it.
-/

namespace Goose.GIR

open Goose.Core

inductive Code
  | v001 | v010 | v020 | v030 | v040 | v050 | v060 | v080 | v100
  deriving DecidableEq, Repr

def Code.tag : Code → String
  | .v001 => "GIR-V001"
  | .v010 => "GIR-V010"
  | .v020 => "GIR-V020"
  | .v030 => "GIR-V030"
  | .v040 => "GIR-V040"
  | .v050 => "GIR-V050"
  | .v060 => "GIR-V060"
  | .v080 => "GIR-V080"
  | .v100 => "GIR-V100"

structure Violation where
  code : Code
  message : String

abbrev Check := Except Violation

def violation (c : Code) (msg : String) : Check α := .error ⟨c, msg⟩

/-- Run a check on every element of a list, stopping at the first failure. -/
def checkAll {ε : Type} (xs : List α) (f : α → Except ε Unit) : Except ε Unit :=
  match xs with
  | [] => pure ()
  | x :: rest => do
    f x
    checkAll rest f

theorem checkAll_ok {ε : Type} {xs : List α} {f : α → Except ε Unit}
    (h : checkAll xs f = .ok ()) : ∀ x ∈ xs, f x = .ok () := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    intro x hx
    simp only [checkAll] at h
    cases hf : f a with
    | error e => rw [hf] at h; simp [bind, Except.bind] at h
    | ok u =>
      rw [hf] at h
      simp only [bind, Except.bind, pure, Except.pure] at h
      rcases List.mem_cons.mp hx with rfl | hx
      · rw [hf]
      · exact ih h x hx

/-- A typing failure reported under `c`, naming the function. -/
def asCheck (c : Code) (label : String) (r : Except String α) : Check α :=
  match r with
  | .ok a => .ok a
  | .error msg => violation c s!"{label}: {msg}"

/-! ### Operations that need an origin -/

/-- The origin an operation carries, if it has the field. -/
def Op.origin : Op → Option OriginId
  | .bin _ _ _ _ o => o
  | .un _ _ _ o => o
  | .conv _ _ _ _ o => o
  | .viewSlice _ _ _ _ o => o
  | .indexChecked _ _ o => o
  | .push _ _ o => o
  | .pop _ o => o
  | .call _ _ o => o
  | _ => none

def Effect.origin : Effect → Option OriginId
  | .slotInit _ _ o => o
  | .store _ _ o => o
  | .append _ _ o => o
  | .popN _ _ o | .resize _ _ _ o | .clear _ o | .replace _ _ o => o
  | .print _ o => o
  | _ => none

def Term.origin : Term → Option OriginId
  | .ret _ o => o
  | .abort _ o => o
  | .exit _ o => o
  | _ => none

def Inst.origin : Inst → Option OriginId
  | .def _ op => op.origin
  | .eff e => e.origin
  | .term t => t.origin

def unMayAbort : UnOp → Bool
  | .neg => true
  | .bitnot => false

def convMayAbort : ConvKind → Bool
  | .as => true
  | .widen | .asUnchecked => false

/-- Instructions that can abort or that stand for a source statement must say
where they came from. -/
def Inst.needsOrigin : Inst → Bool
  | .def _ (.bin o ..) => o.mayAbort
  | .def _ (.un o ..) => unMayAbort o
  | .def _ (.conv k ..) => convMayAbort k
  | .def _ (.viewSlice ..) | .def _ (.indexChecked ..) | .def _ (.call ..) => true
  | .eff (.slotInit ..) | .eff (.store ..) | .eff (.append ..) | .eff (.print ..)
  | .eff (.popN ..) | .eff (.resize ..) | .eff (.clear ..) | .eff (.replace ..) => true
  | .def _ (.pop ..) => true
  | .term (.abort ..) | .term (.exit ..) => true
  | _ => false

/-- A shrink-profile push can abort on limited capacity and therefore needs an origin. -/
def Inst.needsOriginIn (profile : ArtifactProfile) (i : Inst) : Bool :=
  match i with
  | .def _ (.push ..) => profile == .shrink
  | _ => i.needsOrigin

/-! ### GIR-V001 -/

def checkEntryAndGlobals (m : Module) : Check Unit := do
  match m.funcs[m.entry]? with
  | none => violation .v001 s!"the entry {m.entry} is outside the function table"
  | some f =>
    unless f.params.isEmpty && f.results.isEmpty do
      violation .v001 s!"the entry {f.name} must take no parameters and return nothing"
  for g in m.globals do
    unless g.init.params.isEmpty && g.init.results == [g.ty] do
      violation .v001 s!"the initializer of global {g.name} must take no parameters and return its type"
    unless g.org < m.origins.size do violation .v001 s!"global {g.name}: origin outside the origin table"

/-- Table indices an instruction names. -/
def checkInstSymbols (m : Module) (f : Func) (n : Nat) (i : Inst) : Except String Unit := do
  for v in i.uses do
    unless v < n do throw s!"value %{v} is outside the value table of {n}"
  match i.origin with
  | some o => unless o < m.origins.size do throw s!"origin {o} is outside the origin table"
  | none => pure ()
  match i with
  | .def _ (.slotAddr s) | .eff (.slotInit s _ _) =>
    unless s < f.slots.size do throw s!"slot {s} is outside the slot table"
  | .def _ (.globalAddr g) =>
    unless g < m.globals.size do throw s!"global {g} is outside the global table"
  | .def _ (.call g _ _) =>
    unless g < m.funcs.size do throw s!"function {g} is outside the function table"
  | .eff (.enter sc) | .eff (.leave sc) =>
    unless sc < f.scopes.size do throw s!"scope {sc} is outside the scope table"
  | .term t =>
    for b in t.successors do
      unless b < f.blocks.size do throw s!"block {b} is outside the block table"
  | _ => pure ()

def checkSymbols (m : Module) (label : String) (f : Func) : Check Unit := do
  asCheck .v001 label (do
    if f.blocks.isEmpty then throw "no blocks"
    for h : i in [0:f.scopes.size] do
      match f.scopes[i] with
      | some p => unless p < i do throw s!"scope {i}: parent {p} is not an earlier scope"
      | none => pure ()
    for sl in f.slots do
      unless sl.scope < f.scopes.size do throw s!"slot of variable {sl.var}: scope {sl.scope} is outside the scope table"
    match f.org with
    | some o => unless o < m.origins.size do throw s!"function origin {o} is outside the origin table"
    | none => pure ()
    match f.summary with
    | .unknown => pure ()
    | .known s =>
      for t in s.reads ++ s.writes ++ s.grows ++ s.shrinks ++ s.rebinds do
        match t with
        | .param i => unless i < f.params.length do throw s!"summary names parameter {i}, which does not exist"
        | .global g => unless g < m.globals.size do throw s!"summary names global {g}, outside the global table"
    if !f.roots.results.isEmpty && f.roots.results.size != f.results.length then
      throw s!"root info has {f.roots.results.size} result rows, expected {f.results.length}"
    for (i, roots) in f.roots.params do
      unless i < f.params.length do throw s!"root info names parameter {i}, which does not exist"
      unless f.params[i]!.isRefLike do throw s!"root info annotates non-reference parameter {i}"
      for root in roots do
        match root with
        | .local _ => throw s!"root info for parameter {i} names a local slot"
        | .global g => unless g < m.globals.size do throw s!"root info names global {g}, outside the global table"
        | .param p => unless p == i do throw s!"root info for parameter {i} names parameter {p}"
    for (i, roots) in f.roots.contents do
      unless i < f.params.length do throw s!"content root info names parameter {i}, which does not exist"
      unless f.params[i]!.isRefSlice do throw s!"content root info annotates a parameter that is not a reference to a slice"
      for root in roots do
        match root with
        | .local _ => throw s!"content root info for parameter {i} names a local slot"
        | .global g => unless g < m.globals.size do throw s!"content root info names global {g}, outside the global table"
        | .param p => unless p < f.params.length do throw s!"content root info names parameter {p}, which does not exist"
    for roots in f.roots.results do
      for root in roots do
        match root with
        | .local x => throw s!"result root info names local slot {x}"
        | .global g => unless g < m.globals.size do throw s!"result root info names global {g}, outside the global table"
        | .param p => unless p < f.params.length do throw s!"result root info names parameter {p}, which does not exist"
    -- Value ids are dense and each is defined once.
    let n := f.numValues
    let mut seen := Array.replicate n false
    for b in f.blocks do
      for d in b.defs do
        unless d < n do throw s!"value %{d} is outside the value table of {n}"
        if seen[d]! then throw s!"value %{d} is defined twice"
        seen := seen.set! d true
      for i in b.insts do
        checkInstSymbols m f n i)

/-! ### GIR-V010 -/

def checkEffectTypes (env : TyEnv) : Effect → TyR Unit
  | .slotInit s v _ => do
    let some sl := env.slots[s]? | tyErr s!"slot {s} outside the slot table"
    unless (← env.dataTy v) = sl.ty do tyErr s!"slot {s} is initialized with a value of another type"
  | .store r v _ => do
    let (_, t) ← env.refTy r
    unless (← env.dataTy v) = t do tyErr "a store of a value of another type than the referent"
  | .append r v _ => do
    let (_, t) ← env.refTy r
    match t with
    | .grow e | .growshrink e | .limited e _ =>
      let (_, ve) ← env.viewTy v
      unless ve = e do tyErr "appended elements of another type than the array's"
    | _ => tyErr "append to a reference that does not point at an owner array"
  | .popN r count _ => do
    let (_, t) ← env.refTy r
    unless t.ownerElem?.isSome do tyErr "pop_n from a reference that does not point at an owner array"
    let _ ← env.intTy count
  | .resize r size fill _ => do
    let (_, t) ← env.refTy r
    let some e := t.ownerElem? | tyErr "resize of a reference that does not point at an owner array"
    let _ ← env.intTy size
    if let some v := fill then
      unless (← env.dataTy v) = e do tyErr "resize fill of another type than the array's"
  | .clear r _ => do
    let (_, t) ← env.refTy r
    unless t.ownerElem?.isSome do tyErr "clear of a reference that does not point at an owner array"
  | .replace r run _ => do
    let (_, t) ← env.refTy r
    unless t matches .grow _ | .growshrink _ do
      tyErr "replace of a reference that does not point at a resizable array"
    unless (← env.dataTy run) = t do tyErr "replacement run has another type than the owner"
  | .print parts _ => do
    for p in parts do
      match p with
      | .text _ => pure ()
      | .val v =>
        match (← env.dataTy v) with
        | .int _ | .bool => pure ()
        | _ => tyErr "a printed value is neither an integer nor a boolean"
  | .enter _ | .leave _ => pure ()

def checkTermTypes (f : Func) (env : TyEnv) : Term → TyR Unit
  | .condbr c .. => do
    unless (← env.dataTy c) = .bool do tyErr "a branch condition that is not a boolean"
  | .ret vs _ => do
    unless vs.length = f.results.length do tyErr s!"return of {vs.length} values, the function has {f.results.length} results"
    for (v, t) in vs.zip f.results do
      unless (← env.dataTy v) = t do tyErr "a returned value of another type than the result"
  | .exit v _ => do
    let _ ← env.intTy v
  | .br .. | .abort .. | .unreachable => pure ()

def checkInstTypes (f : Func) (env : TyEnv) (vt : Array (Option VTy)) : Inst → Except String Unit
  | .def r op => do
    let t ← op.resultTy env
    unless vt[r]? == some (some t) do throw s!"value %{r} has two types"
  | .eff e => checkEffectTypes env e
  | .term t => checkTermTypes f env t

def checkTypes (m : Module) (label : String) (f : Func) (vt : Array (Option VTy)) : Check Unit := do
  let env : TyEnv := { m.tyEnv f with vals := vt }
  asCheck .v010 label (do
    for b in f.blocks do
      for i in b.insts do
        match i with
        | .def _ (.pop ..) | .eff (.popN ..) | .eff (.resize ..)
        | .eff (.clear ..) | .eff (.replace ..) =>
          unless m.profile == .shrink do throw "operation requires core-shrink"
        | .term (.abort k _) =>
          if m.profile != .shrink && k ∈ [.popEmpty, .popNRange, .resizeNegative, .resizeFill, .capacity] then
            throw s!"abort kind {k.tag.quote} requires core-shrink"
        | _ => pure ()
    checkAll f.results fun t => do
      unless !t.isRefSlice do
        throw "a reference-to-slice type is only valid for a parameter"
    checkAll f.slots.toList.zipIdx fun (sl, index) => do
      unless sl.var == index do
        throw s!"slot {index} must describe variable {index}, found variable {sl.var}"
      let parameterRefSliceSlot :=
        sl.var < f.params.length && f.params[sl.var]? == some sl.ty && sl.ty.isRefSlice
      unless sl.ty.storable || parameterRefSliceSlot do
        throw s!"the slot of variable {sl.var} has a type no variable may have"
    checkAll f.blocks.toList fun b => checkAll b.insts (checkInstTypes f env vt)
    match f.blocks[0]? with
    | some b =>
      unless b.params.map (·.2) == f.params.map VTy.data do
        throw "the parameters of block 0 are not the function's parameters"
    | none => throw "no blocks")

/-! ### GIR-V020 -/

def predecessors (f : Func) : Array (List BlockId) :=
  let n := f.blocks.size
  (List.range n).foldl (fun acc b =>
    match f.blocks[b]? with
    | none => acc
    | some blk =>
      (blk.terms.flatMap Term.successors).foldl (fun acc t =>
        if t < n then acc.modify t (b :: ·) else acc) acc)
    (Array.replicate n [])

/-- Blocks reachable from block 0. -/
def reachable (f : Func) : Array Bool :=
  let n := f.blocks.size
  let rec go : Nat → List BlockId → Array Bool → Array Bool
    | 0, _, seen => seen
    | _, [], seen => seen
    | k + 1, b :: rest, seen =>
      let succs := match f.blocks[b]? with
        | some blk => blk.terms.flatMap Term.successors
        | none => []
      let (seen', new) := succs.foldl (fun (s, new) t =>
        if t < n && !(s[t]?.getD true) then (s.set! t true, t :: new) else (s, new)) (seen, [])
      go k (new ++ rest) seen'
  go (n + 1) [0] ((Array.replicate n false).set! 0 true)

/-- Dominator sets as bit masks over blocks, by rounds until nothing changes. -/
def dominators (f : Func) (preds : Array (List BlockId)) : Array Nat :=
  let n := f.blocks.size
  let full := (1 <<< n) - 1
  let rec go : Nat → Array Nat → Array Nat
    | 0, d => d
    | k + 1, d =>
      let (d', ch) := (List.range n).foldl (fun (d, ch) b =>
        if b = 0 then (d, ch)
        else
          let inter := (preds[b]?.getD []).foldl (fun acc p => acc &&& (d[p]?.getD 0)) full
          let nd := inter ||| (1 <<< b)
          if nd != (d[b]?.getD 0) then (d.set! b nd, true) else (d, ch)) (d, false)
      if ch then go k d' else d'
  go (n + 2) ((Array.replicate n full).set! 0 1)

def checkCfg (label : String) (f : Func) (vt : Array (Option VTy)) : Check Unit := do
  let n := f.blocks.size
  checkAll f.blocks.toList.zipIdx fun (blk, b) => do
    let terms := blk.terms
    unless terms.length = 1 do
      violation .v020 s!"{label}: block {b} has {terms.length} terminators, expected one"
    if blk.lastTerm?.isNone then violation .v020 s!"{label}: block {b} does not end in its terminator"
  -- Edge arguments against the parameters of the target.
  let edgeOk (b : BlockId) (t : BlockId) (args : List ValueId) : Check Unit := do
    let some tb := f.blocks[t]? | violation .v020 s!"{label}: block {b} branches outside the block table"
    unless tb.params.length = args.length do
      violation .v020 s!"{label}: the branch from block {b} to block {t} passes {args.length} arguments for {tb.params.length} parameters"
    for (p, a) in tb.params.zip args do
      unless vt[a]? == some (some p.2) do
        violation .v020 s!"{label}: argument %{a} of the branch from block {b} to block {t} has another type than parameter %{p.1}"
  for h : b in [0:n] do
    match f.blocks[b].lastTerm? with
    | some (.br t args) => edgeOk b t args
    | some (.condbr _ t ta e ea) => do edgeOk b t ta; edgeOk b e ea
    | _ => pure ()
  let preds := predecessors f
  unless (preds[0]?.getD []).isEmpty do
    violation .v020 s!"{label}: the entry block has predecessors"
  let seen := reachable f
  for h : b in [0:n] do
    unless seen[b]? == some true do violation .v020 s!"{label}: block {b} is not reachable from the entry"
  -- Definitions dominate uses.
  let dom := dominators f preds
  let defAt := f.blocks.zipIdx.foldl (fun (acc : Array (Option (BlockId × Int))) (blk, b) =>
    let acc := blk.params.foldl (fun acc (v, _) => acc.set! v (some (b, -1))) acc
    (blk.insts.zipIdx).foldl (fun acc (i, k) =>
      match i with
      | .def r _ => acc.set! r (some (b, (k : Int)))
      | _ => acc) acc) (Array.replicate f.numValues none)
  for h : u in [0:n] do
    for (i, k) in (f.blocks[u].insts).zipIdx do
      for v in i.uses do
        match defAt[v]? with
        | some (some (db, dk)) =>
          let ok := if db = u then decide (dk < (k : Int)) else (dom[u]?.getD 0).testBit db
          unless ok do
            violation .v020 s!"{label}: value %{v} is used in block {u} where its definition in block {db} does not dominate the use"
        | _ => violation .v020 s!"{label}: value %{v} has no definition"

inductive ReturnFlow
  | returns
  | stops
  | branches (targets : List BlockId)

/-- A reached unreachable term is unknown for this analysis. It cannot be used
as evidence that the containing function cannot return. -/
def blockReturnFlow (mayReturn : Array Bool) : List Inst → ReturnFlow
  | [] => .returns
  | .def _ (.call g ..) :: rest =>
    if mayReturn[g]?.getD true then blockReturnFlow mayReturn rest else .stops
  | .term (.ret ..) :: _ => .returns
  | .term (.br b ..) :: _ => .branches [b]
  | .term (.condbr _ t _ e _) :: _ => .branches [t, e]
  | .term (.abort ..) :: _ | .term (.exit ..) :: _ => .stops
  | .term .unreachable :: _ => .returns
  | _ :: rest => blockReturnFlow mayReturn rest

/-- Whether a function has a path to `ret` when calls to proven nonreturning
functions stop execution. The finite worklist is conservative on exhaustion. -/
def funcMayReturn (mayReturn : Array Bool) (f : Func) : Bool := Id.run do
  let rec walk : Nat → List BlockId → Array Bool → Bool
    | 0, _, _ => true
    | fuel + 1, [], _ => false
    | fuel + 1, b :: todo, seen =>
      if seen[b]?.getD false then walk (fuel + 1) todo seen
      else
        let seen := seen.set! b true
        match f.blocks[b]? with
        | none => true
        | some block =>
          match blockReturnFlow mayReturn block.insts with
          | .returns => true
          | .stops => walk fuel todo seen
          | .branches targets => walk fuel (targets ++ todo) seen
  termination_by fuel todo _ => (fuel, todo.length)
  return walk (f.blocks.size + 1) [0] (Array.replicate f.blocks.size false)

/-- Functions with finite returning-call derivations. Exhaustion conservatively
marks every function as potentially returning. -/
def Module.functionsMayReturn (m : Module) : Array Bool := Id.run do
  let conservative := Array.replicate m.funcs.size true
  let rec fix : Nat → Array Bool → Array Bool
    | 0, _ => conservative
    | fuel + 1, current =>
      let next := m.funcs.map (funcMayReturn current)
      if next == current then current else fix fuel next
  return fix (m.funcs.size + 1) (Array.replicate m.funcs.size false)

/-- `unreachable` must immediately follow a call whose body proves it has no
normal return path. -/
def checkUnreachableOf (mayReturn : Array Bool) (label : String) (f : Func) : Check Unit := do
  for block in f.blocks do
    for h : i in [0:block.insts.length] do
      match block.insts[i] with
      | .term .unreachable =>
        match (block.insts.take i).getLast? with
        | some (.def _ (.call g ..)) =>
          if mayReturn[g]?.getD true then
            violation .v020 s!"{label}: unreachable does not immediately follow a call to a function that cannot return"
        | _ =>
          violation .v020 s!"{label}: unreachable does not immediately follow a call to a function that cannot return"
      | _ => pure ()

/-! ### GIR-V030 and GIR-V040 -/

/-- The first problem of each kind found while following the scopes entered
along every path from the entry. -/
structure ScopeWalk where
  storage : Option String := none
  scopes : Option String := none
  /-- Two paths arrive at a block with different scopes entered; reported before
  the other scope problems, which it usually causes. -/
  join : Option String := none

def ScopeWalk.noteStorage (w : ScopeWalk) (msg : String) : ScopeWalk :=
  if w.storage.isNone then { w with storage := some msg } else w

def ScopeWalk.noteScopes (w : ScopeWalk) (msg : String) : ScopeWalk :=
  if w.scopes.isNone then { w with scopes := some msg } else w

/-- Follow one block from the scopes entered on arrival; yields the scopes
entered at its end. -/
def ScopeWalk.noteJoin (w : ScopeWalk) (msg : String) : ScopeWalk :=
  if w.join.isNone then { w with join := some msg } else w

def walkBlock (f : Func) (b : BlockId) (blk : Block) (start : List ScopeId) (w : ScopeWalk) :
    List ScopeId × ScopeWalk :=
  let slotIn (s : SlotId) (stack : List ScopeId) (w : ScopeWalk) : ScopeWalk :=
    match f.slots[s]? with
    | some sl =>
      if stack.contains sl.scope then w
      else w.noteStorage s!"block {b}: the address of slot {s} is taken outside scope {sl.scope}"
    | none => w
  blk.insts.foldl (fun (stack, w) i =>
    match i with
    | .def _ (.slotAddr s) => (stack, slotIn s stack w)
    | .eff (.slotInit s _ _) => (stack, slotIn s stack w)
    | .eff (.enter sc) =>
      let parent := f.scopes[sc]?.getD none
      let ok := match parent, stack with
        | some p, q :: _ => decide (p = q)
        | none, [] => true
        | _, _ => false
      let w := if ok then w
        else w.noteScopes s!"block {b}: scope {sc} is entered where its parent is not the innermost scope entered"
      (sc :: stack, w)
    | .eff (.leave sc) =>
      match stack with
      | q :: rest =>
        if q = sc then (rest, w)
        else (stack, w.noteScopes s!"block {b}: scope {sc} is left but scope {q} is the innermost entered")
      | [] => (stack, w.noteScopes s!"block {b}: scope {sc} is left but none is entered")
    | .term (.ret ..) =>
      if stack.isEmpty then (stack, w)
      else (stack, w.noteScopes s!"block {b}: return with scope {stack.head!} still entered")
    | _ => (stack, w)) (start, w)

def walkScopes (label : String) (f : Func) : ScopeWalk :=
  let n := f.blocks.size
  let rec go : Nat → List BlockId → Array (Option (List ScopeId)) → ScopeWalk → ScopeWalk
    | 0, _, _, w => w
    | _, [], _, w => w
    | k + 1, b :: rest, entry, w =>
      match f.blocks[b]?, entry[b]? with
      | some blk, some (some st) =>
        let (out, w) := walkBlock f b blk st w
        let (entry, rest, w) := (blk.terms.flatMap Term.successors).foldl (fun (entry, rest, w) t =>
          match entry[t]? with
          | some none => (entry.set! t (some out), t :: rest, w)
          | some (some st') =>
            if st' == out then (entry, rest, w)
            else (entry, rest, w.noteJoin s!"block {t} is reached with different scopes entered")
          | none => (entry, rest, w)) (entry, rest, w)
        go k rest entry w
      | _, _ => go k rest entry w
  let w := go (n + 1) [0] ((Array.replicate n none).set! 0 (some [])) {}
  { storage := w.storage.map (s!"{label}: " ++ ·),
    scopes := (w.join <|> w.scopes).map (s!"{label}: " ++ ·) }

/-- Loads and stores of the right kind of storage, through the right kind of reference. -/
def checkStorage (m : Module) (label : String) (f : Func) (vt : Array (Option VTy)) : Check Unit := do
  let refOf (v : ValueId) : Option (Mutability × Ty) :=
    match vt[v]? with
    | some (some (.data (.ref m t))) => some (m, t)
    | _ => none
  for b in f.blocks do
    for i in b.insts do
      match i with
      | .def _ (.load r) =>
        match refOf r with
        | some (_, t) => unless t.readable || t.isRefSlice do
            violation .v030 s!"{label}: a load of a value that cannot be copied"
        | none => pure ()
      | .eff (.store r _ _) =>
        match refOf r with
        | some (m, t) =>
          unless m == .mutable do violation .v030 s!"{label}: a store through a read-only reference"
          unless t.readable do violation .v030 s!"{label}: a store of a value that cannot be copied"
        | none => pure ()
      | .def _ (.push r _ _) | .eff (.append r _ _) =>
        match refOf r with
        | some (mu, t) =>
          unless mu == .mutable || t.ownerElem?.isSome do
            violation .v030 s!"{label}: growth through a read-only reference"
        | none => pure ()
      | .def _ (.pop r _) | .eff (.popN r _ _) | .eff (.resize r ..)
      | .eff (.clear r _) | .eff (.replace r ..) =>
        match refOf r with
        | some (mu, t) =>
          let owner := if m.profile == .shrink then
            (match i with
            | .eff (.replace ..) => match t with
              | .grow _ | .growshrink _ => true
              | _ => false
            | _ => t.ownerElem?.isSome)
          else false
          unless mu == .mutable || owner do
            violation .v030 s!"{label}: array mutation through a read-only reference"
        | none => pure ()
      | _ => pure ()

/-- Whole stores use binding permission; projection and array writes use
contents permission. A read-only borrowed reference never gains either. -/
def checkPermissions (m : Module) (label : String) (f : Func) (vt : Array (Option VTy)) : Check Unit := do
  let caps := f.permissions m vt
  let passable (v : ValueId) (t : Ty) : Bool := match t with
    | .ref .mutable referent =>
      let c := caps[v]?.getD (false, false)
      match referent with
      | .grow _ | .growshrink _ => if m.profile == .shrink then c.1 && c.2 else c.2
      | .structT .. | .arr .. | .limited .. => c.1 && c.2
      | _ => c.1
    | _ => true
  for b in f.blocks do
    for i in b.insts do
      match i with
      | .eff (.store r v _) =>
        match vt[r]? with
        | some (some (.data (.ref _ t))) =>
          unless passable v t do violation .v030 s!"{label}: storing a mutable reference without permission"
        | _ => pure ()
        unless (caps[r]?.getD (false, false)).1 do
          violation .v030 s!"{label}: a store without whole-binding permission"
      | .def _ (.push r _ _) | .eff (.append r _ _)
      | .def _ (.pop r _) | .eff (.popN r _ _) | .eff (.resize r ..)
      | .eff (.clear r _) =>
        unless (caps[r]?.getD (false, false)).2 do
          violation .v030 s!"{label}: array mutation without contents permission"
      | .eff (.replace r _ _) =>
        let cap := caps[r]?.getD (false, false)
        unless cap.1 && cap.2 do
          violation .v030 s!"{label}: replacement without whole-owner permission"
      | .def _ (.ownerBorrow owner) =>
        unless (caps[owner]?.getD (false, false)).2 do
          violation .v030 s!"{label}: an owner borrow without contents permission"
      | .def v (.snapshot _ _) =>
        match vt[v]? with
        | some (some (.view .mutable _)) =>
          unless (caps[v]?.getD (false, false)).2 do
            violation .v030 s!"{label}: a mutable view without contents permission"
        | _ => pure ()
      | .def _ (.call fn args _) =>
        if let some callee := m.funcs[fn]? then
          for (t, arg) in callee.params.zip args do
            unless passable arg t do
              violation .v030 s!"{label}: a mutable argument without binding permission"
      | .eff (.slotInit slot v _) =>
        if let some sl := f.slots[slot]? then
          unless passable v sl.ty do
            violation .v030 s!"{label}: a mutable reference binding without permission"
      | .term (.ret vs _) =>
        for (t, v) in f.results.zip vs do
          unless passable v t do
            violation .v030 s!"{label}: a mutable reference result without permission"
      | _ => pure ()

/-- Reuse Core's nominal identity and authoritative byte-layout checks against
exactly the descriptors retained by the lowering. -/
def checkStructTypes (m : Module) : Check Unit := do
  let cm : Core.Module :=
    { files := m.files
      types := #[]
      globals := #[]
      impls := #[]
      contexts := #[]
      entry := 0
      origins := m.origins
      profile := m.profile
      structs := m.structs }
  let check (r : Core.V Unit) : Check Unit := match r with
    | .ok _ => pure ()
    | .error e => violation .v010 e.message
  check (Core.checkStructTables cm)
  for g in m.globals do check (Core.checkResolvedType cm g.ty)
  for f in m.funcs.toList ++ m.globals.toList.map (·.init) do
    for t in f.params ++ f.results ++ f.slots.toList.map (·.ty) do
      check (Core.checkResolvedType cm t)
    for b in f.blocks do
      for (_, t) in b.params do
        match t with
        | .data t | .view _ t => check (Core.checkResolvedType cm t)
      for i in b.insts do
        match i with
        | .def _ (.structLit t _) | .def _ (.arrLit t _) | .def _ (.arrFill t _) =>
          check (Core.checkResolvedType cm t)
        | .def _ (.fieldAddr ..) =>
          unless m.profile == .shrink do violation .v010 "structs require core-shrink"
        | _ => pure ()

/-! ### GIR-V050 and GIR-V100 -/

/-- Root annotations are over-approximations. Check them at every call site and
against values the body actually returns before using them for effect checks. -/
def checkRootAnnotationsOf (m : Module) (vts : Array (Array (Option VTy)))
    (res : Array (List RootRef)) (nRoots k : Nat) : Check Unit := do
  let some f := m.funcs[k]? | pure ()
  let vt := vts[k]?.getD #[]
  let p := f.provenance res vt nRoots
  let label := s!"function {f.name}"
  if !f.results.isEmpty then
    let declared := (f.roots.results[0]?).getD []
    for root in rootsAt res k do
      unless declared.contains root do
        violation .v050 s!"{label} result 0 root info omits a root returned by the body"
  for block in f.blocks do
    for inst in block.insts do
      match inst with
      | .def _ (.call g args _) =>
        let some callee := m.funcs[g]? | pure ()
        let calleeLabel := s!"function {callee.name}"
        for h : j in [0:callee.params.length] do
          if callee.params[j].isRefLike then
            let expected := mapArgumentRoots f p args[j]! j
            let declared := (callee.roots.params.find? (·.1 == j)).map (·.2) |>.getD []
            unless declared == [.param j] || expected.all declared.contains do
              violation .v050 s!"{calleeLabel} parameter {j} root info omits a root passed at a call site"
          if callee.params[j].isRefSlice then
            if let some (_, declared) := callee.roots.contents.find? (·.1 == j) then
              let actual := argumentContents f p args[j]!
              let mapped := mapContentRoots f p args declared
              unless actual.all mapped.contains do
                violation .v050 s!"{calleeLabel} content root info for parameter {j} omits a root passed at a call site"
      | .def result (.load address) =>
        match vt[result]? with
        | some (some (.data (.slice ..))) =>
          for root in rootsAt p.vals address do
            if let .param parameter := root then
              if (f.params[parameter]?).any Ty.isRefSlice &&
                  (f.roots.contents.find? (·.1 == parameter)).isNone then
                violation .v050 s!"{label} reads slice contents through parameter {parameter} without content root info"
        | _ => pure ()
      | _ => pure ()

def checkRootAnnotations (m : Module) (vts : Array (Array (Option VTy)))
    (res : Array (List RootRef)) (nRoots : Nat) : Check Unit :=
  checkAll (List.range m.funcs.size) (checkRootAnnotationsOf m vts res nRoots)

def checkOrigin (profile : ArtifactProfile) (label : String) (i : Inst) : Check Unit :=
  if i.needsOriginIn profile && i.origin.isNone then
    violation .v100 s!"{label}: an operation that can abort or stands for a statement has no origin"
  else pure ()

def checkOrigins (profile : ArtifactProfile) (label : String) (f : Func) : Check Unit :=
  checkAll f.blocks.toList fun b => checkAll b.insts (checkOrigin profile label)

/-! ### GIR-V060 -/

def edgeArgsTo (t : Term) (target : BlockId) : List (List ValueId) :=
  match t with
  | .br b args => if b == target then [args] else []
  | .condbr _ tb ta eb ea => (if tb == target then [ta] else []) ++ (if eb == target then [ea] else [])
  | _ => []

def termEdges : Term → List (BlockId × List ValueId)
  | .br target args => [(target, args)]
  | .condbr _ thenBlock thenArgs elseBlock elseArgs =>
    [(thenBlock, thenArgs), (elseBlock, elseArgs)]
  | _ => []

def incomingValues (f : Func) (target : BlockId) (param : Nat) : List ValueId :=
  f.blocks.toList.flatMap fun b =>
    match b.lastTerm? with
    | some term => (edgeArgsTo term target).filterMap (·[param]?)
    | none => []

def isLiteralRunType : Ty → Bool
  | .grow _ | .growshrink _ => true
  | _ => false

def freshRunRound (f : Func) (valid : Array Bool) : Array Bool × Bool := Id.run do
  let mut valid := valid
  let mut changed := false
  for h : target in [0:f.blocks.size] do
    for ((v, _), param) in f.blocks[target].params.zipIdx do
      let incoming := incomingValues f target param
      if !valid[v]! && !incoming.isEmpty && incoming.all (fun source => valid[source]?.getD false) then
        valid := valid.set! v true
        changed := true
  return (valid, changed)

def literalRunSeeds (f : Func) (vt : Array (Option VTy)) : Array Bool := Id.run do
  let mut valid := Array.replicate f.numValues false
  for b in f.blocks do
    for i in b.insts do
      match i with
      | .def r (.arrLit t _) =>
        if isLiteralRunType t && vt[r]? == some (some (.data t)) then valid := valid.set! r true
      | _ => pure ()
  return valid

def freshRuns (f : Func) (vt : Array (Option VTy)) : Array Bool := Id.run do
  let mut valid := literalRunSeeds f vt
  let mut changed := true
  let mut fuel := f.numValues + 1
  while changed && fuel > 0 do
    let (next, progress) := freshRunRound f valid
    valid := next
    changed := progress
    fuel := fuel - 1
  return valid

def rootsOverlap (a b : List RootRef) : Bool :=
  a.isEmpty || b.isEmpty || a.any (fun x => b.any (Goose.Core.rootsMayOverlap x))

abbrev ReplacementRootQuery := Option (List RootRef)

structure ReplacementQueries where
  parameters : Array (Nat × List RootRef)
  values : Array (List RootRef)
  emptyValues : Array Bool

def ReplacementQueries.expand (queries : ReplacementQueries) : RootRef → List RootRef
  | .param index =>
    match queries.parameters.find? (·.1 == index) with
    | some (_, roots) => roots
    | none => [.param index]
  | root => [root]

def replacementRootsEmpty (f : Func) (roots : List RootRef) : Bool :=
  !roots.isEmpty && (roots.flatMap (ReplacementQueries.mk f.roots.params #[] #[]).expand).isEmpty

def replacementSlotEmpty (f : Func) (vt : Array (Option VTy)) (p : Prov)
    (empty : Array Bool) (slot : SlotId) : Bool :=
  let known := fun value => empty[value]?.getD false
  let instructions := f.blocks.toList.flatMap (·.insts)
  let writers := instructions.filterMap fun
    | .eff (.slotInit target value _) => if target == slot then some value else none
    | .eff (.store address value _) =>
        if (rootsAt p.vals address).contains (.local slot) then some value else none
    | _ => none
  let unknownWrite := instructions.any fun
    | .eff (.store address value _) =>
        valRefLike vt value && !known address && (rootsAt p.vals address).isEmpty
    | .def _ (.call _ args _) =>
        !(args.any fun value => valRefLike vt value && known value) &&
          args.any fun value => valRefLike vt value && !known value &&
            ((rootsAt p.vals value).isEmpty || (rootsAt p.vals value).contains (.local slot))
    | _ => false
  !writers.isEmpty && writers.all known && !unknownWrite

def replacementParameterContentsStable (m : Module) (f : Func) (vt : Array (Option VTy))
    (p : Prov) (empty : Array Bool) : Bool :=
  let known := fun value => empty[value]?.getD false
  let external := fun value =>
    !known value && ((rootsAt p.vals value).isEmpty ||
      (rootsAt p.vals value).any (fun | .local _ => false | _ => true))
  !(f.blocks.toList.flatMap (·.insts)).any fun
    | .eff (.store address value _) => valRefLike vt value && !known value && external address
    | .def _ (.call fn args _) =>
        if args.any (fun value => valRefLike vt value && known value) then false else
          match m.funcs[fn]? with
          | none => true
          | some callee =>
              match callee.summary with
              | .unknown => true
              | .known summary => (summary.writes ++ summary.rebinds).any fun
                  | .global _ => true
                  | .param parameter =>
                      match args[parameter]? with
                      | none => true
                      | some value => external value
    | _ => false

def replacementEmptyOp (f : Func) (vt : Array (Option VTy)) (p : Prov)
    (empty : Array Bool) (parameterContents : Bool) (result : ValueId) (op : Op) : Bool :=
  let known := fun value => empty[value]?.getD false
  if !valRefLike vt result || !(rootsAt p.vals result).isEmpty then false else
    match op with
    | .fieldAddr value _ | .refElem value _ | .viewSlice _ value _ _ _
    | .indexChecked value _ _ | .indexProven value _ | .refFreeze value | .ownerBorrow value
    | .sliceView value | .push value _ _ | .snapshot _ value => known value
    | .load address =>
        known address || (!(rootsAt p.vals address).isEmpty && (rootsAt p.vals address).all fun
          | .local slot => replacementRootsEmpty f (rootsAt p.slots slot) || replacementSlotEmpty f vt p empty slot
          | .param parameter =>
              (vt[result]?).any (fun | some (.data (.slice ..)) => true | _ => false) &&
                (f.params[parameter]?).any Ty.isRefSlice &&
                parameterContents &&
                (f.roots.contents.find? (·.1 == parameter)).any
                  (fun row => (row.2.flatMap (ReplacementQueries.mk f.roots.params #[] #[]).expand).isEmpty)
          | .global _ => false)
    | _ => false

def replacementEmptyRound (f : Func) (vt : Array (Option VTy)) (p : Prov)
    (empty : Array Bool) (parameterContents : Bool) : Array Bool × Bool := Id.run do
  let mut empty := empty
  let mut changed := false
  for h : index in [0:f.blocks.size] do
    let block := f.blocks[index]
    for ((parameter, type), position) in block.params.zipIdx do
      let incoming := incomingValues f index position
      if type.refLike && (rootsAt p.vals parameter).isEmpty && !incoming.isEmpty &&
          incoming.all (fun value => empty[value]?.getD false) && !empty[parameter]?.getD false && parameter < empty.size then
        empty := empty.set! parameter true
        changed := true
    for inst in block.insts do
      if let .def value op := inst then
        if replacementEmptyOp f vt p empty parameterContents value op && !empty[value]?.getD false && value < empty.size then
          empty := empty.set! value true
          changed := true
  return (empty, changed)

def replacementEmptyCandidate (f : Func) (vt : Array (Option VTy)) (p : Prov)
    (parameterContents : Bool) : Array Bool := Id.run do
  let mut empty := p.vals.map (replacementRootsEmpty f)
  let mut changed := true
  let mut fuel := p.vals.size + 1
  while changed && fuel > 0 do
    let (next, progress) := replacementEmptyRound f vt p empty parameterContents
    empty := next
    changed := progress
    fuel := fuel - 1
  return empty

def replacementEmptyValues (m : Module) (f : Func) (vt : Array (Option VTy)) (p : Prov) : Array Bool :=
  let candidate := replacementEmptyCandidate f vt p (parameterContents := true)
  if replacementParameterContentsStable m f vt p candidate then candidate
  else replacementEmptyCandidate f vt p (parameterContents := false)

def replacementQueries (m : Module) (f : Func) (vt : Array (Option VTy)) (p : Prov) : ReplacementQueries :=
  ⟨f.roots.params, p.vals, replacementEmptyValues m f vt p⟩

def ReplacementQueries.value (queries : ReplacementQueries) (value : ValueId) : ReplacementRootQuery :=
  match rootsAt queries.values value with
  | [] => if queries.emptyValues[value]?.getD false then some [] else none
  | roots => some (roots.flatMap queries.expand)

def replacementOverlap (left right : ReplacementRootQuery) : Bool :=
  match left, right with
  | some [], _ | _, some [] => false
  | some left, some right => left.any fun root => right.any (Goose.Core.rootsMayOverlap root)
  | _, _ => true

def killEmptyFacts (facts : List ValueId) (roots : ReplacementRootQuery)
    (queries : ReplacementQueries) : List ValueId :=
  facts.filter fun fact => !replacementOverlap roots (queries.value fact)

def callSummaryRoots (m : Module) (queries : ReplacementQueries) (fn : FnId)
    (args : List ValueId) : ReplacementRootQuery :=
  match m.funcs[fn]? with
  | none => none
  | some callee =>
    match callee.summary with
    | .unknown => none
    | .known summary =>
      let touched := summary.reads ++ summary.writes ++ summary.grows ++
        summary.shrinks ++ summary.rebinds
      touched.foldlM (init := []) fun roots target => do
        match target with
        | .global g => pure (unionRoots roots [.global g])
        | .param i =>
          let arg ← args[i]?
          let actual ← queries.value arg
          let annotated := ((callee.roots.params.find? (·.1 == i)).map (·.2)).getD [] |>.filterMap fun
            | .global g => some (.global g)
            | _ => none
          pure (unionRoots roots (actual ++ annotated))

def callDependencies (m : Module) (vt : Array (Option VTy)) (queries : ReplacementQueries)
    (fn : FnId) (args : List ValueId) : ReplacementRootQuery :=
  if args.any (fun arg => valRefLike vt arg && queries.value arg == some []) then some [] else
    let argumentRoots := args.foldlM (init := []) fun roots arg => do
      if !valRefLike vt arg then pure roots else
        let actual ← queries.value arg
        pure (unionRoots roots actual)
    argumentRoots.bind fun roots => do
      let touched ← callSummaryRoots m queries fn args
      pure (unionRoots roots touched)

/-- Values evaluated as sources by an instruction. Mutation targets are handled
separately, calls use their summary, and edge arguments only transport facts
to block parameters. -/
def emptyFactSourceOperands : Inst → List ValueId
  | .def _ (.call ..) => []
  | .def _ (.push _ value _) => [value]
  | .def _ op => op.uses
  | .eff (.slotInit _ value _) => [value]
  | .eff (.store _ value _) | .eff (.append _ value _) | .eff (.replace _ value _) => [value]
  | .eff (.popN _ count _) => [count]
  | .eff (.resize _ size fill _) => size :: fill.toList
  | .eff (.print parts _) => parts.flatMap PrintPart.uses
  | .eff (.clear ..) | .eff (.enter ..) | .eff (.leave ..) => []
  | .term _ => []

def killEmptyFactSources (facts : List ValueId) (operands : List ValueId)
    (vt : Array (Option VTy)) (p : ReplacementQueries) : List ValueId :=
  operands.foldl (fun current operand =>
    if valRefLike vt operand then killEmptyFacts current (p.value operand) p
    else current) facts

def transferEmptyInst (m : Module) (vt : Array (Option VTy)) (p : ReplacementQueries)
    (facts : List ValueId) (inst : Inst) : List ValueId := Id.run do
  let afterReceiver := match inst with
    | .eff (.clear r _) => if facts.contains r then facts else facts ++ [r]
    | .def _ (.call fn args _) =>
      killEmptyFacts facts (callDependencies m vt p fn args) p
    | .def _ (.load r) | .def _ (.snapshot _ r) | .def _ (.arrayLen r)
    | .def _ (.sliceView r) | .def _ (.viewLen r) | .def _ (.viewSlice _ r ..)
    | .def _ (.indexChecked r ..) | .def _ (.indexProven r ..)
    | .def _ (.push r ..) | .def _ (.pop r ..)
    | .eff (.store r ..) | .eff (.append r ..) | .eff (.popN r ..)
    | .eff (.resize r ..) | .eff (.replace r ..) => killEmptyFacts facts (p.value r) p
    | _ => facts
  let afterSources := killEmptyFactSources afterReceiver (emptyFactSourceOperands inst) vt p
  match inst with
  | .def res _ =>
    if valRefLike vt res then pure (killEmptyFacts afterSources (p.value res) p)
    else pure afterSources
  | _ => pure afterSources

def transferEmptyBlock (m : Module) (vt : Array (Option VTy)) (p : ReplacementQueries)
    (facts : List ValueId) (b : Block) : List ValueId :=
  b.insts.foldl (transferEmptyInst m vt p) facts

/-- Carry empty-owner facts through block arguments. Source SSA values remain
available along the edge; the target parameter gains the fact when its matching
argument is known empty. Joins later remove facts that are not common to paths. -/
def transferEmptyEdge (f : Func) (facts : List ValueId) (target : BlockId)
    (args : List ValueId) : List ValueId :=
  match f.blocks[target]? with
  | none => facts
  | some block =>
    (block.params.zip args).foldl (fun current ((parameter, _), argument) =>
      if current.contains argument && !current.contains parameter then current ++ [parameter]
      else current) facts

def emptyFactRound (m : Module) (f : Func) (vt : Array (Option VTy)) (p : ReplacementQueries)
    (states : Array (Option (List ValueId))) : Array (Option (List ValueId)) × Bool := Id.run do
  let mut states := states
  let mut changed := false
  let oldStates := states
  for h : b in [0:f.blocks.size] do
    if let some block := f.blocks[b]? then
      if let some incoming := oldStates[b]? |>.join then
        let outgoing := transferEmptyBlock m vt p incoming block
        for (target, args) in block.terms.flatMap termEdges do
          if target < states.size then
            let edgeFacts := transferEmptyEdge f outgoing target args
            match states[target]? with
            | some none =>
              states := states.set! target (some edgeFacts)
              changed := true
            | some (some previous) =>
              let merged := previous.filter edgeFacts.contains
              if merged != previous then
                states := states.set! target (some merged)
                changed := true
            | none => pure ()
  return (states, changed)

def emptyFactsAtBlocks (m : Module) (f : Func) (vt : Array (Option VTy)) (p : ReplacementQueries) :
    Array (Option (List ValueId)) := Id.run do
  let mut states : Array (Option (List ValueId)) := Array.replicate f.blocks.size none
  if !f.blocks.isEmpty then states := states.set! 0 (some [])
  let mut changed := true
  let mut fuel := (f.blocks.size + 1) * (f.numValues + 1) + 1
  while changed && fuel > 0 do
    let (next, progress) := emptyFactRound m f vt p states
    states := next
    changed := progress
    fuel := fuel - 1
  return states

def checkReplace (m : Module) (f : Func) (vt : Array (Option VTy)) (p : ReplacementQueries) (validRuns : Array Bool)
    (label : String) (facts : List ValueId) (inst : Inst) : Check Unit := do
  match inst with
  | .eff (.replace owner run _) =>
    let ownerTy := (ownerTy vt owner).getD .unit
    unless ownerTy matches .grow _ | .growshrink _ do
      violation .v060 s!"{label}: x_replace owner is not grow or growshrink"
    unless validRuns[run]?.getD false do
      violation .v060 s!"{label}: x_replace run is not a fresh literal run"
    unless facts.contains owner do
      violation .v060 s!"{label}: x_replace owner was not cleared on every path"
  | _ => pure ()

def checkShrinkReplace (m : Module) (label : String) (f : Func) (vt : Array (Option VTy))
    (p : Prov) : Check Unit := do
  if m.profile == .shrink then
    let p := replacementQueries m f vt p
    let validRuns := freshRuns f vt
    let states := emptyFactsAtBlocks m f vt p
    for h : b in [0:f.blocks.size] do
      let some block := f.blocks[b]? | pure ()
      let some facts := states[b]? |>.join |
        violation .v060 s!"{label}: no clear-state proof for block {b}"
      let mut current := facts
      for inst in block.insts do
        checkReplace m f vt p validRuns label current inst
        current := transferEmptyInst m vt p current inst

/-! ### The module -/

structure FnInfo where
  label : String
  f : Func
  vt : Array (Option VTy)

/-- The summary of function `k` closes over the effects of its body. -/
def checkSummaryOf (m : Module) (vts : Array (Array (Option VTy))) (res : Array (List RootRef))
    (nRoots : Nat) (k : Nat) : Check Unit :=
  match m.funcs[k]? with
  | none => pure ()
  | some f => do
    checkRootAnnotationsOf m vts res nRoots k
    let vt := vts[k]?.getD #[]
    asCheck .v050 s!"function {f.name}" (f.summaryClosed (f.effects m (f.provenance res vt nRoots)))

/-- Every function of the module with the name the diagnostics use: the
implementations, then the initializers. -/
def Module.labelled (m : Module) : List (String × Func) :=
  (m.funcs.toList.map fun f => (s!"function {f.name}", f)) ++
  (m.globals.toList.map fun g => (s!"initializer of global {g.name}", g.init))

def checkUnreachable (m : Module) : Check Unit :=
  let mayReturn := m.functionsMayReturn
  checkAll m.labelled fun (label, f) => checkUnreachableOf mayReturn label f

def Module.infos (m : Module) : List FnInfo :=
  m.labelled.map fun (l, f) => FnInfo.mk l f (f.valueTypes m)

/-- The value types of the implementations, in order. -/
def Module.implTypes (m : Module) : Array (Array (Option VTy)) :=
  (m.infos.take m.funcs.size).map (·.vt) |>.toArray

def Module.rootCount (m : Module) : Nat :=
  m.globals.size + m.funcs.foldl (fun n f => n + f.params.length + f.slots.size) 0

def validate (m : Module) : Check Unit := do
  checkEntryAndGlobals m
  checkAll m.labelled fun (l, f) => checkSymbols m l f
  checkStructTypes m
  checkAll m.infos fun i => checkTypes m i.label i.f i.vt
  checkAll m.infos fun i => checkCfg i.label i.f i.vt
  checkUnreachable m
  let walks := m.infos.map fun i => walkScopes i.label i.f
  checkAll (m.infos.zip walks) fun (i, w) => do
    if let some msg := w.storage then violation .v030 msg
    checkStorage m i.label i.f i.vt
    checkPermissions m i.label i.f i.vt
  checkAll walks fun w => do
    if let some msg := w.scopes then violation .v040 msg
  -- Summaries are closed over what each body does, with each callee's own summary.
  let res := resultRoots m m.implTypes
  checkAll (List.range m.funcs.size) (checkSummaryOf m m.implTypes res m.rootCount)
  checkAll m.infos fun i =>
    let p := i.f.provenance res i.vt m.rootCount
    checkShrinkReplace m i.label i.f i.vt p
  checkAll m.infos fun i => asCheck .v080 i.label (checkEvidence m i.f i.vt)
  checkAll m.infos fun i => checkOrigins m.profile i.label i.f

end Goose.GIR
