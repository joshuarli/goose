import Goose.Core.Roots
import Goose.GIR.Typing

/-!
Where a reference may point, and the effects of a function body.

A module has no root annotations, so provenance is computed from the body.
Every reference, slice or view value gets the set of roots it may be rooted at:
a slot of the function (a local), a global, or what the caller passed as a
parameter. The set of a value is a union over everything that can flow into it,
without regard to order, and a slot holds the union of everything stored in it.
The result roots of a function are the roots of what it returns, in terms of
its parameters and globals, and are mapped to the arguments at each call. The
computation is a least fixed point, found by rounds bounded by the number of
roots that could be added.

The effects of a body are then the targets it reads, writes, grows and rebinds,
whether it may abort and whether it prints, in the vocabulary of a summary:
parameters and globals only. The rules mirror the Core rules for the same
operations, so a summary that closes over a Core body also closes over its
lowering.
-/

namespace Goose.GIR

open Goose.Core

structure Prov where
  /-- Roots of each slot's contents. -/
  slots : Array (List RootRef)
  /-- Roots of each value. -/
  vals : Array (List RootRef)

def rootsAt (a : Array (List RootRef)) (i : Nat) : List RootRef := a[i]?.getD []

def VTy.refLike : VTy → Bool
  | .data t => t.isRefLike
  | .view .. => true

def valRefLike (vt : Array (Option VTy)) (v : ValueId) : Bool :=
  match vt[v]? with
  | some (some t) => t.refLike
  | _ => false

/-- Add roots to a cell; the flag says whether anything was new. -/
def addTo (a : Array (List RootRef)) (i : Nat) (rs : List RootRef) : Array (List RootRef) × Bool :=
  let old := rootsAt a i
  let new := unionRoots old rs
  if new.length = old.length || i ≥ a.size then (a, false) else (a.set! i new, true)

/-- The roots of what an instruction defines. -/
def rootsOfDef (res : Array (List RootRef)) (vt : Array (Option VTy)) (f : Func) (p : Prov)
    (r : ValueId) : Op → List RootRef
  | .slotAddr s => [.local s]
  | .globalAddr g => [.global g]
  | .fieldAddr v _ | .refElem v _ | .viewSlice _ v _ _ _ | .indexChecked v _ _ => rootsAt p.vals v
  | .refFreeze a | .sliceView a | .push a _ _ => rootsAt p.vals a
  | .snapshot _ a => rootsAt p.vals a
  | .load a =>
    if valRefLike vt r then
      let stored := (rootsAt p.vals a).flatMap fun
        | .local s => rootsAt p.slots s
        | _ => []
      let contents := match vt[r]? with
        | some (some (.data (.slice ..))) =>
          (rootsAt p.vals a).flatMap fun
            | .param j =>
              match f.params[j]? with
              | some t => if t.isRefSlice then (f.roots.contents.find? (·.1 == j)).map (·.2) |>.getD [] else []
              | none => []
            | _ => []
        | _ => []
      unionRoots stored contents
    else []
  | .call f args _ =>
    (rootsAt res f).flatMap fun
      | .param j => (match args[j]? with
          | some a => rootsAt p.vals a
          | none => [])
      | .global g => [.global g]
      | .local _ => []
  | _ => []

/-- One round over the whole function; the flag says whether anything changed. -/
def provRound (res : Array (List RootRef)) (vt : Array (Option VTy)) (f : Func) (p : Prov) :
    Prov × Bool :=
  let edge (acc : Prov × Bool) (b : BlockId) (args : List ValueId) : Prov × Bool :=
    match f.blocks[b]? with
    | none => acc
    | some tb =>
      (tb.params.zip args).foldl (fun (p, ch) (prm, a) =>
        let (vs, c) := addTo p.vals prm.1 (rootsAt p.vals a)
        ({ p with vals := vs }, ch || c)) acc
  f.blocks.foldl (fun acc blk => blk.insts.foldl (fun (p, ch) i =>
    match i with
    | .def r op =>
      let (vs, c) := addTo p.vals r (rootsOfDef res vt f p r op)
      ({ p with vals := vs }, ch || c)
    | .eff (.slotInit s v _) =>
      let (ss, c) := addTo p.slots s (rootsAt p.vals v)
      ({ p with slots := ss }, ch || c)
    | .eff (.store r v _) =>
      (rootsAt p.vals r).foldl (fun (p, ch) root =>
        match root with
        | .local s =>
          let (ss, c) := addTo p.slots s (rootsAt p.vals v)
          ({ p with slots := ss }, ch || c)
        | _ => (p, ch)) (p, ch)
    | .term (.br b args) => edge (p, ch) b args
    | .term (.condbr _ t ta e ea) => edge (edge (p, ch) t ta) e ea
    | _ => (p, ch)) acc) (p, false)

/-- The starting provenance: each reference-like parameter of the entry block is
rooted at its own parameter. -/
def provStart (vt : Array (Option VTy)) (f : Func) : Prov :=
  let vals := match f.blocks[0]? with
    | none => Array.replicate f.numValues []
    | some b =>
      (b.params.zipIdx).foldl (fun a ((v, _), i) =>
        if valRefLike vt v && v < a.size then a.set! v [.param i] else a)
        (Array.replicate f.numValues [])
  ⟨Array.replicate f.slots.size [], vals⟩

/-- Rounds until nothing changes. A round that changes something adds a root to
a cell, so the number of rounds is at most the number of cells times roots. -/
def provFix (res : Array (List RootRef)) (vt : Array (Option VTy)) (f : Func) : Nat → Prov → Prov
  | 0, p => p
  | k + 1, p =>
    let (p', ch) := provRound res vt f p
    if ch then provFix res vt f k p' else p'

def Func.provenance (res : Array (List RootRef)) (vt : Array (Option VTy)) (f : Func) (nRoots : Nat) :
    Prov :=
  provFix res vt f ((f.numValues + f.slots.size + 1) * (nRoots + 1)) (provStart vt f)

/-- What a function returns, as roots in its own terms. -/
def Func.returnedRoots (f : Func) (p : Prov) : List RootRef :=
  f.blocks.foldl (fun acc b => b.insts.foldl (fun acc i =>
    match i with
    | .term (.ret [v] _) => unionRoots acc (rootsAt p.vals v)
    | _ => acc) acc) []

/-- Result roots of every function, by rounds over the whole module. -/
def resultRoots (m : Module) (vts : Array (Array (Option VTy))) : Array (List RootRef) :=
  let nRoots := m.globals.size + m.funcs.foldl (fun n f => n + f.params.length + f.slots.size) 0
  let initial := m.funcs.map fun _ => []
  let one (res : Array (List RootRef)) : Array (List RootRef) × Bool :=
    let next := (m.funcs.zip vts).mapIdx fun k (f, vt) =>
      unionRoots (res[k]?.getD []) (f.returnedRoots (f.provenance res vt nRoots))
    (next, (next.zip res).any fun (a, b) => a.length != b.length)
  let rec go : Nat → Array (List RootRef) → Array (List RootRef)
    | 0, res => res
    | k + 1, res =>
      let (res', ch) := one res
      if ch then go k res' else res'
  go (nRoots + m.funcs.size + 2) initial

/-- A parameter annotation describes the concrete roots a specialization may
refer to. An absent or empty row keeps the generic parameter root, so omission
cannot erase effects while a caller is being analyzed. -/
def Func.parameterRoots (f : Func) (i : Nat) : List RootRef :=
  match f.roots.params.find? (·.1 == i) with
  | some (_, roots) => if roots.isEmpty then [.param i] else roots
  | none => [.param i]

def Func.contentRoots (f : Func) (i : Nat) : List RootRef :=
  f.roots.contents.foldl (fun roots row => if row.1 == i then row.2 else roots) []

/-- Expand a caller's parameter roots in the caller's vocabulary. -/
def Func.expandParameterRoot (f : Func) : RootRef → List RootRef
  | .param i => f.parameterRoots i
  | root => [root]

/-- The roots a ref-like argument may denote in the callee's vocabulary. -/
def mapArgumentRoots (caller : Func) (p : Prov) (value calleeParam : ValueId) : List RootRef :=
  let mapped := (rootsAt p.vals value).flatMap fun root =>
    match root with
    | .local _ => [.param calleeParam]
    | .global _ => [root]
    | .param i =>
      (caller.parameterRoots i).map fun
        | .global g => .global g
        | _ => RootRef.param calleeParam
  mapped.foldl (fun acc root => unionRoots acc [root]) []

/-- The backing roots of a ref-to-slice argument in the caller's vocabulary. -/
def argumentContents (caller : Func) (p : Prov) (value : ValueId) : List RootRef :=
  let mapped := (rootsAt p.vals value).flatMap fun root =>
    let roots := match root with
      | .local s => rootsAt p.slots s
      | .global g => [.global g]
      | .param i =>
        match caller.params[i]? with
        | some t => if t.isRefSlice then
            caller.contentRoots i
          else []
        | none => []
    roots.flatMap caller.expandParameterRoot
  mapped.foldl (fun acc root => unionRoots acc [root]) []

/-- Map the callee's content-root annotation through the arguments at a call.
References to local slice variables and forwarded slice references retain the
roots of their backing elements. Other arguments denote their own storage;
global roots already have the same identity in both cases. -/
def mapContentRoots (caller : Func) (p : Prov) (args : List ValueId) (roots : List RootRef) :
    List RootRef :=
  let mapped := roots.flatMap fun
    | .global g => [.global g]
    | .param j =>
      match args[j]? with
      | some a =>
        let referencesSlice := (rootsAt p.vals a).any fun
          | .local s => (caller.slots[s]?).any (fun slot => slot.ty.isSlice)
          | .param i => (caller.params[i]?).any Ty.isRefSlice
          | .global _ => false
        if referencesSlice then argumentContents caller p a
        else (rootsAt p.vals a).flatMap caller.expandParameterRoot
      | none => []
    | .local _ => []
  mapped.foldl (fun acc root => unionRoots acc [root]) []

/-! ### Effects of a body -/

def targetsOf (rs : List RootRef) : List Target := rootsTargets rs

def ownerTy (vt : Array (Option VTy)) (v : ValueId) : Option Ty :=
  match vt[v]? with
  | some (some (.data (.ref _ t))) => some t
  | _ => none

def ownerIsLimited (vt : Array (Option VTy)) (v : ValueId) : Bool :=
  match ownerTy vt v with
  | some (.limited ..) => true
  | _ => false

def Func.effects (m : Module) (f : Func) (p : Prov) : Core.Eff :=
  let vt := f.valueTypes m
  let call (e : Core.Eff) (g : FnId) (args : List ValueId) : Core.Eff :=
    match m.funcs[g]? with
    | none => { e with unknown := true }
    | some callee =>
      match callee.summary with
      | .unknown => { e with unknown := true }
      | .known sm =>
        let argRoots := args.map fun a =>
          let expanded := (rootsAt p.vals a).flatMap f.expandParameterRoot
          expanded.foldl (fun acc root => unionRoots acc [root]) []
        let mapTargets (targets : List Target) :=
          let actual := mapSummaryTargets argRoots targets
          let annotated := targets.flatMap fun
            | .param j =>
              match callee.params[j]? with
              | some t =>
                if t.isRefLike then
                  ((callee.roots.params.find? (·.1 == j)).map (·.2)).getD [] |>.filterMap fun
                    | .global g => some (.global g)
                    | _ => none
                else []
              | none => []
            | .global _ => []
          addTargets actual annotated
        { e with
          reads := addTargets e.reads (mapTargets sm.reads)
          writes := addTargets e.writes (mapTargets sm.writes)
          grows := addTargets e.grows (mapTargets sm.grows)
          shrinks := addTargets e.shrinks (mapTargets sm.shrinks)
          aborts := e.aborts || sm.aborts
          outputs := e.outputs || sm.outputs }
  f.blocks.foldl (fun acc blk => blk.insts.foldl (fun e i =>
    match i with
    | .def _ op =>
      match op with
      | .load a | .arrayLen a =>
        { e with reads := addTargets e.reads (targetsOf (rootsAt p.vals a)) }
      | .snapshot _ a => { e with reads := addTargets e.reads (targetsOf (rootsAt p.vals a)) }
      | .push a _ _ =>
        let targets := targetsOf (rootsAt p.vals a)
        let e := { e with grows := addTargets e.grows targets }
        if m.profile == .shrink then
          { e with
            writes := addTargets e.writes targets
            aborts := e.aborts || ownerIsLimited vt a }
        else e
      | .pop a _ =>
        let targets := targetsOf (rootsAt p.vals a)
        { e with
          reads := addTargets e.reads targets
          shrinks := addTargets e.shrinks targets
          aborts := true }
      | .bin o .. => if o.mayAbort then { e with aborts := true } else e
      | .un .neg .. => { e with aborts := true }
      | .conv .as .. => { e with aborts := true }
      | .viewSlice .. | .indexChecked .. => { e with aborts := true }
      | .call g args _ => call e g args
      | _ => e
    | .eff (.store r _ _) =>
      let rs := rootsAt p.vals r
      let e := { e with writes := addTargets e.writes (targetsOf rs) }
      -- A store through a reference-to-slice parameter replaces the caller's slice.
      let rebound := rs.filterMap fun
        | .local s =>
          match f.slots[s]? with
          | some sl => if sl.ty.isRefLike && sl.var < f.params.length then some (Target.param sl.var) else none
          | none => none
        | .param j =>
          match f.params[j]? with
          | some t => if t.isRefSlice then some (Target.param j) else none
          | none => none
        | .global _ => none
      { e with rebinds := addTargets e.rebinds rebound }
    | .eff (.append r v _) =>
      let targets := targetsOf (rootsAt p.vals r)
      let sourceTargets := targetsOf (rootsAt p.vals v)
      let e := { e with
        reads := addTargets e.reads sourceTargets
        grows := addTargets e.grows targets }
      if m.profile == .shrink then
        { e with
          writes := addTargets e.writes targets
          aborts := e.aborts || ownerIsLimited vt r }
      else e
    | .eff (.popN r _ _) =>
      let targets := targetsOf (rootsAt p.vals r)
      { e with
        reads := addTargets e.reads targets
        shrinks := addTargets e.shrinks targets
        aborts := true }
    | .eff (.resize r _ fill _) =>
      let targets := targetsOf (rootsAt p.vals r)
      let e := { e with
        reads := addTargets e.reads targets
        shrinks := addTargets e.shrinks targets
        aborts := true }
      match fill with
      | none => e
      | some _ => { e with
          writes := addTargets e.writes targets
          grows := addTargets e.grows targets }
    | .eff (.clear r _) =>
      let targets := targetsOf (rootsAt p.vals r)
      { e with
        reads := addTargets e.reads targets
        shrinks := addTargets e.shrinks targets }
    | .eff (.replace r _ _) =>
      let targets := targetsOf (rootsAt p.vals r)
      { e with
        reads := addTargets e.reads targets
        writes := addTargets e.writes targets
        grows := addTargets e.grows targets
        shrinks := addTargets e.shrinks targets }
    | .eff (.print ..) => { e with outputs := true }
    | .term (.abort ..) | .term (.exit ..) => { e with aborts := true }
    | _ => e) acc) {}

/-- Every found target is declared. -/
def Func.targetsWithin (f : Func) (what : String) (found declared : List Target) : Except String Unit :=
  match found.find? (fun t => !declared.contains t) with
  | some t => throw s!"{f.name} {what} {showTarget t}, which its summary omits"
  | none => pure ()

/-- A boolean effect that is found must be declared. -/
def Func.flagWithin (msg : String) (found declared : Bool) : Except String Unit :=
  if found && !declared then throw msg else pure ()

/-- A callee with an unknown summary makes the function's own unknowable. -/
def Func.noUnknownCallee (f : Func) (unknown : Bool) : Except String Unit :=
  if unknown then
    throw s!"{f.name} calls a function whose summary is unknown, so its own summary cannot be known"
  else pure ()

/-- The summary closes over the body's effects: each effect is declared, and no
callee has an unknown summary unless this function's own is unknown. -/
def Func.summaryClosed (f : Func) (e : Core.Eff) : Except String Unit :=
  match f.summary with
  | .unknown => pure ()
  | .known s => do
    f.noUnknownCallee e.unknown
    f.targetsWithin "reads" e.reads s.reads
    f.targetsWithin "writes" e.writes s.writes
    f.targetsWithin "grows" e.grows s.grows
    f.targetsWithin "shrinks" e.shrinks s.shrinks
    f.targetsWithin "rebinds" e.rebinds s.rebinds
    Func.flagWithin s!"{f.name} may abort, which its summary omits" e.aborts s.aborts
    Func.flagWithin s!"{f.name} prints, which its summary omits" e.outputs s.outputs

end Goose.GIR
