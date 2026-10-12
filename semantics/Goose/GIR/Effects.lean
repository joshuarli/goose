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
def rootsOfDef (res : Array (List RootRef)) (vt : Array (Option VTy)) (p : Prov)
    (r : ValueId) : Op → List RootRef
  | .slotAddr s => [.local s]
  | .globalAddr g => [.global g]
  | .refElem v _ | .viewSlice _ v _ _ _ | .indexChecked v _ _ => rootsAt p.vals v
  | .refFreeze a | .snapshot a | .sliceView a | .push a _ _ => rootsAt p.vals a
  | .load a =>
    if valRefLike vt r then
      (rootsAt p.vals a).flatMap fun
        | .local s => rootsAt p.slots s
        | _ => []
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
      let (vs, c) := addTo p.vals r (rootsOfDef res vt p r op)
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
  let one (res : Array (List RootRef)) : Array (List RootRef) × Bool :=
    let next := (m.funcs.zip vts).map fun (f, vt) =>
      f.returnedRoots (f.provenance res vt nRoots)
    (next, (next.zip res).any fun (a, b) => a.length != b.length)
  let rec go : Nat → Array (List RootRef) → Array (List RootRef)
    | 0, res => res
    | k + 1, res =>
      let (res', ch) := one res
      if ch then go k res' else res'
  go (nRoots + m.funcs.size + 2) (Array.replicate m.funcs.size [])

/-! ### Effects of a body -/

def targetsOf (rs : List RootRef) : List Target := rootsTargets rs

def Func.effects (m : Module) (f : Func) (p : Prov) : Core.Eff :=
  let call (e : Core.Eff) (g : FnId) (args : List ValueId) : Core.Eff :=
    match m.funcs[g]? with
    | none => { e with unknown := true }
    | some callee =>
      match callee.summary with
      | .unknown => { e with unknown := true }
      | .known sm =>
        let argRoots := args.map (rootsAt p.vals)
        { e with
          reads := addTargets e.reads (mapSummaryTargets argRoots sm.reads)
          writes := addTargets e.writes (mapSummaryTargets argRoots sm.writes)
          grows := addTargets e.grows (mapSummaryTargets argRoots sm.grows)
          aborts := e.aborts || sm.aborts
          outputs := e.outputs || sm.outputs }
  f.blocks.foldl (fun acc blk => blk.insts.foldl (fun e i =>
    match i with
    | .def _ op =>
      match op with
      | .load a | .snapshot a | .arrayLen a =>
        { e with reads := addTargets e.reads (targetsOf (rootsAt p.vals a)) }
      | .push a _ _ => { e with grows := addTargets e.grows (targetsOf (rootsAt p.vals a)) }
      | .bin o .. => if o.mayAbort then { e with aborts := true } else e
      | .un .neg .. => { e with aborts := true }
      | .conv .as .. => { e with aborts := true }
      | .viewSlice .. | .indexChecked .. => { e with aborts := true }
      | .call g args _ => call e g args
      | _ => e
    | .eff (.store r _ _) =>
      let rs := rootsAt p.vals r
      let e := { e with writes := addTargets e.writes (targetsOf rs) }
      -- Storing through the slot of a reference parameter rebinds the parameter.
      let rebound := rs.filterMap fun
        | .local s =>
          match f.slots[s]? with
          | some sl => if sl.ty.isRefLike && sl.var < f.params.length then some (Target.param sl.var) else none
          | none => none
        | _ => none
      { e with rebinds := addTargets e.rebinds rebound }
    | .eff (.append r _ _) => { e with grows := addTargets e.grows (targetsOf (rootsAt p.vals r)) }
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
    f.targetsWithin "rebinds" e.rebinds s.rebinds
    Func.flagWithin s!"{f.name} may abort, which its summary omits" e.aborts s.aborts
    Func.flagWithin s!"{f.name} prints, which its summary omits" e.outputs s.outputs

end Goose.GIR
