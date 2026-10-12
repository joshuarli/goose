import Goose.GIR.Syntax
import Goose.Core.Eval

/-!
The meaning of a GIR-H module: one total function indexed by fuel and by the
numeric profile, over Core's memory model, values, outcomes and traces, so a
result of `run` is directly comparable with a result of `Core.eval`.

* Fuel is the structural recursion argument of the mutual block. Every
  instruction, every terminator and every call consumes one unit, so `run n` is
  monotone in `n` and a loop is a chain of terminators that each pass the
  predecessor.
* A frame holds the activation id, the scopes entered so far with their
  instances, and one cell per value id. A cell that was never written is read
  as an `unbound` fault, so a use that is not dominated by its definition is a
  fault rather than a stale value.
* `scope.enter` and the call of a function draw their instance ids from the same
  counters as Core's block entry and call, in the same dynamic order, so a
  reference to a slot has the same `Loc` as the reference to the variable.
* A global initializer is a function activated at depth 0 and the entry at
  depth 1, as Core evaluates them.
* Faults are raised by the same helpers as in Core (`expect*`, the store
  accessors, the table lookups) and by `flow` for a block that ends without a
  terminator or a `scope.leave` that does not match the innermost scope.
-/

namespace Goose.GIR

open Goose.Core

/-- A value held in a cell of a frame. A view is never stored in memory. -/
inductive RVal
  | val (v : Val)
  | view (vw : ViewVal)

structure GCfg where
  profile : NumProfile
  mod : Module

structure Frame where
  act : ActId
  /-- Scopes entered so far, innermost first, with their instances. -/
  scopes : List (ScopeId × ScopeInst)
  vals : Array (Option RVal)
  /-- Calls between the entry and this activation. -/
  depth : Nat

section Helpers

def getCell (fr : Frame) (v : ValueId) : M RVal :=
  match fr.vals[v]? with
  | some (some x) => pure x
  | _ => fault .unbound

def getVal (fr : Frame) (v : ValueId) : M Val := do
  match (← getCell fr v) with
  | .val x => pure x
  | .view _ => fault .shape

def getView (fr : Frame) (v : ValueId) : M ViewVal := do
  match (← getCell fr v) with
  | .view vw => pure vw
  | .val _ => fault .shape

def setCell (fr : Frame) (v : ValueId) (x : RVal) : M Frame :=
  if v < fr.vals.size then pure { fr with vals := fr.vals.set! v (some x) }
  else fault .unbound

def bindParams (fr : Frame) : List (ValueId × VTy) → List RVal → M Frame
  | p :: ps, a :: as => do bindParams (← setCell fr p.1 a) ps as
  | _, _ => pure fr

/-- An abort needs the origin its outcome names. -/
def abortAtOrg (k : AbortKind) (org : Option OriginId) : M α :=
  match org with
  | some o => abortAt k o
  | none => fault .unbound

def lookupFn (cfg : GCfg) (f : FnId) : M Func :=
  match cfg.mod.funcs[f]? with
  | some fn => pure fn
  | none => fault .unbound

def lookupInit (cfg : GCfg) (g : GlobalId) : M Func :=
  match cfg.mod.globals[g]? with
  | some gl => pure gl.init
  | none => fault .unbound

/-- The root instance of a slot: its scope must be entered. -/
def slotRoot (fn : Func) (fr : Frame) (s : SlotId) : M RootInst :=
  match fn.slots[s]? with
  | none => fault .unbound
  | some sl =>
    match fr.scopes.lookup sl.scope with
    | none => fault .unbound
    | some si => pure (.local fr.act si s)

/-- Remove the roots of the slots of scope `sc`, instance `si`. -/
def releaseSlots (fn : Func) (act : ActId) (sc : ScopeId) (si : ScopeInst) : Nat → Store → Store
  | 0, st => st
  | i + 1, st =>
    match fn.slots[i]? with
    | some sl => releaseSlots fn act sc si i (if sl.scope == sc then st.release (.local act si i) else st)
    | none => releaseSlots fn act sc si i st

def releaseScope (fn : Func) (act : ActId) (sc : ScopeId) (si : ScopeInst) : M Unit := fun s =>
  .ok () { s with store := releaseSlots fn act sc si fn.slots.size s.store }

def evalBnd (fr : Frame) (len : Nat) (dflt : Int) : Bnd → M Int
  | .omitted => pure dflt
  | .val v => do
    let (_, k) ← expectInt (← getVal fr v)
    pure k
  | .fromEnd v => do
    let (_, k) ← expectInt (← getVal fr v)
    pure ((len : Int) - k)

def renderPart (fr : Frame) : PrintPart → M String
  | .text s => pure s
  | .val v => do render (← getVal fr v)

/-- Instructions that define no value. -/
def execEff (fn : Func) (fr : Frame) : Effect → M Frame
  | .slotInit s v _ => do
    let r ← slotRoot fn fr s
    bindRoot r (← getVal fr v)
    pure fr
  | .store r v _ => do
    let l ← expectRef (← getVal fr r)
    writeLoc l (← getVal fr v)
    pure fr
  | .append r v _ => do
    let l ← expectRef (← getVal fr r)
    let elems ← readRun (← getView fr v)
    let _ ← appendLoc l elems
    pure fr
  | .enter sc => do
    let si ← freshScope
    pure { fr with scopes := (sc, si) :: fr.scopes }
  | .leave sc =>
    match fr.scopes with
    | (s, si) :: rest =>
      if s = sc then do
        releaseScope fn fr.act sc si
        pure { fr with scopes := rest }
      else fault .flow
    | [] => fault .flow
  | .print parts _ => do
    let strs ← parts.mapM (renderPart fr)
    emit (String.join strs ++ "\n")
    pure fr

end Helpers

mutual

/-- Call function `f` from an activation at depth `depth`. -/
def callFn : Nat → GCfg → Nat → FnId → List Val → M Val
  | 0, _, _, _, _ => timeout
  | n + 1, cfg, depth, f, vals => do
    if depth ≥ maxCallDepth then timeout
    let fn ← lookupFn cfg f
    enterFn n cfg (depth + 1) fn vals

/-- Run `fn` in a fresh activation whose frame has the given depth. -/
def enterFn : Nat → GCfg → Nat → Func → List Val → M Val
  | 0, _, _, _, _ => timeout
  | n + 1, cfg, depth, fn, vals => do
    if fn.params.length = vals.length then
      let act ← freshAct
      let fr : Frame := ⟨act, [], Array.replicate fn.numValues none, depth⟩
      runBlock n cfg fn fr 0 (vals.map RVal.val)
    else fault .arity

/-- Enter block `b` with its parameters bound to `args`. -/
def runBlock : Nat → GCfg → Func → Frame → BlockId → List RVal → M Val
  | 0, _, _, _, _, _ => timeout
  | n + 1, cfg, fn, fr, b, args => do
    match fn.blocks[b]? with
    | none => fault .unbound
    | some blk =>
      if blk.params.length = args.length then
        let fr' ← bindParams fr blk.params args
        runInsts n cfg fn fr' blk.insts
      else fault .arity

def runInsts : Nat → GCfg → Func → Frame → List Inst → M Val
  | 0, _, _, _, _ => timeout
  | _ + 1, _, _, _, [] => fault .flow
  | n + 1, cfg, fn, fr, i :: rest =>
    match i with
    | .def r op => do
      let x ← execOp n cfg fn fr op
      let fr' ← setCell fr r x
      runInsts n cfg fn fr' rest
    | .eff e => do
      let fr' ← execEff fn fr e
      runInsts n cfg fn fr' rest
    | .term t => execTerm n cfg fn fr t

def execTerm : Nat → GCfg → Func → Frame → Term → M Val
  | 0, _, _, _, _ => timeout
  | n + 1, cfg, fn, fr, t =>
    match t with
    | .br b args => do
      let vals ← args.mapM (getCell fr)
      runBlock n cfg fn fr b vals
    | .condbr c tb targs eb eargs => do
      if (← expectBool (← getVal fr c)) then
        runBlock n cfg fn fr tb (← targs.mapM (getCell fr))
      else runBlock n cfg fn fr eb (← eargs.mapM (getCell fr))
    | .ret vs _ =>
      match vs with
      | [] => pure .unit
      | [v] => getVal fr v
      | _ => fault .shape
    | .abort k org => abortAtOrg k org
    | .exit v _ => do
      let (_, code) ← expectInt (← getVal fr v)
      M.stop (.exit code)

def execOp : Nat → GCfg → Func → Frame → Op → M RVal
  | 0, _, _, _, _ => timeout
  | n + 1, cfg, fn, fr, op =>
    match op with
    | .constInt t k => pure (.val (.int t k))
    | .constBool b => pure (.val (.bool b))
    | .constUnit => pure (.val .unit)
    | .bin o t a b org => do
      let (u, x) ← expectInt (← getVal fr a)
      let (w, y) ← expectInt (← getVal fr b)
      expectSameTy u t
      expectSameTy w t
      match evalBin cfg.profile o t x y with
      | .ok r => pure (.val (.int t r))
      | .error k => abortAtOrg (AbortKind.ofNum k) org
    | .un o t a org => do
      let (u, x) ← expectInt (← getVal fr a)
      expectSameTy u t
      match evalUn cfg.profile o t x with
      | .ok r => pure (.val (.int t r))
      | .error k => abortAtOrg (AbortKind.ofNum k) org
    | .cmp o t a b => do
      let (u, x) ← expectInt (← getVal fr a)
      let (w, y) ← expectInt (← getVal fr b)
      expectSameTy u t
      expectSameTy w t
      pure (.val (.bool (evalCmp o x y)))
    | .boolCmp o a b => do
      let p ← expectBool (← getVal fr a)
      let q ← expectBool (← getVal fr b)
      pure (.val (.bool (evalCmp o (if p then 1 else 0) (if q then 1 else 0))))
    | .boolNot a => do
      pure (.val (.bool (!(← expectBool (← getVal fr a)))))
    | .conv k src dst a org => do
      let (u, x) ← expectInt (← getVal fr a)
      expectSameTy u src
      match evalConv cfg.profile k src dst x with
      | .ok r => pure (.val (.int dst r))
      | .error e => abortAtOrg (AbortKind.ofNum e) org
    | .next t a => do
      let (u, x) ← expectInt (← getVal fr a)
      expectSameTy u t
      if x < t.maxVal then pure (.val (.int t (x + 1))) else fault .shape
    | .slotAddr s => do
      let r ← slotRoot fn fr s
      pure (.val (.ref ⟨r, []⟩))
    | .globalAddr g => pure (.val (.ref ⟨.global g, []⟩))
    | .refElem v i => do
      let vw ← getView fr v
      let (_, k) ← expectInt (← getVal fr i)
      if 0 ≤ k then pure (.val (.ref ⟨vw.loc.root, vw.loc.path ++ [vw.start + k.toNat]⟩))
      else fault .pathRange
    | .refFreeze r => do
      pure (.val (.ref (← expectRef (← getVal fr r))))
    | .load r => do
      pure (.val (← readLoc (← expectRef (← getVal fr r))))
    | .snapshot r => do
      let l ← expectRef (← getVal fr r)
      let (len, resizable) ← expectArray (← readLoc l)
      pure (.view ⟨l, 0, len, resizable⟩)
    | .sliceView s => do
      let (l, start, len) ← expectSlice (← getVal fr s)
      pure (.view ⟨l, start, len, false⟩)
    | .viewLen v => do
      pure (.val (.int .i64 (← getView fr v).len))
    | .viewSlice _ v lo hi org => do
      let vw ← getView fr v
      let lo' ← evalBnd fr vw.len 0 lo
      let hi' ← evalBnd fr vw.len vw.len hi
      if 0 ≤ lo' ∧ lo' ≤ hi' ∧ hi' ≤ (vw.len : Int) then
        pure (.val (.slice vw.loc (vw.start + lo'.toNat) (hi' - lo').toNat))
      else abortAtOrg .sliceOob org
    | .arrayLen r => do
      let (len, _) ← expectArray (← readLoc (← expectRef (← getVal fr r)))
      pure (.val (.int .i64 len))
    | .indexChecked v i org => do
      let vw ← getView fr v
      let (_, k) ← expectInt (← getVal fr i)
      if 0 ≤ k ∧ k < (vw.len : Int) then
        pure (.val (.ref ⟨vw.loc.root, vw.loc.path ++ [vw.start + k.toNat]⟩))
      else abortAtOrg .indexOob org
    | .push r v _ => do
      let l ← expectRef (← getVal fr r)
      let x ← getVal fr v
      let i ← appendLoc l #[x]
      pure (.val (.ref { l with path := l.path ++ [i] }))
    | .call f args _ => do
      let vals ← args.mapM (getVal fr)
      pure (.val (← callFn n cfg fr.depth f vals))
    | .arrLit t vs => do
      let xs ← vs.mapM (getVal fr)
      pure (.val (← expectArrayLit t xs.toArray))
    | .arrFill t v => do
      let k ← expectFixedCount t
      let x ← getVal fr v
      pure (.val (.fixed (Array.replicate k x)))

end

/-- Initialize the globals in table order, each by an activation of its
initializer function at depth 0, then run the entry at depth 1. -/
def runModule (fuel : Nat) (cfg : GCfg) : M Unit := do
  for g in [0:cfg.mod.globals.size] do
    let init ← lookupInit cfg g
    let v ← enterFn fuel cfg 0 init []
    bindRoot (.global g) v
  let _ ← callFn fuel cfg 0 cfg.mod.entry []
  pure ()

/-- The meaning of a GIR-H module, in Core's result type. -/
def run (fuel : Nat) (profile : NumProfile) (m : Module) : Result :=
  match runModule fuel ⟨profile, m⟩ St.initial with
  | .ok _ s => .done .returned s.trace
  | .stop (.abort k org) s => .done (.aborted k org) s.trace
  | .stop (.exit code) s => .done (.exited code) s.trace
  | .stop (.fault k) _ => .fault k
  | .stop .timeout s => .timeout s.trace

end Goose.GIR
