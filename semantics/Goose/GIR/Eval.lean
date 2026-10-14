import Goose.GIR.Syntax
import Std.Data.HashMap
import Goose.Core.Eval

/-!
The meaning of a GIR-H module: one total function indexed by fuel and by the
numeric profile, over Core's memory model, values, outcomes and traces, so a
result of `run` is directly comparable with a result of `Core.eval`.

* Fuel is the structural recursion argument of the mutual block. Every
  instruction, every terminator and every call consumes one unit, so `run n` is
  monotone in `n` and a loop is a chain of terminators that each pass the
  predecessor. Running a function's blocks is one self-recursive function, so a
  loop compiles to a jump.
* A frame holds the activation id, the scopes entered so far with their
  instances, and the value of each id defined so far. An id that was never
  written is read as an `unbound` fault, so a use that is not dominated by its definition is a
  fault rather than a stale value.
* `scope.enter` and the call of a function draw their instance ids from the same
  counters as Core's block entry and call, in the same dynamic order, so a
  reference to a slot has the same `Loc` as the reference to the variable.
* An integer instruction takes its type from its operands, as Core's evaluator
  does; the type it states is the verifier's concern and `run` does not read it.
  A comparison of two integers of one type or of two booleans is the same
  operation whichever of the two instructions states it.
* A global initializer is a function activated at depth 0 and the entry at
  depth 1, as Core evaluates them.
* `next` adds one to its operand without a range check, as Core's loops do: the
  lowering applies it only to a counter that is below its loop bound, and a
  bound that is an array length can lie beyond the counter type's range only
  for an array longer than the type, which Core's model allows and a real
  array does not.
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

/-- What a block runs against: the configuration and the function it belongs to. -/
structure FnCtx where
  cfg : GCfg
  fn : Func

structure Frame where
  act : ActId
  /-- Scopes entered so far, innermost first, with their instances. -/
  scopes : List (ScopeId × ScopeInst)
  /-- The value of each id defined so far; the map is never iterated. -/
  vals : Std.HashMap ValueId RVal
  /-- Calls between the entry and this activation. -/
  depth : Nat

section Helpers

def getCell (fr : Frame) (v : ValueId) : M RVal :=
  match fr.vals[v]? with
  | some x => pure x
  | none => fault .unbound

def getVal (fr : Frame) (v : ValueId) : M Val := do
  match (← getCell fr v) with
  | .val x => pure x
  | .view _ => fault .shape

def getView (fr : Frame) (v : ValueId) : M ViewVal := do
  match (← getCell fr v) with
  | .view vw => pure vw
  | .val _ => fault .shape

def setCell (fr : Frame) (v : ValueId) (x : RVal) : M Frame :=
  pure { fr with vals := fr.vals.insert v x }

def bindParams (fr : Frame) : List (ValueId × VTy) → List RVal → M Frame
  | p :: ps, a :: as => do bindParams (← setCell fr p.1 a) ps as
  | _, _ => pure fr

/-- An abort needs the origin its outcome names. -/
def abortAtOrg (k : AbortKind) (org : Option OriginId) : M α :=
  match org with
  | some o => abortAt k o
  | none => fault .unbound

/-- Check the limited owner's static bound after operands are evaluated. -/
def checkCapacityAtOrg (l : Loc) (count : Nat) (org : Option OriginId) : M Unit := do
  match (← readLoc l) with
  | .limited _ capacity _ len =>
    if len + count > capacity then abortAtOrg .capacity org else pure ()
  | .resizable .. => pure ()
  | _ => fault .shape

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
  | .append r v org => do
    let l ← expectRef (← getVal fr r)
    let elems ← readRun (← getView fr v)
    checkCapacityAtOrg l elems.size org
    let _ ← appendLoc l elems
    pure fr
  | .popN r count org => do
    let l ← expectRef (← getVal fr r)
    let (_, n) ← expectInt (← getVal fr count)
    let len ← lengthLoc l
    if n < 0 || n > (len : Int) then abortAtOrg .popNRange org
    else
      truncateLoc l (len - n.toNat)
      pure fr
  | .resize r size fill org => do
    let l ← expectRef (← getVal fr r)
    let (_, n) ← expectInt (← getVal fr size)
    let fillValue ← match fill with
      | none => pure none
      | some v => do pure (some (← getVal fr v))
    let len ← lengthLoc l
    let n := wrap .i64 n
    if n < 0 then abortAtOrg .resizeNegative org
    else if n.toNat < len then
      truncateLoc l n.toNat
      pure fr
    else if n.toNat == len then
      pure fr
    else
      match fillValue with
      | none => abortAtOrg .resizeFill org
      | some value => do
        checkCapacityAtOrg l (n.toNat - len) org
        let _ ← appendLoc l (Array.replicate (n.toNat - len) value)
        pure fr
  | .clear r _ => do
    let l ← expectRef (← getVal fr r)
    truncateLoc l 0
    pure fr
  | .replace r run _ => do
    let l ← expectRef (← getVal fr r)
    let value ← getVal fr run
    match value with
    | .resizable _ _ => writeLoc l value
    | _ => fault .shape
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
    let strs ← mapList (renderPart fr) parts
    emit (String.join strs ++ "\n")
    pure fr

end Helpers

/-- Every operation that defines a value and needs no fuel. The integer
operations take the type of their operand, as Core's evaluator does; the type an
instruction states is the verifier's concern. -/
def execPure (cx : FnCtx) (fr : Frame) : Op → M RVal
    | .constInt t k => pure (.val (.int t k))
    | .constBool b => pure (.val (.bool b))
    | .constUnit => pure (.val .unit)
    | .bin o _ a b org => do
      let (t, x) ← expectInt (← getVal fr a)
      let (u, y) ← expectInt (← getVal fr b)
      expectSameTy t u
      match evalBin cx.cfg.profile o t x y with
      | .ok r => pure (.val (.int t r))
      | .error k => abortAtOrg (AbortKind.ofNum k) org
    | .un o _ a org => do
      let (t, x) ← expectInt (← getVal fr a)
      match evalUn cx.cfg.profile o t x with
      | .ok r => pure (.val (.int t r))
      | .error k => abortAtOrg (AbortKind.ofNum k) org
    | .cmp o _ a b => do
      let (i, j) ← expectComparable (← getVal fr a) (← getVal fr b)
      pure (.val (.bool (evalCmp o i j)))
    | .boolCmp o a b => do
      let (i, j) ← expectComparable (← getVal fr a) (← getVal fr b)
      pure (.val (.bool (evalCmp o i j)))
    | .boolNot a => do
      pure (.val (.bool (!(← expectBool (← getVal fr a)))))
    | .conv k _ dst a org => do
      let (src, x) ← expectInt (← getVal fr a)
      match evalConv cx.cfg.profile k src dst x with
      | .ok r => pure (.val (.int dst r))
      | .error e => abortAtOrg (AbortKind.ofNum e) org
    | .next _ a => do
      let (t, x) ← expectInt (← getVal fr a)
      pure (.val (.int t (x + 1)))
    | .slotAddr s => do
      let r ← slotRoot cx.fn fr s
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
    | .snapshot _ r => do
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
    | .indexProven v i => do
      let vw ← getView fr v
      let (_, k) ← expectInt (← getVal fr i)
      pure (.val (.ref ⟨vw.loc.root, vw.loc.path ++ [vw.start + k.toNat]⟩))
    | .push r v org => do
      let l ← expectRef (← getVal fr r)
      let x ← getVal fr v
      match org with
      | some _ => checkCapacityAtOrg l 1 org
      | none => pure ()
      let i ← appendLoc l #[x]
      pure (.val (.ref { l with path := l.path ++ [i] }))
    | .pop r org => do
      let l ← expectRef (← getVal fr r)
      let len ← lengthLoc l
      if len == 0 then abortAtOrg .popEmpty org
      else do
        let value ← readLoc { l with path := l.path ++ [len - 1] }
        truncateLoc l (len - 1)
        pure (.val value)
    | .structLit t vs => do
      let .structT sid _ := t | fault .shape
      pure (.val (.record sid (← mapList (getVal fr) vs).toArray))
    | .fieldAddr owner i => do
      let l ← expectRef (← getVal fr owner)
      pure (.val (.ref { l with path := l.path ++ [i] }))
    | .arrLit t vs => do
      let xs ← mapList (getVal fr) vs
      pure (.val (← expectArrayLit t xs.toArray))
    | .arrFill t v => do
      let k ← expectFixedCount t
      let x ← getVal fr v
      pure (.val (.fixed (Array.replicate k x)))

    | .call .. => fault .unbound

/-- Enter block `b` of `fn`: bind its parameters to `args` and give its
instructions. -/
def enterBlock (fn : Func) (fr : Frame) (b : BlockId) (args : List RVal) : M (List Inst × Frame) :=
  match fn.blocks[b]? with
  | none => fault .unbound
  | some blk =>
    if blk.params.length = args.length then do
      let fr' ← bindParams fr blk.params args
      pure (blk.insts, fr')
    else fault .arity

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
      let fr : Frame := ⟨act, [], {}, depth⟩
      let (insts, fr') ← enterBlock fn fr 0 (vals.map RVal.val)
      exec n ⟨cfg, fn⟩ fr' insts
    else fault .arity

/-- Run the instructions of the current block; a branch enters the next block
and continues in the same call, so a loop is one tail-recursive function. -/
def exec : Nat → FnCtx → Frame → List Inst → M Val
  | 0, _, _, _ => timeout
  | _ + 1, _, _, [] => fault .flow
  | n + 1, cx, fr, i :: rest =>
    match i with
    | .def r op => do
      let x ← execOp n cx fr op
      let fr' ← setCell fr r x
      exec n cx fr' rest
    | .eff e => do
      let fr' ← execEff cx.fn fr e
      exec n cx fr' rest
    | .term (.br b args) => do
      let vals ← mapList (getCell fr) args
      let (insts, fr') ← enterBlock cx.fn fr b vals
      exec n cx fr' insts
    | .term (.condbr c tb targs eb eargs) => do
      if (← expectBool (← getVal fr c)) then
        let vals ← mapList (getCell fr) targs
        let (insts, fr') ← enterBlock cx.fn fr tb vals
        exec n cx fr' insts
      else
        let vals ← mapList (getCell fr) eargs
        let (insts, fr') ← enterBlock cx.fn fr eb vals
        exec n cx fr' insts
    | .term (.ret vs _) =>
      match vs with
      | [] => pure .unit
      | [v] => getVal fr v
      | _ => fault .shape
    | .term (.abort k org) => abortAtOrg k org
    | .term (.exit v _) => do
      let (_, code) ← expectInt (← getVal fr v)
      M.stop (.exit code)
    | .term .unreachable => fault .flow

/-- One instruction that defines a value. Only a call needs fuel: every other
operation is `execPure`, however little fuel remains. -/
def execOp : Nat → FnCtx → Frame → Op → M RVal
  | n, cx, fr, op =>
    match op with
    | .call f args _ =>
      match n with
      | 0 => timeout
      | n + 1 => do
        let vals ← mapList (getVal fr) args
        pure (.val (← callFn n cx.cfg fr.depth f vals))
    | _ => execPure cx fr op

end

/-- Initialize the globals in table order, each by an activation of its
initializer function at depth 0. -/
def initGlobals (fuel : Nat) (cfg : GCfg) : List GlobalId → M Unit
  | [] => pure ()
  | g :: rest => do
    let init ← lookupInit cfg g
    let v ← enterFn fuel cfg 0 init []
    bindRoot (.global g) v
    initGlobals fuel cfg rest

/-- Initialize the globals, then run the entry at depth 1. -/
def runModule (fuel : Nat) (cfg : GCfg) : M Unit := do
  initGlobals fuel cfg (List.range cfg.mod.globals.size)
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
