import Goose.GIR.Typing

/-!
Lowering of a Core module to GIR-H: the reference for how every Core form
becomes instructions, and for the numbering of every table.

The lowering reads implementations, never a context's root annotations; a
context contributes only the implementation index of a call and of the entry.

## Numbering

* Functions are the implementations, in order; a global's initializer is a
  function of its own held by the global. Globals, slots (one per variable, same
  number), scopes (one per Core block, same number), the file table and the
  origin table are those of the Core module.
* Blocks and values are numbered in the order the lowering creates them.
  `newBlock` takes the next block id and then the next value ids for the
  block's parameters, in order. An instruction that defines a value takes the
  next value id when it is emitted. Block 0 is the entry; its parameters are the
  function's parameters.
* The lowering emits into one current block. A terminator closes the current
  block and leaves no current block. While there is no current block nothing is
  emitted, no block is created and statements are skipped, so there is no
  unreachable block and no instruction after a terminator.

## Scheme

Evaluation order is instruction order. A statement or expression is lowered
in the order Core evaluates its parts:

* `read p` is the address of `p` then `load`; `ref m p` is that address,
  frozen when `m` is read-only and the address is mutable; `elem v i` is the
  view of `v`, the index, then `array.index.checked`.
* `and a b` evaluates `a`; a conditional branch goes to the block that
  evaluates `b` or to a join whose parameter is `a`'s value (`or` mirrors it).
* `ifE`/`ifS` branch on the condition. The join block is created after both
  arms have been lowered, only if an arm can reach it, and each arm that reaches
  it gets its branch to the join appended then.
* `while` branches back to a header that holds the condition. `forRange`
  computes both bounds before the loop; the header's parameter is the counter,
  and the increment is emitted at the end of the body and at each `continue`.
  `forEach` samples its source once; a source that is a grow-only array has its
  length read again by `array.len` in the header, any other source keeps the
  length of the view taken before the loop.
* Every Core block enters its scope, binds the variables its construct
  declares, runs its statements, evaluates its value and leaves its scope.
  `ret` leaves every scope entered, `break` and `continue` the scopes entered
  since the loop began; `abort` and `exit` leave none.

## Expected correspondence

For the simulation proof, a Core state and a GIR state correspond when:

* the stores are equal, with the root of a slot the root of its variable;
* the traces are equal;
* the activation, scope-instance and fresh-id counters are equal;
* the GIR frame's entered scopes are the Core environment's open blocks, in the
  same order and with the same instances;
* every value the lowering has defined so far holds the Core value of the
  expression it was lowered from, and the Core environment's variables are the
  contents of their slots.

A lowered statement or expression is entered with a current block and its
values defined so far. It ends in one of three ways: in terminators that stand
for the Core flow (`ret`, `break`, `continue`, an abort or an exit), each after
the `scope.leave`s that Core's block exits perform; by falling through, leaving
the current block for the next fragment, with the Core result in the value the
fragment returns; or with no current block, when every path ended in a
terminator. The statement is proved by induction on Core's fuel, a fragment at a
time, from `eval n p m = done o t` to `run k p (lower m) = done o t` for some
`k`.
-/

namespace Goose.Lower

open Goose.Core
open Goose.GIR (ValueId BlockId SlotId ScopeId FnId VTy Bnd PrintPart Op Effect Term Inst)

/-! ### Builder -/

structure BlockB where
  params : List (ValueId × VTy)
  insts : Array Inst

/-- The innermost loop and how a `continue` leaves it. -/
inductive ContKind
  /-- Branch to the header, which tests the condition again. -/
  | jump (header : BlockId)
  /-- Increment the counter, then branch to the header. -/
  | next (header : BlockId) (t : IntTy) (counter : ValueId)

structure LoopCtx where
  /-- Number of scopes entered when the loop began. -/
  depth : Nat
  breakTo : BlockId
  cont : ContKind

structure LS where
  blocks : Array BlockB
  /-- Type of every value so far, indexed by value id. -/
  vals : Array (Option VTy)
  cur : Option BlockId
  /-- Scopes entered, innermost first. -/
  stack : List ScopeId

/-- What the lowering of one function reads: the Core module's tables, the
function's slots and the parameter and result types of every implementation. -/
structure LEnv where
  mod : Module
  slots : Array GIR.Slot
  vars : Array LocalVar
  globals : Array (Ty × VarKind)
  sigs : Array (List Ty × List Ty)

abbrev B := ReaderT LEnv (StateM LS)

def tyEnv (env : LEnv) (s : LS) : GIR.TyEnv :=
  ⟨env.slots, env.globals, env.sigs, s.vals⟩

def curBlock : B (Option BlockId) := do pure (← get).cur

def isLive : B Bool := do pure (← curBlock).isSome

def setCur (b : Option BlockId) : B Unit := modify fun s => { s with cur := b }

def pushInst (b : BlockId) (i : Inst) : B Unit :=
  modify fun s => { s with blocks := s.blocks.modify b fun blk => { blk with insts := blk.insts.push i } }

def valTy (v : ValueId) : B VTy := do
  match (← get).vals[v]? with
  | some (some t) => pure t
  | _ => pure (.data .unit)

/-- The integer type of a value, `i64` for a value that has none. -/
def intTyOf (v : ValueId) : B IntTy := do
  match (← valTy v) with
  | .data (.int t) => pure t
  | _ => pure .i64

/-- Define a value in the current block. Nothing is emitted, and 0 is
returned, when there is no current block. -/
def emitDef (op : Op) : B ValueId := do
  let s ← get
  let env ← read
  match s.cur with
  | none => pure 0
  | some b =>
    let ty := ((op.resultTy (tyEnv env s)).toOption).getD (.data .unit)
    let v := s.vals.size
    modify fun s => { s with vals := s.vals.push (some ty) }
    pushInst b (.def v op)
    pure v

def emitEffect (e : Effect) : B Unit := do
  match (← curBlock) with
  | none => pure ()
  | some b => pushInst b (.eff e)

/-- Close the current block with a terminator. -/
def emitTerm (t : Term) : B Unit := do
  match (← curBlock) with
  | none => pure ()
  | some b =>
    pushInst b (.term t)
    setCur none

/-- Append a terminator to a block that is no longer current. -/
def patchTerm (b : BlockId) (t : Term) : B Unit := pushInst b (.term t)

/-- Create a block; its parameters take the next value ids. -/
def newBlock (tys : List VTy) : B (BlockId × List ValueId) := do
  let s ← get
  let b := s.blocks.size
  let ids := (List.range tys.length).map (s.vals.size + ·)
  set { s with
    blocks := s.blocks.push ⟨ids.zip tys, #[]⟩
    vals := tys.foldl (fun a t => a.push (some t)) s.vals }
  pure (b, ids)

/-- Run `k` with the current block, or yield `dflt` when there is none. -/
def whenLive (dflt : α) (k : BlockId → B α) : B α := do
  match (← curBlock) with
  | none => pure dflt
  | some b => k b

/-- Leave, innermost first, every scope entered beyond the first `depth`. -/
def leaveTo (depth : Nat) : B Unit := do
  let st := (← get).stack
  for sc in st.take (st.length - depth) do
    emitEffect (.leave sc)

/-- A mutable address frozen to read-only when a read-only reference is wanted. -/
def freezeTo (m : Mutability) (r : ValueId) : B ValueId := do
  match m, (← valTy r) with
  | .readOnly, .data (.ref .mutable _) => emitDef (.refFreeze r)
  | _, _ => pure r

def pushScope (sc : ScopeId) : B Unit := modify fun s => { s with stack := sc :: s.stack }

def popScope : B Unit := modify fun s => { s with stack := s.stack.drop 1 }

def implOfContext (c : ContextId) : B FnId := do
  pure (((← read).mod.contexts[c]?).map (·.impl) |>.getD 0)

/-! ### Expressions, places, views and statements -/

/-- Whether a view comes from a grow-only array, whose length a loop reads again. -/
def growOwner (r : ValueId) : B Bool := do
  match (← valTy r) with
  | .data (.ref _ (.grow _)) => pure true
  | _ => pure false

/-- The join of the two arms of an `if` expression: each arm that still has a
current block branches to it with its value. -/
def joinValue (endT : Option BlockId) (vt : ValueId) (endF : Option BlockId) (vf : ValueId) :
    B ValueId := do
  match endT, endF with
  | none, none =>
    setCur none
    pure 0
  | _, _ =>
    let live := (endT.map fun b => (b, vt)).toList ++ (endF.map fun b => (b, vf)).toList
    let ty ← valTy (live.headD (0, 0)).2
    let (jb, js) ← newBlock [ty]
    for (b, v) in live do
      patchTerm b (.br jb [v])
    setCur (some jb)
    pure (js.headD 0)

/-- The join of the two arms of an `if` statement, created only if an arm
reaches it. -/
def joinArms (endT endF : Option BlockId) : B Unit := do
  match endT, endF with
  | none, none => setCur none
  | _, _ =>
    let (jb, _) ← newBlock []
    for b in endT.toList ++ endF.toList do
      patchTerm b (.br jb [])
    setCur (some jb)

/-- The right operand of `and`/`or`, whose left value is `x`; `rhs` lowers it. -/
def shortCircuit (isAnd : Bool) (x : ValueId) (rhs : B ValueId) : B ValueId :=
  whenLive 0 fun _ => do
    let (rb, _) ← newBlock []
    let (jb, js) ← newBlock [.data .bool]
    if isAnd then emitTerm (.condbr x rb [] jb [x])
    else emitTerm (.condbr x jb [x] rb [])
    setCur (some rb)
    let y ← rhs
    emitTerm (.br jb [y])
    setCur (some jb)
    pure (js.headD 0)

mutual

def lowerExpr : Expr → B ValueId
  | .lit t n => emitDef (.constInt t n)
  | .bool b => emitDef (.constBool b)
  | .read p => do
    let r ← lowerPlace p
    emitDef (.load r)
  | .ref m p => do
    let r ← lowerPlace p
    freezeTo m r
  | .slice m v lo hi org => do
    let vw ← lowerView v
    let l ← lowerBound lo
    let h ← lowerBound hi
    emitDef (.viewSlice m vw l h (some org))
  | .len v => do
    let vw ← lowerView v
    emitDef (.viewLen vw)
  | .un op e org => do
    let a ← lowerExpr e
    emitDef (.un op (← intTyOf a) a (some org))
  | .bin op a b org => do
    let x ← lowerExpr a
    let y ← lowerExpr b
    emitDef (.bin op (← intTyOf x) x y (some org))
  | .cmp op a b => do
    let x ← lowerExpr a
    let y ← lowerExpr b
    match (← valTy x) with
    | .data (.int t) => emitDef (.cmp op t x y)
    | _ => emitDef (.boolCmp op x y)
  | .and a b => do
    let x ← lowerExpr a
    shortCircuit true x (lowerExpr b)
  | .or a b => do
    let x ← lowerExpr a
    shortCircuit false x (lowerExpr b)
  | .not e => do
    emitDef (.boolNot (← lowerExpr e))
  | .conv k target e org => do
    let a ← lowerExpr e
    let src ← intTyOf a
    let dst := match target with
      | .int d => d
      | _ => src
    emitDef (.conv k src dst a (some org))
  | .call c args org => do
    let vs ← lowerArgs args
    let f ← implOfContext c
    emitDef (.call f vs (some org))
  | .push owner e => do
    let r ← lowerPlace owner
    let v ← lowerExpr e
    emitDef (.push r v none)
  | .ifE c t f => do
    let cv ← lowerExpr c
    whenLive 0 fun _ => do
      let (tb, _) ← newBlock []
      let (eb, _) ← newBlock []
      emitTerm (.condbr cv tb [] eb [])
      setCur (some tb)
      let vt ← lowerBlock none [] true t
      let endT ← curBlock
      setCur (some eb)
      let vf ← lowerBlock none [] true f
      let endF ← curBlock
      joinValue endT vt endF vf
  | .blockE b => lowerBlock none [] true b
  | .arrLit t es => do
    let vs ← lowerExprs es
    emitDef (.arrLit t vs)
  | .fill t e => do
    let v ← lowerExpr e
    emitDef (.arrFill t v)

def lowerExprs : List Expr → B (List ValueId)
  | [] => pure []
  | e :: rest => do
    let v ← lowerExpr e
    let vs ← lowerExprs rest
    pure (v :: vs)

def lowerArg : Arg → B ValueId
  | .byVal e => lowerExpr e
  | .byRef m p => do
    let r ← lowerPlace p
    freezeTo m r

def lowerArgs : List Arg → B (List ValueId)
  | [] => pure []
  | a :: rest => do
    let v ← lowerArg a
    let vs ← lowerArgs rest
    pure (v :: vs)

def lowerPlace : Place → B ValueId
  | .var x => emitDef (.slotAddr x)
  | .global g => emitDef (.globalAddr g)
  | .deref e => lowerExpr e
  | .elem v i org => do
    let vw ← lowerView v
    let iv ← lowerExpr i
    emitDef (.indexChecked vw iv (some org))

def lowerView : View → B ValueId
  | .of p => do
    let r ← lowerPlace p
    emitDef (.snapshot r)
  | .val e => do
    let s ← lowerExpr e
    emitDef (.sliceView s)

def lowerBound : Bound → B Bnd
  | .omitted => pure .omitted
  | .expr e => do pure (.val (← lowerExpr e))
  | .fromEnd e => do pure (.fromEnd (← lowerExpr e))

/-- A Core block: enter its scope, bind `pre`, run the statements, evaluate the
value (a unit when one is `want`ed and the block has none) and leave the scope.
Yields the value; 0 when nothing was produced. -/
def lowerBlock (lc : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId)) (want : Bool) :
    Block → B ValueId
  | .mk sc stmts value => do
    emitEffect (.enter sc)
    pushScope sc
    for (s, v, o) in pre do
      emitEffect (.slotInit s v (some o))
    lowerStmts lc stmts
    let r ← match value with
      | some e => lowerExpr e
      | none => if want then emitDef .constUnit else pure 0
    emitEffect (.leave sc)
    popScope
    pure r

def lowerStmts (lc : Option LoopCtx) : List Stmt → B Unit
  | [] => pure ()
  | s :: rest => do
    if (← isLive) then
      lowerStmt lc s
      lowerStmts lc rest

def lowerPrintArgs : List PrintArg → B (List PrintPart)
  | [] => pure []
  | .text s :: rest => do
    let ps ← lowerPrintArgs rest
    pure (.text s :: ps)
  | .expr e :: rest => do
    let v ← lowerExpr e
    let ps ← lowerPrintArgs rest
    pure (.val v :: ps)

def lowerStmt (lc : Option LoopCtx) : Stmt → B Unit
  | .letS x e org => do
    let v ← lowerExpr e
    emitEffect (.slotInit x v (some org))
  | .assign p e org => do
    let r ← lowerPlace p
    let v ← lowerExpr e
    emitEffect (.store r v (some org))
  | .assignOp op p e org => do
    let r ← lowerPlace p
    let old ← emitDef (.load r)
    let rhs ← lowerExpr e
    let res ← emitDef (.bin op (← intTyOf old) old rhs (some org))
    emitEffect (.store r res (some org))
  | .rebind x e org => do
    let v ← lowerExpr e
    let r ← emitDef (.slotAddr x)
    emitEffect (.store r v (some org))
  | .expr e _ => do
    let _ ← lowerExpr e
    pure ()
  | .append owner src org => do
    let r ← lowerPlace owner
    let vw ← lowerView src
    emitEffect (.append r vw (some org))
  | .ifS c t f _ => do
    let cv ← lowerExpr c
    whenLive () fun _ => do
      match f with
      | none =>
        let (tb, _) ← newBlock []
        let (jb, _) ← newBlock []
        emitTerm (.condbr cv tb [] jb [])
        setCur (some tb)
        let _ ← lowerBlock lc [] false t
        emitTerm (.br jb [])
        setCur (some jb)
      | some fb =>
        let (tb, _) ← newBlock []
        let (eb, _) ← newBlock []
        emitTerm (.condbr cv tb [] eb [])
        setCur (some tb)
        let _ ← lowerBlock lc [] false t
        let endT ← curBlock
        setCur (some eb)
        let _ ← lowerBlock lc [] false fb
        let endF ← curBlock
        joinArms endT endF
  | .while c body _ => do
    let (hb, _) ← newBlock []
    emitTerm (.br hb [])
    setCur (some hb)
    let cv ← lowerExpr c
    whenLive () fun _ => do
      let depth := (← get).stack.length
      let (bb, _) ← newBlock []
      let (xb, _) ← newBlock []
      emitTerm (.condbr cv bb [] xb [])
      setCur (some bb)
      let _ ← lowerBlock (some ⟨depth, xb, .jump hb⟩) [] false body
      emitTerm (.br hb [])
      setCur (some xb)
  | .forRange x lo hi body org => do
    let a ← lowerExpr lo
    let b ← lowerExpr hi
    whenLive () fun _ => do
      let t ← intTyOf a
      let depth := (← get).stack.length
      let (hb, hs) ← newBlock [.data (.int t)]
      let i := hs.headD 0
      emitTerm (.br hb [a])
      setCur (some hb)
      let c ← emitDef (.cmp .lt t i b)
      let (bb, _) ← newBlock []
      let (xb, _) ← newBlock []
      emitTerm (.condbr c bb [] xb [])
      setCur (some bb)
      let _ ← lowerBlock (some ⟨depth, xb, .next hb t i⟩) [(x, i, org)] false body
      if (← isLive) then
        let n ← emitDef (.next t i)
        emitTerm (.br hb [n])
      setCur (some xb)
  | .forEach x idx v byRef body org => do
    -- The source is sampled once. An owner that is a grow-only array is kept by
    -- address so that its length can be read again.
    let (owner, vw) ← match v with
      | .of p => do
        let r ← lowerPlace p
        let vw ← emitDef (.snapshot r)
        pure (some r, vw)
      | .val e => do
        let s ← lowerExpr e
        let vw ← emitDef (.sliceView s)
        pure (none, vw)
    let regrow ← match owner with
      | some r => growOwner r
      | none => pure false
    let sampled ← if regrow then pure 0 else emitDef (.viewLen vw)
    let startAt ← emitDef (.constInt .i64 0)
    whenLive () fun _ => do
      let depth := (← get).stack.length
      let (hb, hs) ← newBlock [.data (.int .i64)]
      let i := hs.headD 0
      emitTerm (.br hb [startAt])
      setCur (some hb)
      let n ← if regrow then emitDef (.arrayLen (owner.getD 0)) else pure sampled
      let c ← emitDef (.cmp .lt .i64 i n)
      let (bb, _) ← newBlock []
      let (xb, _) ← newBlock []
      emitTerm (.condbr c bb [] xb [])
      setCur (some bb)
      let elem ← emitDef (.refElem vw i)
      let ev ← if byRef then
          match (← read).vars[x]? with
          | some lv =>
            match lv.ty with
            | .ref m _ => freezeTo m elem
            | _ => pure elem
          | none => pure elem
        else emitDef (.load elem)
      let pre := (x, ev, org) :: (match idx with
        | some j => [(j, i, org)]
        | none => [])
      let _ ← lowerBlock (some ⟨depth, xb, .next hb .i64 i⟩) pre false body
      if (← isLive) then
        let nx ← emitDef (.next .i64 i)
        emitTerm (.br hb [nx])
      setCur (some xb)
  | .ret e org => do
    let vs ← match e with
      | some e => do pure [← lowerExpr e]
      | none => pure []
    leaveTo 0
    emitTerm (.ret vs (some org))
  | .brk _ => do
    match lc with
    | some l =>
      leaveTo l.depth
      emitTerm (.br l.breakTo [])
    | none => pure ()
  | .cont _ => do
    match lc with
    | some l =>
      leaveTo l.depth
      match l.cont with
      | .jump h => emitTerm (.br h [])
      | .next h t i =>
        let n ← emitDef (.next t i)
        emitTerm (.br h [n])
    | none => pure ()
  | .print args org => do
    let parts ← lowerPrintArgs args
    emitEffect (.print parts (some org))
  | .assertS e org => do
    let cv ← lowerExpr e
    whenLive () fun _ => do
      let (pb, _) ← newBlock []
      let (fb, _) ← newBlock []
      emitTerm (.condbr cv pb [] fb [])
      setCur (some fb)
      emitTerm (.abort .assert (some org))
      setCur (some pb)
  | .abort _ org => emitTerm (.abort .userAbort (some org))
  | .exit e org => do
    let v ← lowerExpr e
    emitTerm (.exit v (some org))

end

/-! ### Scope tree -/

mutual

/-- Every block of an expression with the block that encloses it. -/
def exprScopes (parent : Option Nat) : Expr → List (Nat × Option Nat)
  | .lit .. | .bool _ => []
  | .read p => placeScopes parent p
  | .ref _ p => placeScopes parent p
  | .slice _ v lo hi _ => viewScopes parent v ++ boundScopes parent lo ++ boundScopes parent hi
  | .len v => viewScopes parent v
  | .un _ e _ => exprScopes parent e
  | .bin _ a b _ => exprScopes parent a ++ exprScopes parent b
  | .cmp _ a b => exprScopes parent a ++ exprScopes parent b
  | .and a b => exprScopes parent a ++ exprScopes parent b
  | .or a b => exprScopes parent a ++ exprScopes parent b
  | .not e => exprScopes parent e
  | .conv _ _ e _ => exprScopes parent e
  | .call _ args _ => argsScopes parent args
  | .push p e => placeScopes parent p ++ exprScopes parent e
  | .ifE c t f => exprScopes parent c ++ blockScopes parent t ++ blockScopes parent f
  | .blockE b => blockScopes parent b
  | .arrLit _ es => exprsScopes parent es
  | .fill _ e => exprScopes parent e

def exprsScopes (parent : Option Nat) : List Expr → List (Nat × Option Nat)
  | [] => []
  | e :: rest => exprScopes parent e ++ exprsScopes parent rest

def argsScopes (parent : Option Nat) : List Arg → List (Nat × Option Nat)
  | [] => []
  | .byVal e :: rest => exprScopes parent e ++ argsScopes parent rest
  | .byRef _ p :: rest => placeScopes parent p ++ argsScopes parent rest

def placeScopes (parent : Option Nat) : Place → List (Nat × Option Nat)
  | .var _ | .global _ => []
  | .deref e => exprScopes parent e
  | .elem v i _ => viewScopes parent v ++ exprScopes parent i

def viewScopes (parent : Option Nat) : View → List (Nat × Option Nat)
  | .of p => placeScopes parent p
  | .val e => exprScopes parent e

def boundScopes (parent : Option Nat) : Bound → List (Nat × Option Nat)
  | .omitted => []
  | .expr e | .fromEnd e => exprScopes parent e

def blockScopes (parent : Option Nat) : Block → List (Nat × Option Nat)
  | .mk sc stmts value =>
    (sc, parent) :: (stmtsScopes (some sc) stmts ++ (match value with
      | some e => exprScopes (some sc) e
      | none => []))

def stmtsScopes (parent : Option Nat) : List Stmt → List (Nat × Option Nat)
  | [] => []
  | s :: rest => stmtScopes parent s ++ stmtsScopes parent rest

def printScopes (parent : Option Nat) : List PrintArg → List (Nat × Option Nat)
  | [] => []
  | .text _ :: rest => printScopes parent rest
  | .expr e :: rest => exprScopes parent e ++ printScopes parent rest

def stmtScopes (parent : Option Nat) : Stmt → List (Nat × Option Nat)
  | .letS _ e _ => exprScopes parent e
  | .assign p e _ => placeScopes parent p ++ exprScopes parent e
  | .assignOp _ p e _ => placeScopes parent p ++ exprScopes parent e
  | .rebind _ e _ => exprScopes parent e
  | .expr e _ => exprScopes parent e
  | .append p v _ => placeScopes parent p ++ viewScopes parent v
  | .ifS c t f _ =>
    exprScopes parent c ++ blockScopes parent t ++ (match f with
      | some b => blockScopes parent b
      | none => [])
  | .while c b _ => exprScopes parent c ++ blockScopes parent b
  | .forRange _ lo hi b _ => exprScopes parent lo ++ exprScopes parent hi ++ blockScopes parent b
  | .forEach _ _ v _ b _ => viewScopes parent v ++ blockScopes parent b
  | .ret e _ => (match e with
      | some e => exprScopes parent e
      | none => [])
  | .brk _ | .cont _ => []
  | .print args _ => printScopes parent args
  | .assertS e _ => exprScopes parent e
  | .abort .. => []
  | .exit e _ => exprScopes parent e

end

/-- The scope table: the parent of every block number that occurs. -/
def scopeTable (pairs : List (Nat × Option Nat)) : Array (Option ScopeId) :=
  let n := pairs.foldl (fun m p => max m (p.1 + 1)) 0
  pairs.foldl (fun a p => a.set! p.1 p.2) (Array.replicate n none)

/-! ### Functions and the module -/

def initState : LS := ⟨#[], #[], none, []⟩

def finishBlocks (blocks : Array BlockB) : Array GIR.Block :=
  blocks.map fun b => ⟨b.params, b.insts.toList⟩

def tyOfVar (impl : Impl) (x : VarId) : Ty :=
  match impl.vars[x]? with
  | some lv => lv.ty
  | none => .unit

def lowerEnv (m : Module) (vars : Array LocalVar) : LEnv :=
  { mod := m
    vars
    slots := vars.mapIdx fun i lv => ⟨lv.ty, lv.kind, lv.scope, i⟩
    globals := m.globals.map fun g => (g.ty, g.kind)
    sigs := m.impls.map fun impl => (impl.params.toList.map (tyOfVar impl ·.var), impl.results.toList) }

/-- Lower an implementation. -/
def lowerImpl (m : Module) (impl : Impl) : GIR.Func :=
  let env := lowerEnv m impl.vars
  let act : B Unit := do
    let (b0, ps) ← newBlock (impl.params.toList.map fun p => .data (tyOfVar impl p.var))
    setCur (some b0)
    let pre := (impl.params.toList.zip ps).map fun (p, v) =>
      (p.var, v, (impl.vars[p.var]?.map (·.org)).getD 0)
    let v ← lowerBlock none pre false impl.body
    if (← isLive) then
      emitTerm (.ret (if impl.body.value.isSome then [v] else []) none)
  let ((), s) := (act.run env).run initState
  { name := impl.name
    params := impl.params.toList.map fun p => tyOfVar impl p.var
    results := impl.results.toList
    slots := env.slots
    scopes := scopeTable (blockScopes none impl.body)
    blocks := finishBlocks s.blocks
    summary := impl.summary
    org := impl.vars[0]?.map (·.org) }

/-- Lower a global's initializer to a function that returns the value. -/
def lowerGlobal (m : Module) (g : Global) : GIR.Global :=
  let env := lowerEnv m #[]
  let act : B Unit := do
    let (b0, _) ← newBlock []
    setCur (some b0)
    let v ← lowerExpr g.init
    emitTerm (.ret [v] (some g.org))
  let ((), s) := (act.run env).run initState
  { name := g.name
    ty := g.ty
    kind := g.kind
    init :=
      { name := g.name
        params := []
        results := [g.ty]
        slots := #[]
        scopes := scopeTable (exprScopes none g.init)
        blocks := finishBlocks s.blocks
        summary := .unknown
        org := some g.org }
    org := g.org }

/-- The reference lowering of a Core module. -/
def lower (m : Module) : GIR.Module :=
  { files := m.files
    globals := m.globals.map (lowerGlobal m)
    funcs := m.impls.map (lowerImpl m)
    entry := ((m.contexts[m.entry]?).map (·.impl)).getD 0
    origins := m.origins }

end Goose.Lower
