import Goose.Core.Roots
import Goose.Core.Scopes
import Goose.GIR.Typing

/-!
Lowering of a Core module to GIR-H: the reference for how every Core form
becomes instructions, and for the numbering of every table.

The lowering reads implementations for executable code and attaches each
context's own root annotations to its function. Calls and entry retain their
Core context indices.

## Numbering

* Functions are the contexts, in order; a global's initializer is a
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
function's slots and the parameter and result types of every context. -/
structure LEnv where
  mod : Module
  slots : Array GIR.Slot
  vars : Array LocalVar
  globals : Array (Ty × VarKind)
  sigs : Array (List Ty × List Ty)
  results : List Ty

/-- The builder: reads the function's tables and threads the state. A plain
function type, so that its `do` blocks unfold by definition. -/
def B (α : Type) : Type := LEnv → LS → α × LS

instance : Monad B where
  pure a := fun _ s => (a, s)
  bind x f := fun e s => match x e s with
    | (a, s1) => f a e s1

instance : MonadReaderOf LEnv B where
  read := fun e s => (e, s)

instance : MonadStateOf LS B where
  get := fun _ s => (s, s)
  set s' := fun _ _ => ((), s')
  modifyGet f := fun _ s => f s

def tyEnv (env : LEnv) (s : LS) : GIR.TyEnv :=
  { slots := env.slots
    globals := env.globals
    sigs := env.sigs
    vals := s.vals
    structs := env.mod.structs
    profile := env.mod.profile
    contentsWritable := fun v =>
      let f : GIR.Func :=
        { name := ""
          params := []
          results := []
          slots := env.slots
          scopes := #[]
          blocks := s.blocks.map fun b => ⟨b.params, b.insts.toList⟩
          summary := .unknown
          org := none }
      (f.permissionsFromTables (env.globals.map (·.2)) env.mod.structs s.vals)[v]?.map (·.2) }

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

/-- Initialize each slot with its value. -/
def initSlots : List (SlotId × ValueId × OriginId) → B Unit
  | [] => pure ()
  | (s, v, o) :: rest => do
    emitEffect (.slotInit s v (some o))
    initSlots rest

/-- Run `k` with the current block, or yield `dflt` when there is none. -/
def whenLive (dflt : α) (k : BlockId → B α) : B α := do
  match (← curBlock) with
  | none => pure dflt
  | some b => k b

/-- Leave, innermost first, every scope entered beyond the first `depth`. -/
def leaveAll : List ScopeId → B Unit
  | [] => pure ()
  | sc :: rest => do
    emitEffect (.leave sc)
    leaveAll rest

def leaveTo (depth : Nat) : B Unit := do
  let st := (← get).stack
  leaveAll (st.take (st.length - depth))

/-- A mutable address frozen to read-only when a read-only reference is wanted. -/
def freezeTo (m : Mutability) (r : ValueId) : B ValueId := do
  match m, (← valTy r) with
  | .readOnly, .data (.ref .mutable _) => emitDef (.refFreeze r)
  | _, _ => pure r

def borrowTo (m : Mutability) (r : ValueId) : B ValueId := do
  match m, (← read).mod.profile, (← valTy r) with
  | .mutable, .shrink, .data (.ref .mutable (.grow _))
  | .mutable, .shrink, .data (.ref .mutable (.growshrink _)) =>
    emitDef (.ownerBorrow r)
  | _, _, _ => freezeTo m r

def coerceTo (target : Ty) (r : ValueId) (org : OriginId) : B ValueId := do
  match target, (← valTy r) with
  | .ref .readOnly _, .data (.ref .mutable _) => emitDef (.refFreeze r)
  | .slice .readOnly _, .data (.slice .mutable _) =>
    let view ← emitDef (.sliceView r)
    emitDef (.viewSlice .readOnly view .omitted .omitted (some org))
  | _, _ => pure r

def coerceSlot (slot : SlotId) (value : ValueId) (org : OriginId) : B ValueId := do
  match (← read).slots[slot]? with
  | some destination => coerceTo destination.ty value org
  | none => pure value

def coerceResult (value : ValueId) (org : OriginId) : B ValueId := do
  match (← read).results.head? with
  | some destination => coerceTo destination value org
  | none => pure value

def pushScope (sc : ScopeId) : B Unit := modify fun s => { s with stack := sc :: s.stack }

def popScope : B Unit := modify fun s => { s with stack := s.stack.drop 1 }

/-- Run `k` with `sc` pushed on the stack of entered scopes. -/
def inScope (sc : ScopeId) (k : B α) : B α := do
  pushScope sc
  let r ← k
  popScope
  pure r

/-! ### Expressions, places, views and statements -/

/-- Whether a view comes from a resizable owner whose length a loop reads again. -/
def growOwner (r : ValueId) : B Bool := do
  match (← valTy r) with
  | .data (.ref _ t) => pure (match t with | .grow _ | .growshrink _ => true | _ => false)
  | _ => pure false

/-- Branch on `cv` to two blocks created now, in this order; closes the current
block. Every two-way branch of the lowering has this shape. -/
def fork (cv : ValueId) : B (BlockId × BlockId) := do
  let (tb, _) ← newBlock []
  let (eb, _) ← newBlock []
  emitTerm (.condbr cv tb [] eb [])
  pure (tb, eb)

/-- Whether the owner of a `for` loop's source is resizable, so its length is
read again each time through the loop. -/
def regrowOf : Option ValueId → B Bool
  | some r => growOwner r
  | none => pure false

/-- The length a `for` loop samples before it starts; none for a grow-only owner. -/
def eachSampled (regrow : Bool) (vw : ValueId) : B ValueId :=
  if regrow then pure 0 else emitDef (.viewLen vw)

/-- The length a `for` loop tests against: read again for a grow-only owner, else the sampled one. -/
def eachLen (regrow : Bool) (owner : Option ValueId) (sampled : ValueId) : B ValueId :=
  if regrow then emitDef (.arrayLen (owner.getD 0)) else pure sampled

/-- The value a `for` loop's variable receives from the element at address `elem`: the element
itself, or its address, frozen when the variable is a read-only reference. -/
def eachElemValue (x : VarId) (byRef : Bool) (elem : ValueId) : B ValueId := do
  if byRef then
    match (← read).vars[x]? with
    | some lv =>
      match lv.ty with
      | .ref m _ => borrowTo m elem
      | _ => pure elem
    | none => pure elem
  else emitDef (.load elem)

/-- Append to each block a branch to `jb` passing its value. -/
def patchBrs (jb : BlockId) : List (BlockId × ValueId) → B Unit
  | [] => pure ()
  | (b, v) :: rest => do
    patchTerm b (.br jb [v])
    patchBrs jb rest

/-- Append to each block a branch to `jb` passing nothing. -/
def patchBrs0 (jb : BlockId) : List BlockId → B Unit
  | [] => pure ()
  | b :: rest => do
    patchTerm b (.br jb [])
    patchBrs0 jb rest

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
    patchBrs jb live
    setCur (some jb)
    pure (js.headD 0)

/-- The join of the two arms of an `if` statement, created only if an arm
reaches it. -/
def joinArms (endT endF : Option BlockId) : B Unit := do
  match endT, endF with
  | none, none => setCur none
  | _, _ =>
    let (jb, _) ← newBlock []
    patchBrs0 jb (endT.toList ++ endF.toList)
    setCur (some jb)

/-- The branch of a short-circuit operator whose left value is `x`: to the block that evaluates
the right operand, or to the join, whose one parameter is the result. Returns both blocks and the
parameter. -/
def scFork (isAnd : Bool) (x : ValueId) : B (BlockId × BlockId × ValueId) := do
  let (rb, _) ← newBlock []
  let (jb, js) ← newBlock [.data .bool]
  if isAnd then emitTerm (.condbr x rb [] jb [x])
  else emitTerm (.condbr x jb [x] rb [])
  pure (rb, jb, js.headD 0)

/-- The right operand of `and`/`or`, whose left value is `x`; `rhs` lowers it. -/
def shortCircuit (isAnd : Bool) (x : ValueId) (rhs : B ValueId) : B ValueId :=
  whenLive 0 fun _ => do
    let (rb, jb, p) ← scFork isAnd x
    setCur (some rb)
    let y ← rhs
    emitTerm (.br jb [y])
    setCur (some jb)
    pure p

/-- The conditional branch of a loop header on `cv`, the body and the exit. `body` lowers the loop's
body given the number of scopes entered at the loop and the exit block; `back` runs when the body
falls through. -/
def loopBody (cv : ValueId) (body : Nat → BlockId → B ValueId) (back : B Unit) : B Unit := do
  let depth := (← get).stack.length
  let (bb, xb) ← fork cv
  setCur (some bb)
  let _ ← body depth xb
  back
  setCur (some xb)

/-- The branch back to the header of a counting loop: the counter plus one, unless every path of
the body ended. -/
def rangeBack (t : IntTy) (i : ValueId) (hb : BlockId) : B Unit := do
  if (← isLive) then
    let n ← emitDef (.next t i)
    emitTerm (.br hb [n])

/-- A `while` loop from its header, which is the current block and holds nothing yet. -/
def lowerWhile (hb : BlockId) (cond : B ValueId) (body : Nat → BlockId → B ValueId) : B Unit := do
  let cv ← cond
  whenLive () fun _ => loopBody cv body (emitTerm (.br hb []))

/-- A counting loop from its header, whose parameter `i` is the counter and whose bound is `b`. -/
def lowerRange (t : IntTy) (i b : ValueId) (hb : BlockId) (body : Nat → BlockId → B ValueId) :
    B Unit := do
  let c ← emitDef (.cmp .lt t i b)
  loopBody c body (rangeBack t i hb)

/-- A `for` loop over a sampled run from its header, whose parameter `i` is the index. -/
def lowerEach (regrow : Bool) (owner : Option ValueId) (sampled : ValueId) (hb : BlockId)
    (i : ValueId) (body : Nat → BlockId → B ValueId) : B Unit := do
  let n ← eachLen regrow owner sampled
  let c ← emitDef (.cmp .lt .i64 i n)
  loopBody c body (rangeBack .i64 i hb)

mutual

def lowerExpr : Expr → B ValueId
  | .structLit t es => do
    let vs ← lowerExprs es
    emitDef (.structLit t vs)
  | .lit t n => emitDef (.constInt t n)
  | .bool b => emitDef (.constBool b)
  | .read p => do
    let r ← lowerPlace p
    emitDef (.load r)
  | .ref m p => do
    let r ← lowerPlace p
    borrowTo m r
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
    let r ← emitDef (.call c vs (some org))
    if (← read).mod.noReturn c then emitTerm .unreachable
    pure r
  | .push owner e org => do
    let r ← lowerPlace owner
    let v ← lowerExpr e
    emitDef (.push r v org)
  | .pop owner org => do
    let r ← lowerPlace owner
    emitDef (.pop r (some org))
  | .ifE c t f => do
    let cv ← lowerExpr c
    whenLive 0 fun _ => do
      let (tb, eb) ← fork cv
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
    borrowTo m r

def lowerArgs : List Arg → B (List ValueId)
  | [] => pure []
  | a :: rest => do
    let v ← lowerArg a
    let vs ← lowerArgs rest
    pure (v :: vs)

def lowerPlace : Place → B ValueId
  | .field owner i => do
    let r ← lowerPlace owner
    emitDef (.fieldAddr r i)
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
    emitDef (.snapshot (match p with | .var _ | .global _ => .owner | _ => .borrowed) r)
  | .val e => do
    let s ← lowerExpr e
    emitDef (.sliceView s)

def lowerBound : Bound → B Bnd
  | .omitted => pure .omitted
  | .expr e => do pure (.val (← lowerExpr e))
  | .fromEnd e => do pure (.fromEnd (← lowerExpr e))

/-- The source of a `for` loop, sampled once: the address of the owner when the source is a place,
and the view. -/
def lowerEachSource : View → B (Option ValueId × ValueId)
  | .of p => do
    let r ← lowerPlace p
    let vw ← emitDef (.snapshot (match p with | .var _ | .global _ => .owner | _ => .borrowed) r)
    pure (some r, vw)
  | .val e => do
    let s ← lowerExpr e
    let vw ← emitDef (.sliceView s)
    pure (none, vw)

/-- The value a block yields: its value expression, or a unit when one is wanted. -/
def lowerBlockValue (want : Bool) : Option Expr → B ValueId
  | some e => lowerExpr e
  | none => if want then emitDef .constUnit else pure 0

/-- A Core block: enter its scope, bind `pre`, run the statements, evaluate the
value (a unit when one is `want`ed and the block has none) and leave the scope.
Yields the value; 0 when nothing was produced. -/
def lowerBlock (lc : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId)) (want : Bool) :
    Block → B ValueId
  | .mk sc stmts value => do
    emitEffect (.enter sc)
    inScope sc do
      initSlots pre
      lowerStmts lc stmts
      let r ← lowerBlockValue want value
      emitEffect (.leave sc)
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
    let v ← coerceSlot x v org
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
    let v ← coerceSlot x v org
    let r ← emitDef (.slotAddr x)
    emitEffect (.store r v (some org))
  | .expr e _ => do
    let _ ← lowerExpr e
    pure ()
  | .append owner src org => do
    let r ← lowerPlace owner
    let vw ← lowerView src
    emitEffect (.append r vw (some org))
  | .popN owner count org => do
    let r ← lowerPlace owner
    let n ← lowerExpr count
    emitEffect (.popN r n (some org))
  | .resize owner size fill org => do
    let r ← lowerPlace owner
    let n ← lowerExpr size
    let fill ← match fill with
      | none => pure none
      | some e => pure (some (← lowerExpr e))
    emitEffect (.resize r n fill (some org))
  | .clear owner org => do
    let r ← lowerPlace owner
    emitEffect (.clear r (some org))
  | .assignWhole owner replacement org => do
    let r ← lowerPlace owner
    emitEffect (.clear r (some org))
    let run ← lowerExpr replacement
    emitEffect (.replace r run (some org))
  | .ifS c t f _ => do
    let cv ← lowerExpr c
    whenLive () fun _ => do
      match f with
      | none =>
        let (tb, jb) ← fork cv
        setCur (some tb)
        let _ ← lowerBlock lc [] false t
        emitTerm (.br jb [])
        setCur (some jb)
      | some fb =>
        let (tb, eb) ← fork cv
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
    lowerWhile hb (lowerExpr c) (fun d xb => lowerBlock (some ⟨d, xb, .jump hb⟩) [] false body)
  | .forRange x lo hi body org => do
    let a ← lowerExpr lo
    let b ← lowerExpr hi
    whenLive () fun _ => do
      let t ← intTyOf a
      let (hb, hs) ← newBlock [.data (.int t)]
      let i := hs.headD 0
      emitTerm (.br hb [a])
      setCur (some hb)
      lowerRange t i b hb (fun d xb =>
        lowerBlock (some ⟨d, xb, .next hb t i⟩) [(x, i, org)] false body)
  | .forEach x idx v byRef body org => do
    -- The source is sampled once. An owner that is a grow-only array is kept by
    -- address so that its length can be read again.
    let (owner, vw) ← lowerEachSource v
    let regrow ← regrowOf owner
    let sampled ← eachSampled regrow vw
    let startAt ← emitDef (.constInt .i64 0)
    whenLive () fun _ => do
      let (hb, hs) ← newBlock [.data (.int .i64)]
      let i := hs.headD 0
      emitTerm (.br hb [startAt])
      setCur (some hb)
      lowerEach regrow owner sampled hb i (fun d xb => do
        let elem ← emitDef (.refElem vw i)
        let ev ← eachElemValue x byRef elem
        let pre := (x, ev, org) :: (match idx with
          | some j => [(j, i, org)]
          | none => [])
        lowerBlock (some ⟨d, xb, .next hb .i64 i⟩) pre false body)
  | .ret e org => do
    let vs ← match e with
      | some e => do
        let v ← lowerExpr e
        pure [← coerceResult v org]
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
      let (pb, fb) ← fork cv
      setCur (some fb)
      emitTerm (.abort .assert (some org))
      setCur (some pb)
  | .abort _ org => emitTerm (.abort .userAbort (some org))
  | .exit e org => do
    let v ← lowerExpr e
    emitTerm (.exit v (some org))

end

/-! ### Functions and the module -/

def initState : LS := ⟨#[], #[], none, []⟩

def finishBlocks (blocks : Array BlockB) : Array GIR.Block :=
  blocks.map fun b => ⟨b.params, b.insts.toList⟩

def tyOfVar (impl : Impl) (x : VarId) : Ty :=
  match impl.vars[x]? with
  | some lv => lv.ty
  | none => .unit

def lowerEnv (m : Module) (vars : Array LocalVar) (results : List Ty) : LEnv :=
  { mod := m
    results
    vars
    slots := vars.mapIdx fun i lv => ⟨lv.ty, lv.kind, lv.scope, i⟩
    globals := m.globals.map fun g => (g.ty, g.kind)
    sigs := m.contexts.map fun ctx =>
      match m.impls[ctx.impl]? with
      | some impl => (impl.params.toList.map (tyOfVar impl ·.var), impl.results.toList)
      | none => ([], []) }

def lowerContextRootInfo (ctx : Context) (impl : Impl) : GIR.RootInfo :=
  let params := impl.params.toList.zipIdx.filterMap fun (p, i) =>
    (ctx.varRoots.find? (·.1 == p.var)).map fun (_, roots) => (i, roots)
  let contents := impl.params.toList.zipIdx.filterMap fun (p, i) =>
    (ctx.contentRoots.find? (·.1 == p.var)).map fun (_, roots) => (i, roots)
  let results := (List.range impl.results.size).map fun i =>
    let roots := ctx.resultRoots[i]?.getD []
    let parameterRoots := impl.params.toList.zipIdx.filterMap fun (p, j) =>
      match ctx.varRoots.find? (·.1 == p.var) with
      | some (_, rootsForParam) =>
        if rootsForParam.all roots.contains then some (.param j) else none
      | none => none
    unionRoots roots parameterRoots
  { params := params.toArray, contents := contents.toArray, results := results.toArray }

/-- Core validation proves that a result-bearing body without a tail value
cannot fall through when it diverges. A live frontier left by a constant loop
is therefore synthetic; close it without inventing a return value. A fresh
sink follows the body's scope leaves, so its self-loop preserves scope balance. -/
def finishFunction (impl : Impl) (v : ValueId) : B Unit := do
  let env ← read
  if (← isLive) then
    if !impl.results.isEmpty && impl.body.value.isNone && impl.body.diverges env.mod.noReturn then
      let (sink, _) ← newBlock []
      emitTerm (.br sink [])
      setCur (some sink)
      emitTerm (.br sink [])
    else emitTerm (.ret (if impl.body.value.isSome then [v] else []) none)

def lowerImpl (m : Module) (impl : Impl) : GIR.Func :=
  let env := lowerEnv m impl.vars impl.results.toList
  let act : B Unit := do
    let (b0, ps) ← newBlock (impl.params.toList.map fun p => .data (tyOfVar impl p.var))
    setCur (some b0)
    let pre := (impl.params.toList.zip ps).map fun (p, v) =>
      (p.var, v, (impl.vars[p.var]?.map (·.org)).getD 0)
    let v ← lowerBlock none pre false impl.body
    finishFunction impl v
  let ((), s) := act env initState
  { name := impl.name
    params := impl.params.toList.map fun p => tyOfVar impl p.var
    results := impl.results.toList
    slots := env.slots
    scopes := scopeParents (blockScopes none impl.body)
    blocks := finishBlocks s.blocks
    summary := impl.summary
    org := impl.vars[0]?.map (·.org) }

def lowerContextAt (m : Module) (ctx : Context) (impl : Impl) : GIR.Func :=
  { lowerImpl m impl with roots := lowerContextRootInfo ctx impl }

def invalidContextFunction (ctx : Context) : GIR.Func :=
  { name := ctx.decl
    params := []
    results := []
    slots := #[]
    scopes := #[]
    blocks := #[]
    summary := .unknown
    org := none }

/-- Lower a global's initializer to a function that returns the value. -/
def lowerGlobal (m : Module) (g : Global) : GIR.Global :=
  let env := lowerEnv m #[] [g.ty]
  let act : B Unit := do
    let (b0, _) ← newBlock []
    setCur (some b0)
    let v ← lowerExpr g.init
    emitTerm (.ret [v] (some g.org))
  let ((), s) := act env initState
  { name := g.name
    ty := g.ty
    kind := g.kind
    init :=
      { name := g.name
        params := []
        results := [g.ty]
        slots := #[]
        scopes := scopeParents (exprScopes none g.init)
        blocks := finishBlocks s.blocks
        roots := { results := #[[]] }
        summary := .unknown
        org := some g.org }
    org := g.org }

/-- The reference lowering of a Core module. -/
def lower (m : Module) : GIR.Module :=
  let bodies := m.impls.map fun impl => (impl, lowerImpl m impl)
  { files := m.files
    globals := m.globals.map (lowerGlobal m)
    funcs := m.contexts.map fun ctx =>
      match bodies[ctx.impl]? with
      | some (impl, body) => { body with roots := lowerContextRootInfo ctx impl }
      | none => invalidContextFunction ctx
    entry := m.entry
    origins := m.origins
    profile := m.profile
    structs := m.structs }

private def sameNameRootImpl : Impl :=
  { name := "same"
    params := #[⟨0, .byRef⟩]
    results := #[]
    vars := #[⟨"p", .ref .mutable (.int .i64), .immutable, 0, 0⟩]
    body := .mk 0 [] none
    summary := .unknown }

private def sameNameRootModule : Module :=
  { files := #[]
    types := #[]
    globals := #[]
    impls := #[sameNameRootImpl, sameNameRootImpl]
    contexts := #[
      { impl := 0, decl := "same#0", varRoots := [(0, [.global 0])], resultRoots := [] },
      { impl := 1, decl := "same#1", varRoots := [(0, [.global 1])], resultRoots := [] }]
    entry := 0
    origins := #[] }

#guard (lower sameNameRootModule).funcs[0]?.map (·.roots.params) == some #[(0, [.global 0])]
#guard (lower sameNameRootModule).funcs[1]?.map (·.roots.params) == some #[(0, [.global 1])]

end Goose.Lower
