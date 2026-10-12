import Goose.Core.Memory

/-!
The meaning of a Core module: one total function indexed by fuel and by the
numeric profile.

Shape of the definitions.

* `Fuel` is the structural recursion argument of every function in the
  mutual block, and each recursive call, including the evaluation of a
  subexpression and of the next statement of a block, passes the predecessor.
  So `eval n` is monotone in `n` and every fact about it is proved by
  induction on `n`.
* State and results are plain data (`St`, `Res`, `Stop`, `Flow`); the monad
  `M` is a state-passing function that keeps the state when a computation
  stops, so the trace of an aborted run is available.
* Each fault kind is raised only by one small family of helpers, never by
  the evaluation functions themselves: `danglingRoot` and `pathRange` by the
  store accessors `readLoc`, `writeLoc`, `appendLoc`, `lengthLoc` and
  `readRun`; `shape` by the `expect*` value tests; `unbound` by `rootOf`,
  `lookupContext`, `lookupImpl` and `lookupGlobal`; `arity` by `enterCall`; `flow` by
  `expectNormal` and `expectReturned`.
* Native stack grows only with the call chain, which `maxCallDepth` bounds.
* Nothing is `partial`, `unsafe`, `opaque` or `implemented_by`. A loop is a
  function calling itself in tail position, which the compiler turns into a
  jump, and a call nests native frames only as deeply as the Goose call chain.
-/

namespace Goose.Core

/-- Why a run stopped before the entry returned. -/
inductive Stop
  | abort (k : AbortKind) (org : OriginId)
  | exit (code : Int)
  | fault (k : FaultKind)
  | timeout

/-- Mutable state of a run. `nextAct` and `nextScope` only grow, so every
activation and every block entry gets a root instance no earlier one had. -/
structure St where
  store : Store
  /-- Bytes written by `print`, in order. -/
  trace : String
  nextAct : Nat
  nextScope : Nat

def St.initial : St := ⟨Store.empty, "", 0, 0⟩

inductive Res (α : Type)
  | ok (a : α) (s : St)
  | stop (e : Stop) (s : St)

def M (α : Type) : Type := St → Res α

namespace M

@[inline] def pure' (a : α) : M α := fun s => .ok a s

@[inline] def bind' (m : M α) (f : α → M β) : M β := fun s =>
  match m s with
  | .ok a s' => f a s'
  | .stop e s' => .stop e s'

instance : Monad M where
  pure := pure'
  bind := bind'

@[inline] def stop (e : Stop) : M α := fun s => .stop e s

@[inline] def get : M St := fun s => .ok s s

@[inline] def set (s' : St) : M Unit := fun _ => .ok () s'

end M

/-- How control leaves a statement or block. -/
inductive Flow
  | normal (v : Val)
  | brk
  | cont
  | ret (v : Val)

/-- A numeric profile and the module being run. -/
structure Cfg where
  profile : NumProfile
  mod : Module

/-- The activation a piece of code runs in: the variable table it indexes,
the activation id, and the blocks entered so far with their instances. -/
structure Env where
  vars : Array LocalVar
  act : ActId
  scopes : List (Nat × ScopeInst)
  /-- Calls between the entry and this activation. -/
  depth : Nat

/-- The deepest call nesting a run follows. Native stack grows with the call
chain, so a run that goes deeper stops as a timeout instead of exhausting the
stack: depth is a resource the way fuel is. A bound independent of fuel keeps
`eval` monotone in fuel, since a run that finished never reached it. -/
def maxCallDepth : Nat := 100000

/-- A sampled run of elements of the array at `loc`. `resizable` is set when
the run was taken from a resizable owner, whose length a loop re-reads. -/
structure ViewVal where
  loc : Loc
  start : Nat
  len : Nat
  resizable : Bool

section Helpers

def timeout : M α := M.stop .timeout

def abortAt (k : AbortKind) (org : OriginId) : M α := M.stop (.abort k org)

def fault (k : FaultKind) : M α := M.stop (.fault k)

/-- Store accessors: the only source of `danglingRoot` and `pathRange`. -/
def readLoc (l : Loc) : M Val := fun s =>
  match s.store.read l with
  | .ok v => .ok v s
  | .error k => .stop (.fault k) s

def writeLoc (l : Loc) (v : Val) : M Unit := fun s =>
  match s.store.write l v with
  | .ok st => .ok () { s with store := st }
  | .error k => .stop (.fault k) s

/-- Append to the resizable array at `l`; yields the index of the first new element. -/
def appendLoc (l : Loc) (vs : Array Val) : M Nat := fun s =>
  match s.store.append l vs with
  | .ok (st, i) => .ok i { s with store := st }
  | .error k => .stop (.fault k) s

def lengthLoc (l : Loc) : M Nat := fun s =>
  match s.store.length l with
  | .ok n => .ok n s
  | .error k => .stop (.fault k) s

/-- The elements of a sampled run, copied. -/
def readRun (vw : ViewVal) : M (Array Val) := do
  match (← readLoc vw.loc) with
  | .fixed es | .resizable es =>
    if vw.start + vw.len ≤ es.size then pure (es.extract vw.start (vw.start + vw.len))
    else fault .pathRange
  | _ => fault .shape

/-- Run `f` on each element in order, collecting the results. -/
def mapList (f : α → M β) : List α → M (List β)
  | [] => pure []
  | a :: as => do
    let b ← f a
    let bs ← mapList f as
    pure (b :: bs)

def bindRoot (r : RootInst) (v : Val) : M Unit := fun s =>
  .ok () { s with store := s.store.introduce r v }

/-- Bind each variable of a construct to its value in the scope instance `si`. -/
def bindAll (act : ActId) (si : ScopeInst) : List (VarId × Val) → M Unit
  | [] => pure ()
  | (x, v) :: rest => do
    bindRoot (.local act si x) v
    bindAll act si rest

def freshAct : M ActId := fun s => .ok s.nextAct { s with nextAct := s.nextAct + 1 }

def freshScope : M ScopeInst := fun s => .ok s.nextScope { s with nextScope := s.nextScope + 1 }

def emit (text : String) : M Unit := fun s => .ok () { s with trace := s.trace ++ text }

/-- Value-shape tests: raise `shape`. -/
def expectInt : Val → M (IntTy × Int)
  | .int t n => pure (t, n)
  | _ => fault .shape

def expectBool : Val → M Bool
  | .bool b => pure b
  | _ => fault .shape

def expectRef : Val → M Loc
  | .ref l => pure l
  | _ => fault .shape

def expectSlice : Val → M (Loc × Nat × Nat)
  | .slice l start len => pure (l, start, len)
  | _ => fault .shape

/-- The element count of an array object and whether it can grow. -/
def expectArray : Val → M (Nat × Bool)
  | .fixed es => pure (es.size, false)
  | .resizable es => pure (es.size, true)
  | _ => fault .shape

def expectSameTy (t u : IntTy) : M Unit :=
  if t = u then pure () else fault .shape

def expectIntTy : Ty → M IntTy
  | .int t => pure t
  | _ => fault .shape

/-- The operands of a comparison as integers; booleans compare as 0 and 1. -/
def expectComparable : Val → Val → M (Int × Int)
  | .int t i, .int u j => do expectSameTy t u; pure (i, j)
  | .bool p, .bool q => pure ((if p then 1 else 0), (if q then 1 else 0))
  | _, _ => fault .shape

/-- Build the array a literal of type `t` denotes. -/
def expectArrayLit (t : Ty) (vs : Array Val) : M Val :=
  match t with
  | .arr _ _ => pure (.fixed vs)
  | .grow _ => pure (.resizable vs)
  | _ => fault .shape

def expectFixedCount : Ty → M Nat
  | .arr _ k => pure k
  | _ => fault .shape

/-- Flow tests: raise `flow`. A block operand, and a function body, must end
by falling through or, for a body, returning. -/
def expectNormal : Flow → M Val
  | .normal v => pure v
  | _ => fault .flow

def expectReturned : Flow → M Val
  | .normal v => pure v
  | .ret v => pure v
  | _ => fault .flow

def render : Val → M String
  | .int _ n => pure (toString n)
  | .bool true => pure "true"
  | .bool false => pure "false"
  | _ => fault .shape

/-- Table lookups: raise `unbound`. -/
def lookupContext (cfg : Cfg) (c : ContextId) : M Context :=
  match cfg.mod.contexts[c]? with
  | some ctx => pure ctx
  | none => fault .unbound

def lookupGlobal (cfg : Cfg) (g : GlobalId) : M Global :=
  match cfg.mod.globals[g]? with
  | some gl => pure gl
  | none => fault .unbound

def lookupImpl (cfg : Cfg) (i : ImplId) : M Impl :=
  match cfg.mod.impls[i]? with
  | some impl => pure impl
  | none => fault .unbound

/-- The root instance of variable `x`: its declaring block must be open. -/
def rootOf (env : Env) (x : VarId) : M RootInst :=
  match env.vars[x]? with
  | none => fault .unbound
  | some lv =>
    match env.scopes.lookup lv.scope with
    | none => fault .unbound
    | some si => pure (.local env.act si x)

/-- Remove the roots of the variables declared in block `sc`, instance `si`. -/
def releaseVars (vars : Array LocalVar) (act : ActId) (sc : Nat) (si : ScopeInst) :
    Nat → Store → Store
  | 0, st => st
  | i + 1, st =>
    match vars[i]? with
    | some lv => releaseVars vars act sc si i (if lv.scope == sc then st.release (.local act si i) else st)
    | none => releaseVars vars act sc si i st

def releaseScope (env : Env) (sc : Nat) (si : ScopeInst) : M Unit := fun s =>
  .ok () { s with store := releaseVars env.vars env.act sc si env.vars.size s.store }

end Helpers

mutual

def evalExpr : Nat → Cfg → Env → Expr → M Val
  | 0, _, _, _ => timeout
  | n + 1, cfg, env, e =>
    match e with
    | .lit t v => pure (.int t v)
    | .bool b => pure (.bool b)
    | .read p => do
      let l ← evalPlace n cfg env p
      readLoc l
    | .ref _ p => do
      let l ← evalPlace n cfg env p
      pure (.ref l)
    | .slice _ v lo hi org => do
      let vw ← evalView n cfg env v
      let lo' ← evalBound n cfg env vw.len 0 lo
      let hi' ← evalBound n cfg env vw.len vw.len hi
      if 0 ≤ lo' ∧ lo' ≤ hi' ∧ hi' ≤ (vw.len : Int) then
        pure (.slice vw.loc (vw.start + lo'.toNat) (hi' - lo').toNat)
      else abortAt .sliceOob org
    | .len v => do
      let vw ← evalView n cfg env v
      pure (.int .i64 vw.len)
    | .un op a org => do
      let (t, x) ← expectInt (← evalExpr n cfg env a)
      match evalUn cfg.profile op t x with
      | .ok r => pure (.int t r)
      | .error k => abortAt (AbortKind.ofNum k) org
    | .bin op a b org => do
      let (t, x) ← expectInt (← evalExpr n cfg env a)
      let (u, y) ← expectInt (← evalExpr n cfg env b)
      expectSameTy t u
      match evalBin cfg.profile op t x y with
      | .ok r => pure (.int t r)
      | .error k => abortAt (AbortKind.ofNum k) org
    | .cmp op a b => do
      let x ← evalExpr n cfg env a
      let y ← evalExpr n cfg env b
      let (i, j) ← expectComparable x y
      pure (.bool (evalCmp op i j))
    | .and a b => do
      if (← expectBool (← evalExpr n cfg env a)) then
        pure (.bool (← expectBool (← evalExpr n cfg env b)))
      else pure (.bool false)
    | .or a b => do
      if (← expectBool (← evalExpr n cfg env a)) then pure (.bool true)
      else pure (.bool (← expectBool (← evalExpr n cfg env b)))
    | .not a => do
      pure (.bool (!(← expectBool (← evalExpr n cfg env a))))
    | .conv k target a org => do
      let (src, x) ← expectInt (← evalExpr n cfg env a)
      let dst ← expectIntTy target
      match evalConv cfg.profile k src dst x with
      | .ok r => pure (.int dst r)
      | .error k => abortAt (AbortKind.ofNum k) org
    | .call c args _ => do
      let vals ← mapList (evalArg n cfg env) args
      enterCall n cfg env.depth c vals
    | .push owner a => do
      let l ← evalPlace n cfg env owner
      let v ← evalExpr n cfg env a
      let i ← appendLoc l #[v]
      pure (.ref { l with path := l.path ++ [i] })
    | .ifE c t f => do
      if (← expectBool (← evalExpr n cfg env c)) then blockValue n cfg env t
      else blockValue n cfg env f
    | .blockE b => blockValue n cfg env b
    | .arrLit t es => do
      let vs ← mapList (evalExpr n cfg env) es
      expectArrayLit t vs.toArray
    | .fill t a => do
      let k ← expectFixedCount t
      let v ← evalExpr n cfg env a
      pure (.fixed (Array.replicate k v))

/-- A block used as an expression yields its value; `break`, `continue` and
`return` cannot cross an expression boundary. -/
def blockValue : Nat → Cfg → Env → Block → M Val
  | 0, _, _, _ => timeout
  | n + 1, cfg, env, b => do
    expectNormal (← execBlock n cfg env [] b)

def evalArg : Nat → Cfg → Env → Arg → M Val
  | 0, _, _, _ => timeout
  | n + 1, cfg, env, a =>
    match a with
    | .byVal e => evalExpr n cfg env e
    | .byRef _ p => do
      let l ← evalPlace n cfg env p
      pure (.ref l)

/-- Evaluate a bound of a slice expression against the sampled length. -/
def evalBound : Nat → Cfg → Env → Nat → Int → Bound → M Int
  | 0, _, _, _, _, _ => timeout
  | n + 1, cfg, env, len, dflt, b =>
    match b with
    | .omitted => pure dflt
    | .expr e => do
      let (_, k) ← expectInt (← evalExpr n cfg env e)
      pure k
    | .fromEnd e => do
      let (_, k) ← expectInt (← evalExpr n cfg env e)
      pure ((len : Int) - k)

def evalPlace : Nat → Cfg → Env → Place → M Loc
  | 0, _, _, _ => timeout
  | n + 1, cfg, env, p =>
    match p with
    | .var x => do
      let r ← rootOf env x
      pure ⟨r, []⟩
    | .global g => pure ⟨.global g, []⟩
    | .deref e => do
      expectRef (← evalExpr n cfg env e)
    | .elem v i org => do
      let vw ← evalView n cfg env v
      let (_, k) ← expectInt (← evalExpr n cfg env i)
      if 0 ≤ k ∧ k < (vw.len : Int) then
        pure ⟨vw.loc.root, vw.loc.path ++ [vw.start + k.toNat]⟩
      else abortAt .indexOob org

def evalView : Nat → Cfg → Env → View → M ViewVal
  | 0, _, _, _ => timeout
  | n + 1, cfg, env, v =>
    match v with
    | .of p => do
      let l ← evalPlace n cfg env p
      let (len, resizable) ← expectArray (← readLoc l)
      pure ⟨l, 0, len, resizable⟩
    | .val e => do
      let (l, start, len) ← expectSlice (← evalExpr n cfg env e)
      pure ⟨l, start, len, false⟩

/-- Enter a fresh activation of the implementation context `c` names. -/
def enterCall : Nat → Cfg → Nat → ContextId → List Val → M Val
  | 0, _, _, _, _ => timeout
  | n + 1, cfg, depth, c, vals => do
    if depth ≥ maxCallDepth then timeout
    let ctx ← lookupContext cfg c
    let impl ← lookupImpl cfg ctx.impl
    if impl.params.size = vals.length then
      let act ← freshAct
      let env : Env := ⟨impl.vars, act, [], depth + 1⟩
      let pre := (impl.params.toList.zip vals).map fun (p, v) => (p.var, v)
      expectReturned (← execBlock n cfg env pre impl.body)
    else fault .arity

/-- Run a block in a fresh scope instance. `pre` binds the variables the
construct around the block declares into the block's own scope. The scope's
roots are removed on every way out except a stop, which ends the run. -/
def execBlock : Nat → Cfg → Env → List (VarId × Val) → Block → M Flow
  | 0, _, _, _, _ => timeout
  | n + 1, cfg, env, pre, .mk sc stmts value => do
    let si ← freshScope
    let env' : Env := { env with scopes := (sc, si) :: env.scopes }
    bindAll env.act si pre
    let flow ← execStmts n cfg env' stmts
    let flow ← match flow, value with
      | .normal _, some e => do pure (Flow.normal (← evalExpr n cfg env' e))
      | f, _ => pure f
    releaseScope env sc si
    pure flow

def execStmts : Nat → Cfg → Env → List Stmt → M Flow
  | 0, _, _, _ => timeout
  | _ + 1, _, _, [] => pure (.normal .unit)
  | n + 1, cfg, env, s :: rest => do
    match (← execStmt n cfg env s) with
    | .normal _ => execStmts n cfg env rest
    | f => pure f

def execStmt : Nat → Cfg → Env → Stmt → M Flow
  | 0, _, _, _ => timeout
  | n + 1, cfg, env, s =>
    match s with
    | .letS x e _ => do
      let v ← evalExpr n cfg env e
      let r ← rootOf env x
      bindRoot r v
      pure (.normal .unit)
    | .assign p e _ => do
      let l ← evalPlace n cfg env p
      let v ← evalExpr n cfg env e
      writeLoc l v
      pure (.normal .unit)
    | .assignOp op p e org => do
      let l ← evalPlace n cfg env p
      let (t, x) ← expectInt (← readLoc l)
      let (u, y) ← expectInt (← evalExpr n cfg env e)
      expectSameTy t u
      match evalBin cfg.profile op t x y with
      | .ok r => do
        writeLoc l (.int t r)
        pure (.normal .unit)
      | .error k => abortAt (AbortKind.ofNum k) org
    | .rebind x e _ => do
      let v ← evalExpr n cfg env e
      let r ← rootOf env x
      writeLoc ⟨r, []⟩ v
      pure (.normal .unit)
    | .expr e _ => do
      let _ ← evalExpr n cfg env e
      pure (.normal .unit)
    | .append owner src _ => do
      let l ← evalPlace n cfg env owner
      let vw ← evalView n cfg env src
      let elems ← readRun vw
      let _ ← appendLoc l elems
      pure (.normal .unit)
    | .ifS c t f _ => do
      let branch ← expectBool (← evalExpr n cfg env c)
      let flow ←
        if branch then execBlock n cfg env [] t
        else match f with
          | some b => execBlock n cfg env [] b
          | none => pure (.normal .unit)
      match flow with
      | .normal _ => pure (.normal .unit)
      | f => pure f
    | .while c body _ => execWhile n cfg env c body
    | .forRange x lo hi body _ => do
      let (t, a) ← expectInt (← evalExpr n cfg env lo)
      let (u, b) ← expectInt (← evalExpr n cfg env hi)
      expectSameTy t u
      execRange n cfg env x t a b body
    | .forEach x idx v byRef body _ => do
      let vw ← evalView n cfg env v
      execEach n cfg env x idx byRef body vw 0
    | .ret e _ => do
      match e with
      | some e => pure (.ret (← evalExpr n cfg env e))
      | none => pure (.ret .unit)
    | .brk _ => pure .brk
    | .cont _ => pure .cont
    | .print args _ => do
      let parts ← mapList (execPrintArg n cfg env) args
      emit (String.join parts ++ "\n")
      pure (.normal .unit)
    | .assertS e org => do
      if (← expectBool (← evalExpr n cfg env e)) then pure (.normal .unit)
      else abortAt .assert org
    | .abort _ org => abortAt .userAbort org
    | .exit e _ => do
      let (_, code) ← expectInt (← evalExpr n cfg env e)
      M.stop (.exit code)

/-- Arguments of one `print` are all evaluated before any of the line is
written, so output produced while evaluating a later argument comes first. -/
def execPrintArg : Nat → Cfg → Env → PrintArg → M String
  | 0, _, _, _ => timeout
  | n + 1, cfg, env, a =>
    match a with
    | .text s => pure s
    | .expr e => do render (← evalExpr n cfg env e)

def execWhile : Nat → Cfg → Env → Expr → Block → M Flow
  | 0, _, _, _, _ => timeout
  | n + 1, cfg, env, c, body => do
    if (← expectBool (← evalExpr n cfg env c)) then
      match (← execBlock n cfg env [] body) with
      | .normal _ => execWhile n cfg env c body
      | .cont => execWhile n cfg env c body
      | .brk => pure (.normal .unit)
      | .ret v => pure (.ret v)
    else pure (.normal .unit)

/-- Iterate `i` over `[i, hi)`; both bounds were evaluated once, before the loop. -/
def execRange : Nat → Cfg → Env → VarId → IntTy → Int → Int → Block → M Flow
  | 0, _, _, _, _, _, _, _ => timeout
  | n + 1, cfg, env, x, t, i, hi, body => do
    if i < hi then
      match (← execBlock n cfg env [(x, .int t i)] body) with
      | .normal _ => execRange n cfg env x t (i + 1) hi body
      | .cont => execRange n cfg env x t (i + 1) hi body
      | .brk => pure (.normal .unit)
      | .ret v => pure (.ret v)
    else pure (.normal .unit)

/-- Iterate over a sampled run. A run taken from a resizable owner is as long
as the owner is when each iteration starts; any other run keeps its length. -/
def execEach : Nat → Cfg → Env → VarId → Option VarId → Bool → Block → ViewVal → Nat → M Flow
  | 0, _, _, _, _, _, _, _, _ => timeout
  | n + 1, cfg, env, x, idx, byRef, body, vw, i => do
    let len ← if vw.resizable then lengthLoc vw.loc else pure vw.len
    if i < len then
      let elem : Loc := ⟨vw.loc.root, vw.loc.path ++ [vw.start + i]⟩
      let ev ← if byRef then pure (Val.ref elem) else readLoc elem
      let pre := (x, ev) :: (match idx with
        | some j => [(j, Val.int .i64 i)]
        | none => [])
      match (← execBlock n cfg env pre body) with
      | .normal _ => execEach n cfg env x idx byRef body vw (i + 1)
      | .cont => execEach n cfg env x idx byRef body vw (i + 1)
      | .brk => pure (.normal .unit)
      | .ret v => pure (.ret v)
    else pure (.normal .unit)

end

/-- How the entry's run ended, other than by a fault or by running out of fuel. -/
inductive Outcome
  | returned
  | aborted (k : AbortKind) (org : OriginId)
  | exited (code : Int)

inductive Result
  | done (o : Outcome) (trace : String)
  | timeout (trace : String)
  | fault (k : FaultKind)

/-- Initialize the globals in table order, each in an activation of its own
with no variables, then run the entry context. -/
def initGlobals (fuel : Nat) (cfg : Cfg) : List GlobalId → M Unit
  | [] => pure ()
  | g :: rest => do
    let gl ← lookupGlobal cfg g
    let act ← freshAct
    let v ← evalExpr fuel cfg ⟨#[], act, [], 0⟩ gl.init
    bindRoot (.global g) v
    initGlobals fuel cfg rest

def runModule (fuel : Nat) (cfg : Cfg) : M Unit := do
  initGlobals fuel cfg (List.range cfg.mod.globals.size)
  let _ ← enterCall fuel cfg 0 cfg.mod.entry []
  pure ()

/-- The meaning of a module: deterministic, total, and monotone in `fuel`. -/
def eval (fuel : Nat) (profile : NumProfile) (m : Module) : Result :=
  match runModule fuel ⟨profile, m⟩ St.initial with
  | .ok _ s => .done .returned s.trace
  | .stop (.abort k org) s => .done (.aborted k org) s.trace
  | .stop (.exit code) s => .done (.exited code) s.trace
  | .stop (.fault k) _ => .fault k
  | .stop .timeout s => .timeout s.trace

end Goose.Core
