import Goose.Core.Syntax

/-!
Static checks that need no root annotation: typing (`V-TYPE`), writes through
`mut` places (`V-MUT`) and the mutability a call's arguments must carry
(`V-CALL`).

The check is one traversal of each implementation. It computes the type of
every expression, place and view, tracks which variables are declared and
visible, and rejects with the rule that the failing condition belongs to.
Variables must be declared once each, in ascending variable order, which is
the order the encoding numbers them in; later checks rely on it to compare
declaration order.
-/

namespace Goose.Core

inductive Rule
  | type
  | mut
  | root
  | block
  | result
  | call
  | summary
  deriving DecidableEq, Repr

def Rule.tag : Rule → String
  | .type => "V-TYPE"
  | .mut => "V-MUT"
  | .root => "V-ROOT"
  | .block => "V-BLOCK"
  | .result => "V-RESULT"
  | .call => "V-CALL"
  | .summary => "V-SUMMARY"

structure Rejection where
  rule : Rule
  message : String

abbrev V := Except Rejection

def reject (r : Rule) (msg : String) : V α := .error ⟨r, msg⟩

/-! ### Type predicates -/

/-- What a reference may point to. -/
def Ty.refTarget : Ty → Bool
  | .int _ | .bool => true
  | .arr e _ => e.flat
  | .grow e => e.flat
  | _ => false

/-- Types a variable, parameter or global may have. -/
def Ty.storable : Ty → Bool
  | .int _ | .bool => true
  | .arr e _ => e.flat
  | .grow e => e.flat
  | .ref _ t => t.refTarget
  | .slice _ e => e.flat
  | _ => false

/-- Types whose values a read may produce: flat values, references and slices. -/
def Ty.readable : Ty → Bool
  | .ref _ t => t.refTarget
  | .slice _ e => e.flat
  | t => t.flat

def Ty.isRefLike : Ty → Bool
  | .ref _ _ | .slice _ _ => true
  | _ => false

def Mutability.atLeast : Mutability → Mutability → Bool
  | .mutable, _ => true
  | .readOnly, .readOnly => true
  | .readOnly, .mutable => false

/-- An argument of type `a` may be passed where `p` is expected: equal, except
that a mutable reference or slice may stand for a read-only one. -/
def Ty.passableTo : Ty → Ty → Bool
  | .ref m t, .ref m' t' => t == t' && m.atLeast m'
  | .slice m t, .slice m' t' => t == t' && m.atLeast m'
  | a, p => a == p

/-! ### Divergence -/

mutual
def Stmt.hasBreak : Stmt → Bool
  | .brk _ => true
  | .ifS _ t f _ => t.hasBreak || (match f with | some b => b.hasBreak | none => false)
  | .while _ b _ => b.hasBreak
  | .forRange _ _ _ b _ => b.hasBreak
  | .forEach _ _ _ _ b _ => b.hasBreak
  | _ => false

def Block.hasBreak : Block → Bool
  | .mk _ ss _ => stmtsHaveBreak ss

def stmtsHaveBreak : List Stmt → Bool
  | [] => false
  | s :: rest => s.hasBreak || stmtsHaveBreak rest
end

mutual
/-- The statement never completes normally: it returns, aborts, exits or loops forever. -/
def Stmt.diverges : Stmt → Bool
  | .ret _ _ => true
  | .abort _ _ => true
  | .exit _ _ => true
  | .ifS _ t (some f) _ => t.diverges && f.diverges
  | .while (.bool true) b _ => !b.hasBreak
  | _ => false

def Block.diverges : Block → Bool
  | .mk _ ss _ => stmtsDiverge ss

def stmtsDiverge : List Stmt → Bool
  | [] => false
  | s :: rest => s.diverges || stmtsDiverge rest
end

/-! ### Typing environment -/

structure TEnv where
  mod : Module
  impl : Option Impl
  vars : Array LocalVar
  /-- Variables declared and in scope at this point. -/
  visible : List VarId
  /-- Loops enclosing this point in the current implementation. -/
  loops : Nat
  /-- Scope numbers of the open blocks, innermost first. -/
  scopes : List Nat
  /-- Globals a place may name: all of them in an implementation, the earlier
  ones in a global initializer. -/
  globalLimit : Nat
  /-- The global being initialized, when checking an initializer. -/
  initializing : Option GlobalId

/-- The state is the next variable to be declared. -/
abbrev T := StateT Nat V

def rej (r : Rule) (msg : String) : T α := throw ⟨r, msg⟩

def checkOrg (env : TEnv) (o : OriginId) : T Unit :=
  if o < env.mod.origins.size then pure () else rej .type s!"origin {o} outside the origin table"

def varOf (env : TEnv) (x : VarId) : T LocalVar :=
  if !env.visible.contains x then rej .type s!"variable {x} is not declared at this point"
  else match env.vars[x]? with
    | some lv => pure lv
    | none => rej .type s!"variable {x} outside the variable table"

/-- Claim the next variable id for a declaration in block `scope`. The encoding
numbers a variable before the variables its initializer declares. -/
def declare (env : TEnv) (x : VarId) (scope : Nat) : T LocalVar := do
  let next ← get
  unless x = next do rej .type s!"variable {x} is declared out of order (expected {next})"
  match env.vars[x]? with
  | none => rej .type s!"variable {x} outside the variable table"
  | some lv =>
    unless lv.scope = scope do
      rej .type s!"variable {x} belongs to block {lv.scope}, declared in block {scope}"
    unless lv.ty.storable do rej .type s!"variable {x} has a type no variable may have"
    set (next + 1)
    pure lv

def requireInt (what : String) (t : Ty) : T IntTy :=
  match t with
  | .int i => pure i
  | _ => rej .type s!"{what} is not an integer"

def requireBool (what : String) (t : Ty) : T Unit :=
  match t with
  | .bool => pure ()
  | _ => rej .type s!"{what} is not a boolean"

def requireWrite (what : String) (mutable : Bool) : T Unit :=
  if mutable then pure () else rej .mut s!"{what} writes through a place that is not mutable"

/-- Arguments against parameters, one by one. -/
def argMode : Arg → Mode
  | .byVal _ => .byValue
  | .byRef _ _ => .byRef

mutual

def tyPlace (env : TEnv) : Place → T (Ty × Bool)
  | .var x => do
    let lv ← varOf env x
    pure (lv.ty, lv.kind == .mutable)
  | .global g => do
    if g < env.globalLimit then
      match env.mod.globals[g]? with
      | some gl => pure (gl.ty, gl.kind == .mutable)
      | none => rej .type s!"global {g} outside the global table"
    else rej .type s!"global {g} is not initialized at this point"
  | .deref e => do
    match (← tyExpr env e) with
    | .ref m t => pure (t, m == .mutable)
    | _ => rej .type "dereference of a value that is not a reference"
  | .elem v i o => do
    checkOrg env o
    let (el, mu) ← tyView env v
    let _ ← requireInt "an index" (← tyExpr env i)
    pure (el, mu)

def tyView (env : TEnv) : View → T (Ty × Bool)
  | .of p => do
    let (t, mu) ← tyPlace env p
    match t with
    | .arr el _ => pure (el, mu)
    | .grow el => pure (el, mu)
    | _ => rej .type "a view of something that is not an array"
  | .val e => do
    match (← tyExpr env e) with
    | .slice m el => pure (el, m == .mutable)
    | _ => rej .type "a view of a value that is not a slice"

def tyBound (env : TEnv) : Bound → T Unit
  | .omitted => pure ()
  | .expr e => do let _ ← requireInt "a slice bound" (← tyExpr env e)
  | .fromEnd e => do let _ ← requireInt "a slice bound" (← tyExpr env e)

def tyExpr (env : TEnv) : Expr → T Ty
  | .lit t n =>
    if t.inRange n then pure (.int t) else rej .type s!"constant {n} out of range"
  | .bool _ => pure .bool
  | .read p => do
    let (t, _) ← tyPlace env p
    if t.readable then pure t else rej .type "a read of a value that cannot be copied"
  | .ref m p => do
    let (t, mu) ← tyPlace env p
    unless t.refTarget do rej .type "a reference to a value of a type no reference may target"
    if m == .mutable then requireWrite "a mutable reference" mu
    pure (.ref m t)
  | .slice m v lo hi o => do
    checkOrg env o
    let (el, mu) ← tyView env v
    tyBound env lo
    tyBound env hi
    if m == .mutable then requireWrite "a mutable slice" mu
    pure (.slice m el)
  | .len v => do
    let _ ← tyView env v
    pure (.int .i64)
  | .un op a o => do
    checkOrg env o
    let t ← requireInt "a unary operand" (← tyExpr env a)
    match op with
    | .neg =>
      -- Unary minus on an unsigned operand is a compile error in the language,
      -- although the numeric model defines it.
      if t.signed then pure (.int t) else rej .type "negation of an unsigned integer"
    | .bitnot => pure (.int t)
  | .bin _ a b o => do
    checkOrg env o
    let t ← requireInt "a binary operand" (← tyExpr env a)
    let u ← requireInt "a binary operand" (← tyExpr env b)
    unless t = u do rej .type "binary operands of different integer types"
    pure (.int t)
  | .cmp op a b => do
    match (← tyExpr env a), (← tyExpr env b) with
    | .int t, .int u =>
      unless t = u do rej .type "compared integers of different types"
      pure .bool
    | .bool, .bool =>
      match op with
      | .eq | .ne => pure .bool
      | _ => rej .type "booleans are only compared for equality"
    | _, _ => rej .type "comparison of values that are not both integers or both booleans"
  | .and a b => do
    requireBool "an operand of `and`" (← tyExpr env a)
    requireBool "an operand of `and`" (← tyExpr env b)
    pure .bool
  | .or a b => do
    requireBool "an operand of `or`" (← tyExpr env a)
    requireBool "an operand of `or`" (← tyExpr env b)
    pure .bool
  | .not a => do
    requireBool "the operand of `not`" (← tyExpr env a)
    pure .bool
  | .conv k target a o => do
    checkOrg env o
    let s ← requireInt "a converted value" (← tyExpr env a)
    match target with
    | .int d =>
      match k with
      | .widen =>
        unless d.minVal ≤ s.minVal ∧ s.maxVal ≤ d.maxVal do
          rej .type "a widening that does not preserve every value"
        pure (.int d)
      | _ => pure (.int d)
    | _ => rej .type "conversion to a type that is not an integer"
  | .call c args o => do
    checkOrg env o
    let some ctx := env.mod.contexts[c]? | rej .type s!"call of context {c}, outside the context table"
    let some callee := env.mod.impls[ctx.impl]? | rej .type s!"context {c} names a missing implementation"
    unless callee.params.size = args.length do
      rej .type s!"call of {callee.name} with {args.length} arguments, expected {callee.params.size}"
    tyArgs env callee callee.params.toList args
    if let some gi := env.initializing then
      -- An initializer runs before the later globals exist, so the callee must
      -- be known to leave them alone.
      match callee.summary with
      | .unknown => rej .call s!"initializer of global {gi} calls {callee.name}, whose effects are unknown"
      | .known s =>
        let later (t : Target) : Bool :=
          match t with | .global g => g ≥ gi | .param _ => false
        if (s.reads ++ s.writes ++ s.grows).any later then
          rej .call s!"initializer of global {gi} calls {callee.name}, which touches a later global"
    match callee.results.toList with
    | [] => pure .unit
    | [t] => pure t
    | _ => rej .type s!"{callee.name} has several results"
  | .push owner a => do
    let (t, mu) ← tyPlace env owner
    match t with
    | .grow el =>
      let argTy ← tyExpr env a
      unless argTy == el do rej .type "a pushed element of another type than the array's"
      requireWrite "push" mu
      pure (.ref .mutable el)
    | _ => rej .type "push to something that is not a grow-only array"
  | .ifE c t f => do
    requireBool "the condition of `if`" (← tyExpr env c)
    let tt ← tyBlock env [] t
    let ft ← tyBlock env [] f
    unless tt == ft do rej .type "the branches of `if` have different types"
    pure tt
  | .blockE b => tyBlock env [] b
  | .arrLit t es => do
    match t with
    | .arr el k =>
      unless el.flat do rej .type "array elements must be flat"
      unless es.length = k do rej .type s!"array literal of {es.length} elements for a type of {k}"
      tyExprsAs env el es
      pure t
    | .grow el =>
      unless el.flat do rej .type "array elements must be flat"
      tyExprsAs env el es
      pure t
    | _ => rej .type "array literal of a type that is not an array"
  | .fill t a => do
    match t with
    | .arr el _ =>
      unless el.flat do rej .type "array elements must be flat"
      let argTy ← tyExpr env a
      unless argTy == el do rej .type "fill value of another type than the elements"
      pure t
    | _ => rej .type "fill of a type that is not a fixed array"

def tyExprsAs (env : TEnv) (el : Ty) : List Expr → T Unit
  | [] => pure ()
  | e :: rest => do
    let t ← tyExpr env e
    unless t == el do rej .type "array element of another type than the array's"
    tyExprsAs env el rest

/-- Check each argument against the callee parameter at its position. -/
def tyArgs (env : TEnv) (callee : Impl) : List Param → List Arg → T Unit
  | p :: ps, a :: as => do
    unless argMode a == p.mode do
      rej .type s!"argument passed {repr (argMode a)}, parameter takes {repr p.mode}"
    let some pv := callee.vars[p.var]? | rej .type "parameter without a variable row"
    match a with
    | .byVal e =>
      let argTy ← tyExpr env e
      unless argTy.passableTo pv.ty do rej .call s!"argument of a type the parameter {pv.name} does not accept"
    | .byRef m p' =>
      let (t, mu) ← tyPlace env p'
      unless t.refTarget do rej .type "a by-reference argument of a type no reference may target"
      if m == .mutable then requireWrite "a mutable argument" mu
      unless (Ty.ref m t).passableTo pv.ty do
        rej .call s!"argument of a type or mutability the parameter {pv.name} does not accept"
    tyArgs env callee ps as
  | _, _ => pure ()

/-- Type a block. `pre` are the variables its construct declares in the
block's own scope before the first statement, with their required types. -/
def tyBlock (env : TEnv) (pre : List (VarId × Ty)) : Block → T Ty
  | .mk sc stmts value => do
    if env.scopes.contains sc then rej .type s!"block {sc} is nested in a block of the same number"
    let mut env' := { env with scopes := sc :: env.scopes }
    for (x, ty) in pre do
      let lv ← declare env' x sc
      unless lv.ty == ty do rej .type s!"variable {x} is declared with another type than the loop gives it"
      env' := { env' with visible := x :: env'.visible }
    env' ← tyStmts env' sc stmts
    match value with
    | none => pure .unit
    | some e => tyExpr env' e

def tyStmts (env : TEnv) (sc : Nat) : List Stmt → T TEnv
  | [] => pure env
  | s :: rest => do
    let env' ← tyStmt env sc s
    tyStmts env' sc rest

def tyPrintArgs (env : TEnv) : List PrintArg → T Unit
  | [] => pure ()
  | .text _ :: rest => tyPrintArgs env rest
  | .expr e :: rest => do
    match (← tyExpr env e) with
    | .int _ | .bool => tyPrintArgs env rest
    | _ => rej .type "printed value is neither an integer nor a boolean"

def tyStmt (env : TEnv) (sc : Nat) : Stmt → T TEnv
  | .letS x e o => do
    checkOrg env o
    let lv ← declare env x sc
    let t ← tyExpr env e
    unless lv.ty == t do rej .type s!"variable {x} is declared with another type than its initializer's"
    pure { env with visible := x :: env.visible }
  | .assign p e o => do
    checkOrg env o
    let (t, mu) ← tyPlace env p
    unless t.flat do rej .type "assignment to a place that does not hold a flat value"
    let et ← tyExpr env e
    unless et == t do rej .type "assigned value of another type than the place"
    requireWrite "assignment" mu
    pure env
  | .assignOp _ p e o => do
    checkOrg env o
    let (t, mu) ← tyPlace env p
    let i ← requireInt "the target of a compound assignment" t
    let u ← requireInt "the right side of a compound assignment" (← tyExpr env e)
    unless i = u do rej .type "compound assignment of another integer type"
    requireWrite "compound assignment" mu
    pure env
  | .rebind x e o => do
    checkOrg env o
    let lv ← varOf env x
    unless lv.ty.isRefLike do rej .type s!"rebind of variable {x}, which is not a reference or slice"
    unless lv.kind == .mutable do rej .mut s!"rebind of variable {x}, which is not a `var`"
    let et ← tyExpr env e
    unless et == lv.ty do rej .type "rebound value of another type than the variable"
    pure env
  | .expr e o => do
    checkOrg env o
    let _ ← tyExpr env e
    pure env
  | .append owner src o => do
    checkOrg env o
    let (t, mu) ← tyPlace env owner
    match t with
    | .grow el =>
      let (sel, _) ← tyView env src
      unless sel == el do rej .type "appended elements of another type than the array's"
      requireWrite "append" mu
      pure env
    | _ => rej .type "append to something that is not a grow-only array"
  | .ifS c t f o => do
    checkOrg env o
    requireBool "the condition of `if`" (← tyExpr env c)
    let _ ← tyBlock env [] t
    match f with
    | some b => do let _ ← tyBlock env [] b
    | none => pure ()
    pure env
  | .while c b o => do
    checkOrg env o
    requireBool "the condition of `while`" (← tyExpr env c)
    let _ ← tyBlock { env with loops := env.loops + 1 } [] b
    pure env
  | .forRange x lo hi b o => do
    checkOrg env o
    let t ← requireInt "a range bound" (← tyExpr env lo)
    let u ← requireInt "a range bound" (← tyExpr env hi)
    unless t = u do rej .type "range bounds of different integer types"
    let _ ← tyBlock { env with loops := env.loops + 1 } [(x, .int t)] b
    pure env
  | .forEach x idx v byRef b o => do
    checkOrg env o
    let (el, mu) ← tyView env v
    -- A reference loop variable may be read-only over a mutable run, so its
    -- mutability is read from its row; it may be mutable only over a mutable run.
    let xty ← if byRef then
        match env.vars[x]? with
        | some lv =>
          match lv.ty with
          | .ref mx t =>
            unless t == el do rej .type "loop variable of another type than the elements"
            if mx == .mutable then requireWrite "a mutable loop reference" mu
            pure lv.ty
          | _ => rej .type "a by-reference loop variable that is not a reference"
        | none => rej .type s!"variable {x} outside the variable table"
      else
        pure el
    let pre := (x, xty) :: (match idx with | some j => [(j, Ty.int .i64)] | none => [])
    let _ ← tyBlock { env with loops := env.loops + 1 } pre b
    pure env
  | .ret e o => do
    checkOrg env o
    match env.impl with
    | none => rej .type "return in a global initializer"
    | some impl =>
      match impl.results.toList, e with
      | [], none => pure env
      | [t], some e => do
        let et ← tyExpr env e
        unless et == t do rej .type "returned value of another type than the result"
        pure env
      | _, _ => rej .type "return does not match the function's result"
  | .brk o => do
    checkOrg env o
    if env.loops = 0 then rej .type "break outside a loop" else pure env
  | .cont o => do
    checkOrg env o
    if env.loops = 0 then rej .type "continue outside a loop" else pure env
  | .print args o => do
    checkOrg env o
    tyPrintArgs env args
    pure env
  | .assertS e o => do
    checkOrg env o
    requireBool "an asserted value" (← tyExpr env e)
    pure env
  | .abort _ o => do
    checkOrg env o
    pure env
  | .exit e o => do
    checkOrg env o
    let _ ← requireInt "an exit code" (← tyExpr env e)
    pure env

end

/-- Check an implementation: its parameters, its body and that a function with
a result does not fall off its end. -/
def checkImpl (m : Module) (impl : Impl) : V Unit := do
  let env : TEnv := {
    mod := m, impl := some impl, vars := impl.vars
    visible := (List.range impl.params.size), loops := 0, scopes := []
    globalLimit := m.globals.size, initializing := none }
  if impl.results.size > 1 then reject .type s!"{impl.name} has several results"
  for t in impl.results do
    unless t.readable && t != .unit do reject .type s!"{impl.name} has a result of a type no function may return"
  for h : i in [0:impl.params.size] do
    let p := impl.params[i]
    unless p.var = i do reject .type s!"parameter {i} names variable {p.var}"
    let some lv := impl.vars[i]? | reject .type s!"parameter {i} has no variable row"
    unless lv.scope = 0 do reject .type s!"parameter {i} is not declared in the body block"
    match p.mode, lv.ty with
    | .byRef, .ref _ t => unless t.refTarget do reject .type s!"parameter {i} refers to a type no reference may target"
    | .byRef, _ => reject .type s!"by-reference parameter {i} is not of reference type"
    | .byValue, .ref _ _ => reject .type s!"by-value parameter {i} is of reference type"
    | .byValue, .grow _ => reject .type s!"by-value parameter {i} is a growable array"
    | .byValue, t => unless t.storable do reject .type s!"parameter {i} has a type no variable may have"
  unless impl.body.scope = 0 do reject .type s!"{impl.name}: the body block is not scope 0"
  let (bodyTy, declared) ← (tyBlock env [] impl.body).run impl.params.size
  let _ := declared
  match impl.results.toList with
  | [] =>
    unless bodyTy == .unit do reject .type s!"{impl.name} has no result but its body yields a value"
  | [t] =>
    if impl.body.value.isSome then
      unless bodyTy == t do reject .type s!"{impl.name}: body value of another type than the result"
    else
      unless impl.body.diverges do reject .type s!"{impl.name} can fall off its end without returning a value"
  | _ => reject .type s!"{impl.name} has several results"

/-- Check a global's declaration and initializer. -/
def checkGlobal (m : Module) (g : GlobalId) (gl : Global) : V Unit := do
  unless gl.ty.storable && !gl.ty.isRefLike do
    reject .type s!"global {gl.name} has a type no pilot global may have"
  unless gl.org < m.origins.size do reject .type s!"global {gl.name}: origin outside the origin table"
  let env : TEnv := {
    mod := m, impl := none, vars := #[], visible := [], loops := 0, scopes := []
    globalLimit := g, initializing := some g }
  let (t, _) ← (tyExpr env gl.init).run 0
  unless t == gl.ty do reject .type s!"initializer of global {gl.name} has another type than the global"

end Goose.Core
