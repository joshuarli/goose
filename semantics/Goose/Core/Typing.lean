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

/-- Run a check on each element in order, stopping at the first rejection. -/
def forAll (l : List α) (f : α → V Unit) : V Unit :=
  match l with
  | [] => pure ()
  | a :: rest => do
    f a
    forAll rest f

mutual
/-- Nominal payloads must be the field types of this module's declaration. -/
def checkResolvedType (m : Module) : Ty → V Unit
  | .structT sid fs => do
    unless m.profile == .shrink do reject .type "structs require core-shrink"
    unless m.structType? sid == some (.structT sid fs) do
      reject .type "struct type disagrees with its nominal descriptor"
    checkResolvedTypes m fs
  | .arr e _ | .grow e | .ref _ e | .slice _ e => checkResolvedType m e
  | .tuple ts => checkResolvedTypes m ts
  | .int _ | .bool | .unit => pure ()

def checkResolvedTypes (m : Module) : TyList → V Unit
  | .nil => pure ()
  | .cons t ts => do checkResolvedType m t; checkResolvedTypes m ts
end

def Module.fixedByteSize? (m : Module) : Ty → Option Nat
  | .int t => some (t.bits / 8)
  | .bool => some 1
  | .arr e k => (m.fixedByteSize? e).map (k * ·)
  | .structT sid fs => do
    if m.structType? sid != some (.structT sid fs) then none
    else (m.structs[sid]?).map (·.byteSize)
  | _ => none

/-- Logical field types and byte extents are checked independently of the exporter. -/
def checkStructTables (m : Module) : V Unit := do
  if m.profile == .pilot && !m.structs.isEmpty then reject .type "core-pilot has no struct table"
  for d in m.structs do
    if d.byteSize == 0 then reject .type "struct byte size must be positive"
    let mut endOffset := 0
    for f in d.fields do
      checkResolvedType m f.ty
      unless f.ty.flat do reject .type "struct fields must be flat fixed values"
      let some bytes := m.fixedByteSize? f.ty | reject .type "struct field has no fixed byte size"
      if bytes == 0 then reject .type "zero-size struct field"
      if f.byteOffset < endOffset then reject .type "struct fields overlap or are out of order"
      let fieldEnd := f.byteOffset + bytes
      if fieldEnd > d.byteSize then reject .type "struct field extends beyond its byte size"
      endOffset := fieldEnd
  forAll m.types.toList (checkResolvedType m)
  for g in m.globals do checkResolvedType m g.ty
  for impl in m.impls do
    for v in impl.vars do checkResolvedType m v.ty
    for r in impl.results do checkResolvedType m r

/-! ### Type predicates -/

/-- What a reference may point to. -/
def Ty.refTarget : Ty → Bool
  | .int _ | .bool => true
  | .arr e _ => e.flat
  | .grow e => e.flat
  | .structT _ fs => fs.flat
  | _ => false

/-- Types a variable, parameter or global may have. -/
def Ty.storable : Ty → Bool
  | .int _ | .bool => true
  | .arr e _ => e.flat
  | .grow e => e.flat
  | .structT _ fs => fs.flat
  | .ref _ t => t.refTarget
  | .slice _ e => e.flat
  | _ => false

/-- Types whose values a read may produce: flat values, references and slices. -/
def Ty.readable : Ty → Bool
  | .ref _ t => t.refTarget
  | .slice _ e => e.flat
  | t => t.flat

/-- A reference to a slice variable. Such a reference exists only as a
parameter: it is passed, never copied or stored. -/
def Ty.isRefSlice : Ty → Bool
  | .ref _ (.slice _ e) => e.flat
  | _ => false

def Ty.isSlice : Ty → Bool
  | .slice _ e => e.flat
  | _ => false

/-- Types a parameter may have. -/
def Ty.paramOk (t : Ty) : Bool := t.storable || t.isRefSlice

/-- A variable or a global named directly: the owner of its contents. `let`
forbids assigning the variable as a whole and nothing more, so the contents
of an array the place owns are writable whatever the variable's kind. -/
def Place.isOwner : Place → Bool
  | .var _ | .global _ => true
  | _ => false

/-- The variable a place dereferences directly. -/
def Place.derefVar? : Place → Option VarId
  | .deref (.read (.var x)) => some x
  | _ => none

/-- A place whose slice may be passed by reference: a slice variable, or the
pointee of a reference to one. -/
def Place.sliceArg : Place → Bool
  | .var _ => true
  | p => p.derefVar?.isSome

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
/-- The statement never completes normally: it returns, aborts, exits, loops
forever, or calls a function that never returns. `nr` says which contexts
never return to their caller. -/
def Stmt.diverges (nr : ContextId → Bool) : Stmt → Bool
  | .ret _ _ => true
  | .abort _ _ => true
  | .exit _ _ => true
  | .expr (.call c _ _) _ => nr c
  | .ifS _ t (some f) _ => t.diverges nr && f.diverges nr
  | .while (.bool true) b _ => !b.hasBreak
  | _ => false

def Block.diverges (nr : ContextId → Bool) : Block → Bool
  | .mk _ ss _ => stmtsDiverge nr ss

def stmtsDiverge (nr : ContextId → Bool) : List Stmt → Bool
  | [] => false
  | s :: rest => s.diverges nr || stmtsDiverge nr rest
end

/-- A statement that completes normally or ends the run: it never leaves by
`return`, `break` or `continue`. -/
def Stmt.isPlain : Stmt → Bool
  | .letS .. | .assign .. | .assignOp .. | .rebind .. | .expr .. | .append .. | .print ..
  | .assertS .. => true
  | _ => false

mutual
/-- The statement ends the run or never comes back: it aborts, exits, or calls
a function that never returns. Unlike `diverges`, a `return` does not count. -/
def Stmt.stops (nr : ContextId → Bool) : Stmt → Bool
  | .abort _ _ => true
  | .exit _ _ => true
  | .expr (.call c _ _) _ => nr c
  | .ifS _ t (some f) _ => t.stops nr && f.stops nr
  | _ => false

def Block.stops (nr : ContextId → Bool) : Block → Bool
  | .mk _ ss _ => stmtsStop nr ss

/-- Some statement stops, and every statement before it is plain. -/
def stmtsStop (nr : ContextId → Bool) : List Stmt → Bool
  | [] => false
  | s :: rest => s.stops nr || (s.isPlain && stmtsStop nr rest)
end

/-- Contexts that never return to their caller, found in `k` rounds: the body
stops, where a call stops if its callee was found in an earlier round. -/
def neverReturns (m : Module) : Nat → ContextId → Bool
  | 0, _ => false
  | k + 1, c =>
    match m.contexts[c]? with
    | some ctx =>
      match m.impls[ctx.impl]? with
      | some impl => impl.body.stops (neverReturns m k)
      | none => false
    | none => false

/-- The contexts of the module that never return: one round per context is
enough for any chain of calls. -/
def Module.noReturn (m : Module) : ContextId → Bool := neverReturns m m.contexts.size

/-! ### Typing environment -/

structure TEnv where
  mod : Module
  impl : Option Impl
  vars : Array LocalVar
  /-- Variables declared and in scope at this point. -/
  visible : List VarId
  /-- Loops enclosing this point that `break` and `continue` may leave. -/
  loops : Nat
  /-- Inside the block of an `if` or block expression, which must complete
  normally: control cannot leave an expression by `return`, `break` or
  `continue`. -/
  inExpr : Bool
  /-- Scope numbers of the open blocks, innermost first. -/
  scopes : List Nat
  /-- Globals a place may name: all of them in an implementation, the earlier
  ones in a global initializer. -/
  globalLimit : Nat
  /-- The global being initialized, when checking an initializer. -/
  initializing : Option GlobalId

/-- The state is the next variable to be declared. -/
abbrev T := StateT Nat V

/-- Effective capabilities of one place, computed while typing its owner once. -/
structure PlaceInfo where
  ty : Ty
  bindingWritable : Bool
  contentsWritable : Bool

def rej (r : Rule) (msg : String) : T α := throw ⟨r, msg⟩

/-- A plain reference cannot retain different whole-binding and contents capabilities. -/
def checkFieldReference (p : Place) (info : PlaceInfo) : T Unit :=
  match p, info.ty with
  | .field .., .structT .. | .field .., .arr .. =>
    if info.bindingWritable != info.contentsWritable then
      rej .type "split aggregate field references are outside this slice"
    else pure ()
  | _, _ => pure ()

def checkType (env : TEnv) (t : Ty) : T Unit := fun n => do
  checkResolvedType env.mod t
  pure ((), n)

/-- Resolved types carry the descriptor's field types, never a second nominal definition. -/
def structDef (env : TEnv) (t : Ty) : T StructDef := do
  unless env.mod.profile == .shrink do rej .type "structs require core-shrink"
  match t with
  | .structT sid _ =>
    unless env.mod.structType? sid == some t do rej .type "struct type disagrees with its nominal descriptor"
    let some d := env.mod.structs[sid]? | rej .type "struct id outside the descriptor table"
    pure d
  | _ => rej .type "a struct operation on another type"

def structField (env : TEnv) (t : Ty) (i : Nat) : T StructField := do
  let d ← structDef env t
  let some f := d.fields[i]? | rej .type "field index outside the struct descriptor"
  pure f

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

/-- The environment of a block that is an operand. -/
def exprEnv (env : TEnv) : TEnv := { env with loops := 0, inExpr := true }

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

/-- Declare the variables a construct binds in its block's own scope, in order,
each with the type the construct gives it. -/
def declarePre (env : TEnv) (sc : Nat) : List (VarId × Ty) → T TEnv
  | [] => pure env
  | (x, ty) :: rest => do
    let lv ← declare env x sc
    unless lv.ty == ty do rej .type s!"variable {x} is declared with another type than the loop gives it"
    declarePre { env with visible := x :: env.visible } sc rest

/-- An initializer runs before the later globals exist, so a function it calls
must be known to leave them alone. -/
def checkInitCall (env : TEnv) (callee : Impl) : T Unit :=
  match env.initializing with
  | none => pure ()
  | some gi =>
    match callee.summary with
    | .unknown => rej .call s!"initializer of global {gi} calls {callee.name}, whose effects are unknown"
    | .known s =>
      let later (t : Target) : Bool :=
        match t with | .global g => g ≥ gi | .param _ => false
      if (s.reads ++ s.writes ++ s.grows).any later then
        rej .call s!"initializer of global {gi} calls {callee.name}, which touches a later global"
      else pure ()

/-- The type of a call: the callee's one result, or unit. -/
def callResultTy (callee : Impl) : T Ty :=
  match callee.results.toList with
  | [] => pure .unit
  | [t] => pure t
  | _ => rej .type s!"{callee.name} has several results"

/-- The loop variable of a loop over elements of `el`: a copy of an element,
or a reference to one, which may be read-only over a mutable run and mutable
only over a mutable run. -/
def loopVarOk (lv : LocalVar) (byRef : Bool) (el : Ty) (mu : Bool) : T Unit :=
  if byRef then
    match lv.ty with
    | .ref mx t => do
      unless t == el do rej .type "loop variable of another type than the elements"
      if mx == .mutable then requireWrite "a mutable loop reference" mu else pure ()
    | _ => rej .type "a by-reference loop variable that is not a reference"
  else
    if lv.ty == el then pure ()
    else rej .type s!"variable {lv.name} is declared with another type than the loop gives it"

/-- The index variable of a loop over a run, declared after the element variable. -/
def declareIndex (env : TEnv) (sc : Nat) : Option VarId → T Unit
  | none => pure ()
  | some j => do
    let lj ← declare env j sc
    if lj.ty == .int .i64 then pure ()
    else rej .type s!"variable {j} is declared with another type than the loop gives it"

/-- The type of a visible reference-to-slice variable that is read only to be
dereferenced. No expression yields such a reference as a value. -/
def sliceRefTy (env : TEnv) (e : Expr) : Option Ty :=
  match e with
  | .read (.var x) =>
    if env.visible.contains x then
      match env.vars[x]? with
      | some lv => if lv.ty.isRefSlice then some lv.ty else none
      | none => none
    else none
  | _ => none

/-- A `return` without a value: outside expression blocks, in a function with
no result. -/
def retUnit (env : TEnv) : T Unit := do
  if env.inExpr then rej .type "return inside an expression block"
  match env.impl with
  | none => rej .type "return in a global initializer"
  | some impl =>
    match impl.results.toList with
    | [] => pure ()
    | _ => rej .type "return does not match the function's result"

/-- The type a `return` with a value must yield: outside expression blocks,
the function's one result. -/
def retTy (env : TEnv) : T Ty := do
  if env.inExpr then rej .type "return inside an expression block"
  match env.impl with
  | none => rej .type "return in a global initializer"
  | some impl =>
    match impl.results.toList with
    | [t] => pure t
    | _ => rej .type "return does not match the function's result"

/-- Arguments against parameters, one by one. -/
def argMode : Arg → Mode
  | .byVal _ => .byValue
  | .byRef _ _ => .byRef

mutual

def tyPlace (env : TEnv) : Place → T PlaceInfo
  | .var x => do
    let lv ← varOf env x
    pure ⟨lv.ty, lv.kind == .mutable, true⟩
  | .global g => do
    if g < env.globalLimit then
      match env.mod.globals[g]? with
      | some gl => pure ⟨gl.ty, gl.kind == .mutable, true⟩
      | none => rej .type s!"global {g} outside the global table"
    else rej .type s!"global {g} is not initialized at this point"
  | .deref e => do
    let src ← (match sliceRefTy env e with
      | some t => pure t
      | none => do
        let t ← tyExpr env e
        if t.isRefSlice then rej .type "a reference to a slice variable is not a value" else pure t)
    match src with
    | .ref m t => pure ⟨t, m == .mutable, m == .mutable⟩
    | _ => rej .type "dereference of a value that is not a reference"
  | .elem v i o => do
    checkOrg env o
    let (el, mu) ← tyView env v
    let _ ← requireInt "an index" (← tyExpr env i)
    pure ⟨el, mu, mu⟩
  | .field owner i => do
    let ownerInfo ← tyPlace env owner
    let f ← structField env ownerInfo.ty i
    pure ⟨f.ty, ownerInfo.contentsWritable && f.binding == .mutable,
      ownerInfo.contentsWritable && f.contents == .mutable⟩

def tyView (env : TEnv) : View → T (Ty × Bool)
  | .of p => do
    let placeInfo ← tyPlace env p
    let t := placeInfo.ty
    let mu := placeInfo.contentsWritable
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
    let placeInfo ← tyPlace env p
    let t := placeInfo.ty
    if t.readable then pure t else rej .type "a read of a value that cannot be copied"
  | .ref m p => do
    let placeInfo ← tyPlace env p
    let t := placeInfo.ty
    let mu := placeInfo.bindingWritable
    checkFieldReference p placeInfo
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
    checkInitCall env callee
    callResultTy callee
  | .push owner a => do
    let placeInfo ← tyPlace env owner
    let t := placeInfo.ty
    let mu := placeInfo.bindingWritable
    match t with
    | .grow el =>
      let argTy ← tyExpr env a
      unless argTy == el do rej .type "a pushed element of another type than the array's"
      requireWrite "push" mu
      pure (.ref .mutable el)
    | _ => rej .type "push to something that is not a grow-only array"
  | .ifE c t f => do
    requireBool "the condition of `if`" (← tyExpr env c)
    let tt ← tyBlock (exprEnv env) [] t
    let ft ← tyBlock (exprEnv env) [] f
    unless tt == ft do rej .type "the branches of `if` have different types"
    pure tt
  | .blockE b => tyBlock (exprEnv env) [] b
  | .arrLit t es => do
    checkType env t
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
    checkType env t
    match t with
    | .arr el _ =>
      unless el.flat do rej .type "array elements must be flat"
      let argTy ← tyExpr env a
      unless argTy == el do rej .type "fill value of another type than the elements"
      pure t
    | _ => rej .type "fill of a type that is not a fixed array"
  | .structLit t es => do
    let d ← structDef env t
    unless d.fields.size == es.length do rej .type "struct initializer count differs from its fields"
    tyStructExprs env (d.fields.toList.map (·.ty)) es
    pure t

def tyStructExprs (env : TEnv) : List Ty → List Expr → T Unit
  | [], [] => pure ()
  | t :: ts, e :: es => do
    unless (← tyExpr env e) == t do rej .type "struct initializer has another field type"
    tyStructExprs env ts es
  | _, _ => rej .type "struct initializer count differs from its fields"

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
      let placeInfo ← tyPlace env p'
      let t := placeInfo.ty
      let mu := placeInfo.bindingWritable
      checkFieldReference p' placeInfo
      -- A slice may be passed by reference only from a `var` slice variable or
      -- through a reference to one.
      unless t.refTarget || (t.isSlice && mu && p'.sliceArg) do
        rej .type "a by-reference argument of a type no reference may target"
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
    let env1 ← declarePre { env with scopes := sc :: env.scopes } sc pre
    let env2 ← tyStmts env1 sc stmts
    match value with
    | none => pure .unit
    | some e => tyExpr env2 e

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
    -- A writable reference or slice may initialize a read-only one.
    unless t.passableTo lv.ty do rej .type s!"variable {x} is declared with another type than its initializer's"
    pure { env with visible := x :: env.visible }
  | .assign p e o => do
    checkOrg env o
    let placeInfo ← tyPlace env p
    let t := placeInfo.ty
    let mu := placeInfo.bindingWritable
    -- A slice is assigned only through a reference to a slice variable; a
    -- slice variable itself is rebound.
    unless t.flat || (t.isSlice && p.derefVar?.isSome) do
      rej .type "assignment to a place that does not hold a flat value"
    let et ← tyExpr env e
    unless et == t do rej .type "assigned value of another type than the place"
    requireWrite "assignment" mu
    pure env
  | .assignOp _ p e o => do
    checkOrg env o
    let placeInfo ← tyPlace env p
    let t := placeInfo.ty
    let mu := placeInfo.bindingWritable
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
    unless et.passableTo lv.ty do rej .type "rebound value of another type than the variable"
    pure env
  | .expr e o => do
    checkOrg env o
    let _ ← tyExpr env e
    pure env
  | .append owner src o => do
    checkOrg env o
    let placeInfo ← tyPlace env owner
    let t := placeInfo.ty
    let mu := placeInfo.bindingWritable
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
    -- The loop variable is numbered where it is declared: before the
    -- variables its bounds declare.
    let lv ← declare env x b.scope
    let t ← requireInt "a range bound" (← tyExpr env lo)
    let u ← requireInt "a range bound" (← tyExpr env hi)
    unless t = u do rej .type "range bounds of different integer types"
    (if lv.ty == .int t then pure ()
      else rej .type s!"variable {x} is declared with another type than the loop gives it" : T Unit)
    let _ ← tyBlock { env with loops := env.loops + 1, visible := x :: env.visible } [] b
    pure env
  | .forEach x idx v byRef b o => do
    checkOrg env o
    -- The loop variables are numbered before the variables the run declares.
    let lv ← declare env x b.scope
    declareIndex env b.scope idx
    let (el, mu) ← tyView env v
    loopVarOk lv byRef el mu
    let _ ← tyBlock { env with loops := env.loops + 1, visible := x :: idx.toList ++ env.visible } [] b
    pure env
  | .ret none o => do
    checkOrg env o
    retUnit env
    pure env
  | .ret (some e) o => do
    checkOrg env o
    let t ← retTy env
    let et ← tyExpr env e
    unless et.passableTo t do rej .type "returned value of another type than the result"
    pure env
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

/-- A parameter is the variable of its position, declared in the body block,
and of a type its passing mode allows. -/
def checkParam (impl : Impl) (i : Nat) : V Unit :=
  match impl.params[i]? with
  | none => pure ()
  | some p => do
    unless p.var = i do reject .type s!"parameter {i} names variable {p.var}"
    let some lv := impl.vars[i]? | reject .type s!"parameter {i} has no variable row"
    unless lv.scope = 0 do reject .type s!"parameter {i} is not declared in the body block"
    match p.mode, lv.ty with
    | .byRef, .ref _ t =>
      unless t.refTarget || t.isSlice do
        reject .type s!"parameter {i} refers to a type no reference may target"
    | .byRef, _ => reject .type s!"by-reference parameter {i} is not of reference type"
    | .byValue, .ref _ _ => reject .type s!"by-value parameter {i} is of reference type"
    | .byValue, .grow _ => reject .type s!"by-value parameter {i} is a growable array"
    | .byValue, t => unless t.storable do reject .type s!"parameter {i} has a type no variable may have"

/-- Check an implementation: its parameters, its body and that a function with
a result does not fall off its end. -/
def checkImpl (m : Module) (impl : Impl) : V Unit := do
  let env : TEnv := {
    mod := m, impl := some impl, vars := impl.vars
    visible := (List.range impl.params.size), loops := 0, inExpr := false, scopes := []
    globalLimit := m.globals.size, initializing := none }
  if impl.results.size > 1 then reject .type s!"{impl.name} has several results"
  forAll impl.results.toList fun t =>
    unless t.readable && t != .unit do reject .type s!"{impl.name} has a result of a type no function may return"
  forAll (List.range impl.params.size) (checkParam impl)
  unless impl.body.scope = 0 do reject .type s!"{impl.name}: the body block is not scope 0"
  let (bodyTy, _) ← (tyBlock env [] impl.body).run impl.params.size
  match impl.results.toList with
  | [] =>
    unless bodyTy == .unit do reject .type s!"{impl.name} has no result but its body yields a value"
  | [t] =>
    if impl.body.value.isSome then
      unless bodyTy == t do reject .type s!"{impl.name}: body value of another type than the result"
    else
      unless impl.body.diverges m.noReturn do reject .type s!"{impl.name} can fall off its end without returning a value"
  | _ => reject .type s!"{impl.name} has several results"

/-- Check a global's declaration and initializer. -/
def checkGlobal (m : Module) (g : GlobalId) (gl : Global) : V Unit := do
  unless gl.ty.storable && !gl.ty.isRefLike do
    reject .type s!"global {gl.name} has a type no pilot global may have"
  unless gl.org < m.origins.size do reject .type s!"global {gl.name}: origin outside the origin table"
  let env : TEnv := {
    mod := m, impl := none, vars := #[], visible := [], loops := 0, inExpr := true, scopes := []
    globalLimit := g, initializing := some g }
  let (t, _) ← (tyExpr env gl.init).run 0
  unless t == gl.ty do reject .type s!"initializer of global {gl.name} has another type than the global"

end Goose.Core
