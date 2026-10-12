import Goose.Core.Typing

/-!
The checks that depend on a context's root annotation: `V-ROOT`, `V-BLOCK`,
`V-RESULT`, the root half of `V-CALL`, and `V-SUMMARY`.

One traversal per context computes, for every expression, place and view, the
set of roots a reference or slice it yields may have, and rejects where a
binding, a block value, a result or a call argument breaks its rule. The same
traversal collects the effects of the body, which the last step compares with
the implementation's summary. Nothing in the annotation or the summary is
trusted: roots are recomputed from the body and compared with the annotation.

Roots follow the scope rules of the language. A reference or slice variable
is bound to values whose roots are all within the variable's annotation, and
each of those roots is a parameter, a global, or a local of the variable's
own scope or an enclosing one; the order of declaration within one scope does
not matter because a scope's variables end together.
-/

namespace Goose.Core

/-- Targets of effects as a set; order and repeats are immaterial. -/
structure Eff where
  reads : List Target := []
  writes : List Target := []
  grows : List Target := []
  rebinds : List Target := []
  aborts : Bool := false
  outputs : Bool := false
  /-- Some callee's summary is `unknown`. -/
  unknown : Bool := false

structure RState where
  /-- Next variable to be declared; mirrors the typing pass. -/
  nextVar : Nat
  eff : Eff

abbrev P := StateT RState V

structure PEnv where
  mod : Module
  impl : Impl
  ctx : Context
  /-- Scope numbers of the open blocks, innermost first. -/
  scopes : List Nat

def rejP (r : Rule) (msg : String) : P α := throw ⟨r, msg⟩

/-- A check that neither reads nor changes the traversal state. -/
def liftV (x : V α) : P α := fun s =>
  match x with
  | .ok a => .ok (a, s)
  | .error e => .error e

def PEnv.ann (env : PEnv) (x : VarId) : Option (List RootRef) :=
  (env.ctx.varRoots.find? (·.1 == x)).map (·.2)

def rootTarget : RootRef → Option Target
  | .local _ => none
  | .global g => some (.global g)
  | .param i => some (.param i)

def rootsTargets (rs : List RootRef) : List Target := rs.filterMap rootTarget

def addTargets (old new : List Target) : List Target :=
  new.foldl (fun acc t => if acc.contains t then acc else acc ++ [t]) old

def addRoots (rs : List RootRef) (upd : Eff → List Target → Eff) : P Unit :=
  modify fun s => { s with eff := upd s.eff (rootsTargets rs) }

def addReads (rs : List RootRef) : P Unit :=
  addRoots rs fun e ts => { e with reads := addTargets e.reads ts }

def addWrites (rs : List RootRef) : P Unit :=
  addRoots rs fun e ts => { e with writes := addTargets e.writes ts }

def addGrows (rs : List RootRef) : P Unit :=
  addRoots rs fun e ts => { e with grows := addTargets e.grows ts }

def noteAborts : P Unit := modify fun s => { s with eff := { s.eff with aborts := true } }

def noteOutputs : P Unit := modify fun s => { s with eff := { s.eff with outputs := true } }

def unionRoots (a b : List RootRef) : List RootRef :=
  b.foldl (fun acc r => if acc.contains r then acc else acc ++ [r]) a

def subsetRoots (a b : List RootRef) : Bool := a.all b.contains

def showRoot : RootRef → String
  | .local x => s!"local {x}"
  | .global g => s!"global {g}"
  | .param i => s!"param {i}"

def showRoots (rs : List RootRef) : String := "{" ++ ", ".intercalate (rs.map showRoot) ++ "}"

/-- Statement and expression operators that may abort, per the summary rules. -/
def BinOp.mayAbort : BinOp → Bool
  | .add | .sub | .mul | .div | .mod => true
  | _ => false

/-- Each local root is declared in an open scope that is the binder's scope or
an enclosing one; `xpos` is the binder's position in `chain`. -/
def checkOutlives (env : PEnv) (chain : List Nat) (lv : LocalVar) (xpos : Nat) : List RootRef → V Unit
  | [] => pure ()
  | .local y :: rest =>
    match env.impl.vars[y]? with
    | none => reject .root s!"root names variable {y}, outside the variable table"
    | some ly => do
      unless chain.contains ly.scope do
        reject .root s!"root {ly.name} of {lv.name} is not declared in an open scope"
      unless chain.idxOf ly.scope ≥ xpos do
        reject .root s!"root {ly.name} ends before {lv.name}"
      checkOutlives env chain lv xpos rest
  | _ :: rest => checkOutlives env chain lv xpos rest

/-- The roots a value bound to `x` may have must lie in `x`'s annotation, and
each must outlive `x`: a parameter, a global, or a local of `x`'s scope or an
enclosing one. `chain` lists the open scopes, innermost first, and holds `x`'s
scope. -/
def bindRootsV (env : PEnv) (chain : List Nat) (x : VarId) (rho : List RootRef) : V Unit := do
  let some lv := env.impl.vars[x]? | reject .root s!"variable {x} outside the variable table"
  let some ann := env.ann x | reject .root s!"variable {x} has no root annotation"
  unless subsetRoots rho ann do
    reject .root s!"variable {lv.name} is bound to roots {showRoots rho} outside its annotation {showRoots ann}"
  checkOutlives env chain lv (chain.idxOf lv.scope) rho

def bindRoots (env : PEnv) (chain : List Nat) (x : VarId) (rho : List RootRef) : P Unit :=
  liftV (bindRootsV env chain x rho)

def checkNoLocal : List RootRef → V Unit
  | [] => pure ()
  | .local y :: _ => reject .result s!"a returned reference or slice is rooted at local variable {y}"
  | _ :: rest => checkNoLocal rest

/-- `V-RESULT`: what a function returns is rooted at the caller's storage, and
within what its context declares. -/
def checkResultV (env : PEnv) (rho : List RootRef) : V Unit := do
  checkNoLocal rho
  match env.ctx.resultRoots with
  | [declared] =>
    unless subsetRoots rho declared do
      reject .result s!"a returned value is rooted at {showRoots rho}, the context declares {showRoots declared}"
  | _ => reject .result "the context does not declare roots for the single result"

def checkResult (env : PEnv) (rho : List RootRef) : P Unit := liftV (checkResultV env rho)

/-- Map a callee's root set to the caller's, given the roots of each argument. -/
def mapCalleeRoots (argRoots : List (List RootRef)) : RootRef → V (List RootRef)
  | .param j =>
    match argRoots[j]? with
    | some rs => pure rs
    | none => reject .call s!"callee result roots name parameter {j}, which has no argument"
  | .global g => pure [.global g]
  | .local y => reject .call s!"callee result roots name its local {y}"

/-- The caller's roots of a result the callee declares rooted at `rs`, added to `acc`. -/
def mapResultRoots (argRoots : List (List RootRef)) : List RootRef → List RootRef → V (List RootRef)
  | acc, [] => pure acc
  | acc, r :: rest => do
    let mapped ← mapCalleeRoots argRoots r
    mapResultRoots argRoots (unionRoots acc mapped) rest

/-- The globals the callee context knows parameter `j` may be rooted at. A
summary entry for the parameter stands for them in the callee's own check, so
it stands for them at the call too. -/
def paramGlobals (callee : Impl) (cctx : Context) (j : Nat) : List Target :=
  match callee.vars[j]?, cctx.varRoots.find? (·.1 == j) with
  | some lv, some (_, rs) =>
    if lv.ty.isRefLike then
      rs.filterMap fun r => match r with
        | .global g => some (Target.global g)
        | _ => none
    else []
  | _, _ => []

def mapSummaryTargets (argRoots : List (List RootRef)) : List Target → List Target
  | [] => []
  | .global g :: rest => .global g :: mapSummaryTargets argRoots rest
  | .param j :: rest =>
    rootsTargets (argRoots[j]?.getD []) ++ mapSummaryTargets argRoots rest

/-- A callee's summary targets as the caller's: an entry for parameter `j`
stands for the argument's roots and for the globals the callee context lists
for the parameter. -/
def mapCallTargets (callee : Impl) (cctx : Context) (argRoots : List (List RootRef)) :
    List Target → List Target
  | [] => []
  | .global g :: rest => .global g :: mapCallTargets callee cctx argRoots rest
  | .param j :: rest =>
    rootsTargets (argRoots[j]?.getD []) ++ paramGlobals callee cctx j
      ++ mapCallTargets callee cctx argRoots rest

/-- The callee context's assumption about parameter `i` holds for its argument. -/
def checkArgRoots (callee : Impl) (cctx : Context) (argRoots : List (List RootRef)) (i : Nat) : V Unit :=
  match callee.params[i]? with
  | none => pure ()
  | some p =>
    match callee.vars[p.var]? with
    | some pv =>
      if pv.ty.isRefLike then
        match cctx.varRoots.find? (·.1 == p.var) with
        | none => reject .call s!"callee {callee.name} has no root annotation for parameter {i}"
        | some (_, ann) =>
          unless ann == [.param i] do
            let actual := argRoots[i]?.getD []
            unless subsetRoots actual ann do
              reject .call s!"argument {i} of {callee.name} is rooted at {showRoots actual}, the callee context assumes {showRoots ann}"
      else pure ()
    | none => reject .call s!"callee {callee.name} has no variable row for parameter {i}"

/-- `V-BLOCK`: the value must not be rooted at a variable of the block, which
are the variables numbered from `n0` up to `n1`. -/
def checkBlockValue (n0 n1 : Nat) : List RootRef → V Unit
  | [] => pure ()
  | .local y :: rest =>
    if n0 ≤ y ∧ y < n1 then
      reject .block s!"the value of a block is rooted at variable {y}, declared inside it"
    else checkBlockValue n0 n1 rest
  | _ :: rest => checkBlockValue n0 n1 rest

/-- The effects of a call added to `e`: the callee's summary through the
argument roots, or everything when the summary is unknown. -/
def callEffects (callee : Impl) (cctx : Context) (argRoots : List (List RootRef)) (e : Eff) : Eff :=
  match callee.summary with
  | .unknown => { e with unknown := true }
  | .known sm =>
    { e with
      reads := addTargets e.reads (mapCallTargets callee cctx argRoots sm.reads)
      writes := addTargets e.writes (mapCallTargets callee cctx argRoots sm.writes)
      grows := addTargets e.grows (mapCallTargets callee cctx argRoots sm.grows)
      aborts := e.aborts || sm.aborts
      outputs := e.outputs || sm.outputs }

/-- The caller's roots of what a call yields. -/
def callResultRoots (callee : Impl) (cctx : Context) (argRoots : List (List RootRef)) : V (List RootRef) :=
  match callee.results.toList, cctx.resultRoots with
  | [t], [rs] =>
    if t.isRefLike then mapResultRoots argRoots [] rs
    else pure []
  | _, _ => pure []

/-- The roots of a value read from a place: a reference or slice variable
yields its annotation, anything else a value that holds no reference. -/
def readRoots (env : PEnv) : Place → P (List RootRef)
  | .var x =>
    match env.impl.vars[x]? with
    | some lv =>
      if lv.ty.isRefLike then
        match env.ann x with
        | some ann => pure ann
        | none => rejP .root s!"variable {lv.name} has no root annotation"
      else pure []
    | none => pure []
  | _ => pure []

mutual

def rpPlace (env : PEnv) : Place → P (List RootRef)
  | .var x => pure [.local x]
  | .global g => pure [.global g]
  | .deref e => rpExpr env e
  | .elem v i _ => do
    let rho ← rpView env v
    let _ ← rpExpr env i
    noteAborts
    pure rho

/-- Sampling an owner's run reads its header. -/
def rpView (env : PEnv) : View → P (List RootRef)
  | .of p => do
    let rho ← rpPlace env p
    addReads rho
    pure rho
  | .val e => rpExpr env e

def rpBound (env : PEnv) : Bound → P Unit
  | .omitted => pure ()
  | .expr e => do let _ ← rpExpr env e
  | .fromEnd e => do let _ ← rpExpr env e

def rpExpr (env : PEnv) : Expr → P (List RootRef)
  | .lit _ _ => pure []
  | .bool _ => pure []
  | .read p => do
    let rho ← rpPlace env p
    addReads rho
    readRoots env p
  | .ref _ p => rpPlace env p
  | .slice _ v lo hi _ => do
    let rho ← rpView env v
    rpBound env lo
    rpBound env hi
    noteAborts
    pure rho
  | .len v => do
    let _ ← rpView env v
    pure []
  | .un op a _ => do
    let _ ← rpExpr env a
    match op with
    | .neg => noteAborts
    | .bitnot => pure ()
    pure []
  | .bin op a b _ => do
    let _ ← rpExpr env a
    let _ ← rpExpr env b
    if op.mayAbort then noteAborts
    pure []
  | .cmp _ a b => do
    let _ ← rpExpr env a
    let _ ← rpExpr env b
    pure []
  | .and a b => do
    let _ ← rpExpr env a
    let _ ← rpExpr env b
    pure []
  | .or a b => do
    let _ ← rpExpr env a
    let _ ← rpExpr env b
    pure []
  | .not a => do
    let _ ← rpExpr env a
    pure []
  | .conv k _ a _ => do
    let _ ← rpExpr env a
    match k with
    | .as => noteAborts
    | _ => pure ()
    pure []
  | .call c args _ => do
    let argRoots ← rpArgs env args
    rpCall env c argRoots
  | .push owner a => do
    let rho ← rpPlace env owner
    let _ ← rpExpr env a
    addGrows rho
    pure rho
  | .ifE c t f => do
    let _ ← rpExpr env c
    let (rt, lt) ← rpBlockValue env [] t
    let (rf, lf) ← rpBlockValue env [] f
    let _ := (lt, lf)
    pure (unionRoots rt rf)
  | .blockE b => do
    let (rho, _) ← rpBlockValue env [] b
    pure rho
  | .arrLit _ es => do
    rpExprs env es
    pure []
  | .fill _ a => do
    let _ ← rpExpr env a
    pure []

def rpExprs (env : PEnv) : List Expr → P Unit
  | [] => pure ()
  | e :: rest => do
    let _ ← rpExpr env e
    rpExprs env rest

/-- Roots of each argument; a by-reference argument is rooted where its place is. -/
def rpArgs (env : PEnv) : List Arg → P (List (List RootRef))
  | [] => pure []
  | .byVal e :: rest => do
    let rho ← rpExpr env e
    pure (rho :: (← rpArgs env rest))
  | .byRef _ p :: rest => do
    let rho ← rpPlace env p
    pure (rho :: (← rpArgs env rest))

/-- A call: the callee context's parameter assumptions must hold for these
arguments, its result roots are mapped to the caller's, and its summary is
mapped to the caller's targets. -/
def rpCall (env : PEnv) (c : ContextId) (argRoots : List (List RootRef)) : P (List RootRef) := do
  let some cctx := env.mod.contexts[c]? | rejP .call s!"call of context {c}, outside the context table"
  let some callee := env.mod.impls[cctx.impl]? | rejP .call s!"context {c} names a missing implementation"
  liftV (forAll (List.range callee.params.size) (checkArgRoots callee cctx argRoots))
  modify fun s => { s with eff := callEffects callee cctx argRoots s.eff }
  liftV (callResultRoots callee cctx argRoots)

/-- Check a block and return the roots of its value together with the range
of variable ids it declares (`pre` included). -/
def rpBlockValue (env : PEnv) (pre : List VarId) : Block → P (List RootRef × (Nat × Nat))
  | .mk sc stmts value => do
    let st0 ← get
    -- The variables a construct declares are the next ones in declaration order.
    (if pre.all (fun x => st0.nextVar ≤ x && x < st0.nextVar + pre.length) then pure ()
      else rejP .root s!"block {sc} binds a variable out of declaration order" : P Unit)
    modify fun s => { s with nextVar := s.nextVar + pre.length }
    rpStmts { env with scopes := sc :: env.scopes } stmts
    let rho ← (match value with
      | none => pure []
      | some e => rpExpr { env with scopes := sc :: env.scopes } e)
    let st1 ← get
    liftV (checkBlockValue st0.nextVar st1.nextVar rho)
    pure (rho, (st0.nextVar, st1.nextVar))

def rpStmts (env : PEnv) : List Stmt → P Unit
  | [] => pure ()
  | s :: rest => do
    rpStmt env s
    rpStmts env rest

def rpPrintArgs (env : PEnv) : List PrintArg → P Unit
  | [] => pure ()
  | .text _ :: rest => rpPrintArgs env rest
  | .expr e :: rest => do
    let _ ← rpExpr env e
    rpPrintArgs env rest

def rpStmt (env : PEnv) : Stmt → P Unit
  | .letS x e _ => do
    -- A `let` declares the next variable in declaration order.
    unless x = (← get).nextVar do rejP .root s!"variable {x} is declared out of order"
    modify fun s => { s with nextVar := s.nextVar + 1 }
    let rho ← rpExpr env e
    match env.impl.vars[x]? with
    | some lv =>
      if lv.ty.isRefLike then bindRoots env env.scopes x rho
    | none => rejP .root s!"variable {x} outside the variable table"
  | .assign p e _ => do
    let rho ← rpPlace env p
    let _ ← rpExpr env e
    addWrites rho
  | .assignOp op p e _ => do
    let rho ← rpPlace env p
    let _ ← rpExpr env e
    addReads rho
    addWrites rho
    if op.mayAbort then noteAborts
  | .rebind x e _ => do
    let rho ← rpExpr env e
    bindRoots env env.scopes x rho
    if x < env.impl.params.size then
      modify fun s => { s with eff := { s.eff with rebinds := addTargets s.eff.rebinds [.param x] } }
  | .expr e _ => do
    let _ ← rpExpr env e
  | .append owner src _ => do
    let rho ← rpPlace env owner
    -- The appended elements are copied out of the run.
    let run ← rpView env src
    addReads run
    addGrows rho
  | .ifS c t f _ => do
    let _ ← rpExpr env c
    let _ ← rpBlockValue env [] t
    match f with
    | some b => do let _ ← rpBlockValue env [] b
    | none => pure ()
  | .while c b _ => do
    let _ ← rpExpr env c
    let _ ← rpBlockValue env [] b
  | .forRange x lo hi b _ => do
    let _ ← rpExpr env lo
    let _ ← rpExpr env hi
    let _ ← rpBlockValue env [x] b
  | .forEach x idx v byRef b _ => do
    let rho ← rpView env v
    -- A loop over values copies each element out of the run.
    if byRef then bindRoots env (b.scope :: env.scopes) x rho else addReads rho
    let _ ← rpBlockValue env (x :: idx.toList) b
  | .ret e _ => do
    match e with
    | none => pure ()
    | some e => do
      let rho ← rpExpr env e
      checkResult env rho
  | .brk _ => pure ()
  | .cont _ => pure ()
  | .print args _ => do
    rpPrintArgs env args
    noteOutputs
  | .assertS e _ => do
    let _ ← rpExpr env e
    noteAborts
  | .abort _ _ => noteAborts
  | .exit e _ => do
    let _ ← rpExpr env e
    noteAborts

end


/-- Where the annotation of `x` may point, by kind of variable. -/
def checkAnnotationShape (m : Module) (impl : Impl) (ctx : Context) : V Unit := do
  for (x, rs) in ctx.varRoots do
    match impl.vars[x]? with
    | none => reject .root s!"annotation for variable {x}, outside the variable table"
    | some lv =>
      unless lv.ty.isRefLike do
        reject .root s!"annotation for variable {lv.name}, which is not a reference or slice"
      for r in rs do
        match r with
        | .local y =>
          match impl.vars[y]? with
          | none => reject .root s!"root of {lv.name} names variable {y}, outside the variable table"
          | some ly =>
            if ly.ty.isRefLike then reject .root s!"root of {lv.name} names {ly.name}, which holds a reference"
        | .global g =>
          unless g < m.globals.size do reject .root s!"root of {lv.name} names global {g}, outside the global table"
        | .param i =>
          unless i < impl.params.size do reject .root s!"root of {lv.name} names parameter {i}, which does not exist"
  for h : x in [0:impl.vars.size] do
    if impl.vars[x].ty.isRefLike then
      let n := (ctx.varRoots.filter (·.1 == x)).length
      unless n = 1 do
        reject .root s!"variable {impl.vars[x].name} has {n} root annotations, expected one"
  -- A parameter is rooted at what the caller passes, or at one global the
  -- specialization knows.
  forAll (List.range impl.params.size) fun i =>
    match ctx.varRoots.find? (·.1 == i) with
    | none => pure ()
    | some (_, rs) =>
      forAll rs fun r =>
        match r with
        | .param j => unless j = i do reject .root s!"parameter {i} is annotated with the roots of parameter {j}"
        | .local _ => reject .root s!"parameter {i} is annotated with a local root"
        | .global _ => pure ()

def checkResultShape (m : Module) (impl : Impl) (ctx : Context) : V Unit := do
  unless ctx.resultRoots.length = impl.results.size do
    reject .result s!"the context declares {ctx.resultRoots.length} result root sets for {impl.results.size} results"
  for (t, rs) in impl.results.toList.zip ctx.resultRoots do
    if !t.isRefLike && !rs.isEmpty then
      reject .result "result roots declared for a result that holds no reference"
    for r in rs do
      match r with
      | .local _ => reject .result "a declared result root is a local variable"
      | .global g =>
        unless g < m.globals.size do reject .result s!"result root names global {g}, outside the global table"
      | .param j =>
        match impl.vars[j]? with
        | some lv =>
          unless j < impl.params.size && lv.ty.isRefLike do
            reject .result s!"result root names parameter {j}, which holds no reference"
        | none => reject .result s!"result root names parameter {j}, which does not exist"

/-- Targets the context's annotation lets a summary entry stand for. -/
def expandTargets (impl : Impl) (ctx : Context) (ts : List Target) : List Target :=
  ts.flatMap fun t =>
    match t with
    | .global _ => [t]
    | .param i =>
      match impl.vars[i]?, ctx.varRoots.find? (·.1 == i) with
      | some lv, some (_, rs) => if lv.ty.isRefLike then rootsTargets rs else [t]
      | _, _ => [t]

def showTarget : Target → String
  | .param i => s!"parameter {i}"
  | .global g => s!"global {g}"

/-- Every effect found is among those declared. -/
def effWithin (name what : String) (found declared : List Target) : V Unit :=
  match found.find? (fun t => !declared.contains t) with
  | some t => reject .summary s!"{name} {what} {showTarget t}, which its summary omits"
  | none => pure ()

def checkSummary (impl : Impl) (ctx : Context) (eff : Eff) : V Unit := do
  match impl.summary with
  | .unknown => pure ()
  | .known s =>
    -- An entry for a parameter is read through that parameter's annotation, so
    -- it must name a parameter.
    forAll (s.reads ++ s.writes ++ s.grows) fun t =>
      match t with
      | .param i =>
        unless i < impl.params.size do
          reject .summary s!"{impl.name}: its summary names parameter {i}, which does not exist"
      | .global _ => pure ()
    if eff.unknown then
      reject .summary s!"{impl.name} calls an implementation whose summary is unknown, so its own summary cannot be known"
    effWithin impl.name "reads" eff.reads (expandTargets impl ctx s.reads)
    effWithin impl.name "writes" eff.writes (expandTargets impl ctx s.writes)
    effWithin impl.name "grows" eff.grows (expandTargets impl ctx s.grows)
    effWithin impl.name "rebinds" eff.rebinds s.rebinds
    if eff.aborts && !s.aborts then reject .summary s!"{impl.name} may abort, which its summary omits"
    if eff.outputs && !s.outputs then reject .summary s!"{impl.name} prints, which its summary omits"

/-- Check one context against its implementation. -/
def checkContext (m : Module) (ctx : Context) : V Unit := do
  let some impl := m.impls[ctx.impl]? | reject .root s!"context {ctx.decl}: no such implementation"
  checkAnnotationShape m impl ctx
  checkResultShape m impl ctx
  let env : PEnv := ⟨m, impl, ctx, []⟩
  let ((), st) ← (do
      let (rho, _) ← rpBlockValue env [] impl.body
      if impl.body.value.isSome then checkResult env rho : P Unit).run ⟨impl.params.size, {}⟩
  checkSummary impl ctx st.eff

/-- An implementation and context with no variables, parameters or results:
what a global initializer is checked against. -/
def initImpl : Impl := ⟨"", #[], #[], #[], .mk 0 [] none, .unknown⟩

def initContext : Context := ⟨0, "", [], []⟩

/-- A global's initializer runs before the later globals exist. Its roots and
effects are computed like a function body's, and nothing it reads, writes or
grows, itself or through the calls it makes, may be a global that is not yet
initialized. -/
def checkInitRoots (m : Module) (g : GlobalId) : V Unit :=
  match m.globals[g]? with
  | none => pure ()
  | some gl => do
    let (_, st) ← (rpExpr ⟨m, initImpl, initContext, []⟩ gl.init).run ⟨0, {}⟩
    if st.eff.unknown then
      reject .call s!"initializer of global {gl.name} calls an implementation whose effects are unknown"
    forAll (st.eff.reads ++ st.eff.writes ++ st.eff.grows) fun t =>
      match t with
      | .global h =>
        unless h < g do
          reject .call s!"initializer of global {gl.name} reaches global {h}, which is not initialized before it"
      | .param _ => pure ()

end Goose.Core
