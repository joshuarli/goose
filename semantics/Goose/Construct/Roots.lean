import Goose.Construct.Access



namespace Goose.Construct
open Goose.Core (V reject forAll Rule VarId GlobalId ContextId BinOp)


structure Eff where
  reads : List Target := []
  writes : List Target := []
  grows : List Target := []
  shrinks : List Target := []
  rebinds : List Target := []
  aborts : Bool := false
  outputs : Bool := false
  
  unknown : Bool := false

structure RState where
  
  nextVar : Nat
  eff : Eff

abbrev P := StateT RState V

structure PEnv where
  mod : Module
  impl : Impl
  ctx : Context
  
  scopes : List Nat

def rejP (r : Rule) (msg : String) : P α := throw ⟨r, msg⟩


def liftV (x : V α) : P α := fun s =>
  match x with
  | .ok a => .ok (a, s)
  | .error e => .error e

def PEnv.ann (env : PEnv) (x : VarId) : Option (List RootRef) :=
  (env.ctx.varRoots.find? (·.1 == x)).map (·.2)


def PEnv.cont (env : PEnv) (x : VarId) : Option (List RootRef) :=
  (env.ctx.contentRoots.find? (·.1 == x)).map (·.2)

def PEnv.isRefSliceVar (env : PEnv) (x : VarId) : Bool :=
  match env.impl.vars[x]? with
  | some lv => lv.ty.isRefSlice
  | none => false

def rootTarget : RootRef → Option Target
  | .static | .local _ => none
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

def addShrinks (rs : List RootRef) : P Unit :=
  addRoots rs fun e ts => { e with shrinks := addTargets e.shrinks ts }

def PEnv.access (env : PEnv) : AccessEnv := ⟨env.mod, env.impl, env.ctx⟩

def PEnv.limitedOwner (env : PEnv) (p : Place) : V Bool :=
  match env.access.placeType? p with
  | some (.limited ..) => pure true
  | some _ => pure false
  | none => reject .type "owner has no checked declaration type"

def noteAborts : P Unit := modify fun s => { s with eff := { s.eff with aborts := true } }

def noteOutputs : P Unit := modify fun s => { s with eff := { s.eff with outputs := true } }

def unionRoots (a b : List RootRef) : List RootRef :=
  b.foldl (fun acc r => if acc.contains r then acc else acc ++ [r]) a

def subsetRoots (a b : List RootRef) : Bool := a.all b.contains

def showRoot : RootRef → String
  | .static => "static"
  | .local x => s!"local {x}"
  | .global g => s!"global {g}"
  | .param i => s!"param {i}"

def showRoots (rs : List RootRef) : String := "{" ++ ", ".intercalate (rs.map showRoot) ++ "}"


def binOpMayAbort : BinOp → Bool
  | .add | .sub | .mul | .div | .mod => true
  | _ => false


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


def checkResultV (env : PEnv) (rho : List RootRef) : V Unit := do
  checkNoLocal rho
  match env.ctx.resultRoots with
  | [declared] =>
    unless subsetRoots rho declared do
      reject .result s!"a returned value is rooted at {showRoots rho}, the context declares {showRoots declared}"
  | _ => reject .result "the context does not declare roots for the single result"

def checkResultChannels (env : PEnv) (actual : List (List RootRef)) : V Unit := do
  if actual.length != env.ctx.resultRoots.length then reject .result "result root channel count mismatch"
  for (roots, declared) in actual.zip env.ctx.resultRoots do
    checkNoLocal roots
    if !subsetRoots roots declared then reject .result "result roots exceed declared channel roots"

def checkResult (env : PEnv) (rho : List RootRef) : P Unit := liftV (checkResultV env rho)


def mapCalleeRoots (argRoots : List (List RootRef)) : RootRef → V (List RootRef)
  | .param j =>
    match argRoots[j]? with
    | some rs => pure rs
    | none => reject .call s!"callee result roots name parameter {j}, which has no argument"
  | .static => pure [.static]
  | .global g => pure [.global g]
  | .local y => reject .call s!"callee result roots name its local {y}"


def mapResultRoots (argRoots : List (List RootRef)) : List RootRef → List RootRef → V (List RootRef)
  | acc, [] => pure acc
  | acc, r :: rest => do
    let mapped ← mapCalleeRoots argRoots r
    mapResultRoots argRoots (unionRoots acc mapped) rest


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


def mapCallTargets (callee : Impl) (cctx : Context) (argRoots : List (List RootRef)) :
    List Target → List Target
  | [] => []
  | .global g :: rest => .global g :: mapCallTargets callee cctx argRoots rest
  | .param j :: rest =>
    rootsTargets (argRoots[j]?.getD []) ++ paramGlobals callee cctx j
      ++ mapCallTargets callee cctx argRoots rest


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


def checkBlockValue (n0 n1 : Nat) : List RootRef → V Unit
  | [] => pure ()
  | .local y :: rest =>
    if n0 ≤ y ∧ y < n1 then
      reject .block s!"the value of a block is rooted at variable {y}, declared inside it"
    else checkBlockValue n0 n1 rest
  | _ :: rest => checkBlockValue n0 n1 rest


def callEffects (callee : Impl) (cctx : Context) (argRoots : List (List RootRef)) (e : Eff) : Eff :=
  match callee.summary with
  | .unknown =>
    { e with writes := addTargets e.writes (rootsTargets argRoots.flatten), unknown := true }
  | .known sm =>
    { e with
      reads := addTargets e.reads (mapCallTargets callee cctx argRoots sm.reads)
      writes := addTargets e.writes (mapCallTargets callee cctx argRoots sm.writes)
      grows := addTargets e.grows (mapCallTargets callee cctx argRoots sm.grows)
      shrinks := addTargets e.shrinks (mapCallTargets callee cctx argRoots sm.shrinks)
      rebinds := addTargets e.rebinds (mapCallTargets callee cctx argRoots sm.rebinds)
      aborts := e.aborts || sm.aborts
      outputs := e.outputs || sm.outputs }


def callResultRoots (callee : Impl) (context : Context) (arguments : List (List RootRef)) : V (List RootRef) := do
  if callee.results.size != context.resultRoots.length then reject .result "call result root channel count mismatch"
  let mut roots := []
  for (descriptor, declared) in callee.results.toList.zip context.resultRoots do
    if descriptor.ty.isRefLike then
      roots := unionRoots roots (← mapResultRoots arguments [] declared)
  pure roots


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
  | .deref (.read (.var x)) =>

    if env.isRefSliceVar x then
      match env.cont x with
      | some cont => pure cont
      | none => rejP .root s!"variable {x} has no content roots"
    else pure []
  | _ => pure []


def checkStore (env : PEnv) (p : Place) (rho : List RootRef) : V Unit :=
  match p.derefVar? with
  | some x =>
    if env.isRefSliceVar x then
      match env.cont x with
      | some cont =>
        unless subsetRoots rho cont do
          reject .root s!"a slice rooted at {showRoots rho} is stored through variable {x}, whose content roots are {showRoots cont}"
      | none => reject .root s!"variable {x} has no content roots"
    else pure ()
  | none => pure ()


def storeRebinds (env : PEnv) (p : Place) : List Target :=
  match p.derefVar? with
  | some x => if env.isRefSliceVar x && x < env.impl.params.size then [.param x] else []
  | none => []


def asCall (x : V Unit) : V Unit :=
  match x with
  | .ok u => .ok u
  | .error e => .error ⟨.call, e.message⟩


def checkContent (env : PEnv) (cctx : Context) (args : List Arg) (argRoots : List (List RootRef))
    (i : Nat) : V Unit :=
  match (cctx.contentRoots.find? (·.1 == i)).map (·.2) with
  | none => pure ()
  | some cont => do
    let inst ← mapResultRoots argRoots [] cont
    match args[i]? with
    | some (.byRef _ (.var s)) =>
      match env.ann s with
      | some ann => do
        unless subsetRoots ann inst do
          reject .call s!"argument {i}: the callee context's content roots {showRoots inst} do not cover the roots {showRoots ann} of the slice variable passed"
        asCall (bindRootsV env env.scopes s inst)
      | none => reject .call s!"argument {i}: the slice variable passed has no root annotation"
    | some (.byRef _ (.deref (.read (.var q)))) =>
      match env.cont q with
      | some cq =>
        unless subsetRoots inst cq && subsetRoots cq inst do
          reject .call s!"argument {i}: the callee context's content roots {showRoots inst} differ from the content roots {showRoots cq} of the reference passed"
      | none => reject .call s!"argument {i}: the reference passed has no content roots"
    | _ => reject .call s!"argument {i}: the callee context declares content roots for an argument that is no slice variable"

def checkContents (env : PEnv) (c : ContextId) (args : List Arg) (argRoots : List (List RootRef)) :
    V Unit :=
  match env.mod.contexts[c]? with
  | none => pure ()
  | some cctx => forAll (List.range args.length) (checkContent env cctx args argRoots)

mutual

def rpPlace (env : PEnv) : Place → P (List RootRef)
  | .var x => pure [.local x]
  | .global g => pure [.global g]
  | .deref e => rpExpr env e
  | .field owner _ => rpPlace env owner
  | .elem v i _ => do
    let rho ← rpView env v
    let _ ← rpExpr env i
    noteAborts
    pure rho


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
    if binOpMayAbort op then noteAborts
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
    liftV (checkContents env c args argRoots)
    rpCall env c argRoots
  | .push owner a _ => do
    let rho ← rpPlace env owner
    let _ ← rpExpr env a
    addGrows rho
    addWrites rho
    if (← liftV (env.limitedOwner owner)) then noteAborts
    pure rho
  | .pop owner _ => do
    let rho ← rpPlace env owner
    addReads rho
    addShrinks rho
    noteAborts
    pure []
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
  | .structLit _ es => do
    rpExprs env es
    pure []
  | .fill _ a => do
    let _ ← rpExpr env a
    pure []
  | .bytes ty _ _ => match ty with
    | .slice .. => pure [.static]
    | _ => pure []
  | .str ty args _ => do
    rpPrintArgs env args
    if (match ty with | .limited .. => true | _ => false) then noteAborts
    pure []
  | .copy ty source _ => do
    if (match ty with | .limited .. => true | _ => false) then noteAborts
    let roots ← rpPlace env source
    addReads roots
    pure []
  | .resultLocal _ _ => pure []
  | .values operands => do
    rpExprs env operands
    let roots ← liftV (env.access.resultRoots (.values operands))
    pure roots.flatten.eraseDups

def rpExprs (env : PEnv) : List Expr → P Unit
  | [] => pure ()
  | e :: rest => do
    let _ ← rpExpr env e
    rpExprs env rest


def rpArgs (env : PEnv) : List Arg → P (List (List RootRef))
  | [] => pure []
  | .byVal e :: rest | .construct e :: rest => do
    let rho ← rpExpr env e
    pure (rho :: (← rpArgs env rest))
  | .byRef _ p :: rest => do
    let rho ← rpPlace env p
    pure (rho :: (← rpArgs env rest))


def rpCall (env : PEnv) (c : ContextId) (argRoots : List (List RootRef)) : P (List RootRef) := do
  let some cctx := env.mod.contexts[c]? | rejP .call s!"call of context {c}, outside the context table"
  let some callee := env.mod.impls[cctx.impl]? | rejP .call s!"context {c} names a missing implementation"
  liftV (forAll (List.range callee.params.size) (checkArgRoots callee cctx argRoots))
  modify fun s => { s with eff := callEffects callee cctx argRoots s.eff }
  liftV (callResultRoots callee cctx argRoots)


def rpBlockValue (env : PEnv) (pre : List VarId) : Block → P (List RootRef × (Nat × Nat))
  | .mk sc stmts value => do
    let st0 ← get

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

def rpReturnOperands (env : PEnv) : List (List RootRef) → List Expr → P Unit
  | [], [] => pure ()
  | roots :: channels, operand :: operands => do
      let actual ← rpExpr env operand
      liftV (checkNoLocal actual)
      if !subsetRoots actual roots then rejP .result "returned roots exceed declared channel roots"
      rpReturnOperands env channels operands
  | _, _ => rejP .result "returned roots channel count mismatch"

def rpNoLocalOperands (env : PEnv) : List Expr → P Unit
  | [] => pure ()
  | operand :: operands => do
      let roots ← rpExpr env operand
      liftV (checkNoLocal roots)
      rpNoLocalOperands env operands

def rpStmts (env : PEnv) : List Stmt → P Unit
  | [] => pure ()
  | s :: rest => do
    rpStmt env s
    rpStmts env rest

def rpPrintArgs (env : PEnv) : List PrintArg → P Unit
  | [] => pure ()
  | .text _ :: rest => rpPrintArgs env rest
  | .view view :: rest => do
    let _ ← rpView env view
    rpPrintArgs env rest
  | .expr e :: rest => do
    let _ ← rpExpr env e
    rpPrintArgs env rest

def rpStmt (env : PEnv) : Stmt → P Unit
  | .letS x e _ => do

    unless x = (← get).nextVar do rejP .root s!"variable {x} is declared out of order"
    modify fun s => { s with nextVar := s.nextVar + 1 }
    let rho ← rpExpr env e
    match env.impl.vars[x]? with
    | some lv =>
      if lv.ty.isRefLike then bindRoots env env.scopes x rho
    | none => rejP .root s!"variable {x} outside the variable table"
  | .assign p e _ => do
    let rho ← rpPlace env p
    let stored ← rpExpr env e
    liftV (checkStore env p stored)
    addWrites rho

    modify fun s => { s with eff := { s.eff with rebinds := addTargets s.eff.rebinds (storeRebinds env p) } }
  | .assignOp op p e _ => do
    let rho ← rpPlace env p
    let _ ← rpExpr env e
    addReads rho
    addWrites rho
    if binOpMayAbort op then noteAborts
  | .rebind x e _ => do
    let rho ← rpExpr env e
    bindRoots env env.scopes x rho
    if x < env.impl.params.size then
      modify fun s => { s with eff := { s.eff with rebinds := addTargets s.eff.rebinds [.param x] } }
  | .expr e _ => do
    let _ ← rpExpr env e
  | .append owner src _ => do
    let rho ← rpPlace env owner

    let run ← rpView env src
    addReads run
    addGrows rho
    addWrites rho
    if (← liftV (env.limitedOwner owner)) then noteAborts
  | .popN owner count _ => do
    let rho ← rpPlace env owner
    let _ ← rpExpr env count
    addReads rho
    addShrinks rho
    noteAborts
  | .resize owner size fill _ => do
    let rho ← rpPlace env owner
    let _ ← rpExpr env size
    match fill with
    | none => pure ()
    | some e =>
      let _ ← rpExpr env e
      addWrites rho
      addGrows rho
    addReads rho
    addShrinks rho
    noteAborts
  | .clear owner _ => do
    let rho ← rpPlace env owner
    addReads rho
    addShrinks rho
  | .assignWhole owner replacement _ => do
    let rho ← rpPlace env owner
    addReads rho
    addShrinks rho
    let _ ← rpExpr env replacement
    addWrites rho
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


    let st0 ← get
    (if x = st0.nextVar then pure () else rejP .root s!"variable {x} is declared out of order" : P Unit)
    modify fun s => { s with nextVar := s.nextVar + 1 }
    let _ ← rpExpr env lo
    let _ ← rpExpr env hi
    let body ← rpBlockValue env [] b

    liftV (checkBlockValue st0.nextVar body.2.1 body.1)
  | .forEach x idx v byRef b _ => do
    let st0 ← get
    (if x = st0.nextVar && idx.all (· == st0.nextVar + 1) then pure ()
      else rejP .root s!"variable {x} is declared out of order" : P Unit)
    modify fun s => { s with nextVar := s.nextVar + 1 + idx.toList.length }
    let rho ← rpView env v

    if byRef then bindRoots env (b.scope :: env.scopes) x rho else addReads rho
    let body ← rpBlockValue env [] b
    liftV (checkBlockValue st0.nextVar body.2.1 body.1)
  | .receive ids producer _ => do
    let _ ← rpExpr env producer
    for id in ids do
      modify fun state => { state with nextVar := state.nextVar + 1 }
      let some localVar := env.impl.vars[id]? | rejP .type "receive variable outside table"
      if localVar.ty.isRefLike then
        let roots ← liftV (env.access.resultRoots producer)
        let position := ids.idxOf id
        let some actual := roots[position]? | rejP .result "receive result channel missing"
        bindRoots env env.scopes id actual
  | .appendValue owner producer _ | .appendConstruct owner producer _ => do
    let roots ← rpPlace env owner
    let _ ← rpExpr env producer
    addGrows roots
    addWrites roots
    if (← liftV (env.limitedOwner owner)) then noteAborts
  | .retValues operands _ => do
    if operands.length != env.impl.results.size then rejP .result "result count mismatch"
    rpReturnOperands env env.ctx.resultRoots operands
  | .retForward producer _ => do
    let _ ← rpExpr env producer
    let actual ← liftV (env.access.resultRoots producer)
    liftV (checkResultChannels env actual)
  | .returnFrom target operands _ => do
    let some target := env.mod.targets[target]? | rejP .call "target outside table"
    let some implementation := env.mod.impls[target.first]? | rejP .call "target member outside table"
    if operands.length != implementation.results.size then rejP .result "target result count mismatch"
    rpNoLocalOperands env operands
  | .returnFromForward _ producer _ => do
    let roots ← rpExpr env producer
    liftV (checkNoLocal roots)
  | .breakValue expression _ => do let _ ← rpExpr env expression; pure ()
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
        | .static => pure ()
        | .param i =>
          unless i < impl.params.size do reject .root s!"root of {lv.name} names parameter {i}, which does not exist"
  for h : x in [0:impl.vars.size] do
    if impl.vars[x].ty.isRefLike then
      let n := (ctx.varRoots.filter (·.1 == x)).length
      unless n = 1 do
        reject .root s!"variable {impl.vars[x].name} has {n} root annotations, expected one"


  forAll (List.range impl.params.size) fun i =>
    match ctx.varRoots.find? (·.1 == i) with
    | none => pure ()
    | some (_, rs) =>
      forAll rs fun r =>
        match r with
        | .param j => unless j = i do reject .root s!"parameter {i} is annotated with the roots of parameter {j}"
        | .local _ => reject .root s!"parameter {i} is annotated with a local root"
        | .static | .global _ => pure ()


def checkContentShape (m : Module) (impl : Impl) (ctx : Context) : V Unit :=
  forAll ctx.contentRoots fun (x, cont) => do
    unless x < impl.params.size do
      reject .root s!"content roots for variable {x}, which is not a parameter"
    match impl.vars[x]? with
    | none => reject .root s!"content roots for variable {x}, outside the variable table"
    | some lv => do
      unless lv.ty.isRefSlice do
        reject .root s!"content roots for {lv.name}, which is not a reference to a slice"
      unless (ctx.varRoots.find? (·.1 == x)).map (·.2) == some [.param x] do
        reject .root s!"{lv.name} refers to a slice variable and is not annotated with its own parameter root"
      forAll cont fun r =>
        match r with
        | .param j =>
          unless j < impl.params.size do
            reject .root s!"content root of {lv.name} names parameter {j}, which does not exist"
        | .global g =>
          unless g < m.globals.size do
            reject .root s!"content root of {lv.name} names global {g}, outside the global table"
        | .static => pure ()
        | .local y => reject .root s!"content root of {lv.name} names local variable {y}"

def checkResultShape (m : Module) (impl : Impl) (ctx : Context) : V Unit := do
  unless ctx.resultRoots.length = impl.results.size do
    reject .result s!"the context declares {ctx.resultRoots.length} result root sets for {impl.results.size} results"
  for (t, rs) in impl.results.toList.zip ctx.resultRoots do
    if !t.ty.isRefLike && !rs.isEmpty then
      reject .result "result roots declared for a result that holds no reference"
    for r in rs do
      match r with
      | .static => pure ()
      | .local _ => reject .result "a declared result root is a local variable"
      | .global g =>
        unless g < m.globals.size do reject .result s!"result root names global {g}, outside the global table"
      | .param j =>
        match impl.vars[j]? with
        | some lv =>
          unless j < impl.params.size && lv.ty.isRefLike do
            reject .result s!"result root names parameter {j}, which holds no reference"
        | none => reject .result s!"result root names parameter {j}, which does not exist"


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


def effWithin (name what : String) (found declared : List Target) : V Unit :=
  match found.find? (fun t => !declared.contains t) with
  | some t => reject .summary s!"{name} {what} {showTarget t}, which its summary omits"
  | none => pure ()

def checkSummaryTargets (m : Module) (impl : Impl) (what : String) (targets : List Target) : V Unit :=
  forAll targets fun t =>
    match t with
    | .param i =>
      unless i < impl.params.size do
        reject .summary s!"{impl.name}: its {what} summary names parameter {i}, which does not exist"
    | .global g =>
      unless g < m.globals.size do
        reject .summary s!"{impl.name}: its {what} summary names global {g}, outside the global table"

def checkSummary (m : Module) (impl : Impl) (ctx : Context) (eff : Eff) : V Unit := do
  match impl.summary with
  | .unknown => pure ()
  | .known s =>
    checkSummaryTargets m impl "reads" s.reads
    checkSummaryTargets m impl "writes" s.writes
    checkSummaryTargets m impl "grows" s.grows
    checkSummaryTargets m impl "shrinks" s.shrinks
    checkSummaryTargets m impl "rebinds" s.rebinds
    if eff.unknown then
      reject .summary s!"{impl.name} calls an implementation whose summary is unknown, so its own summary cannot be known"
    effWithin impl.name "reads" eff.reads (expandTargets impl ctx s.reads)
    effWithin impl.name "writes" eff.writes (expandTargets impl ctx s.writes)
    effWithin impl.name "grows" eff.grows (expandTargets impl ctx s.grows)
    effWithin impl.name "shrinks" eff.shrinks (expandTargets impl ctx s.shrinks)
    effWithin impl.name "rebinds" eff.rebinds s.rebinds
    if eff.aborts && !s.aborts then reject .summary s!"{impl.name} may abort, which its summary omits"
    if eff.outputs && !s.outputs then reject .summary s!"{impl.name} prints, which its summary omits"


def checkContext (m : Module) (ctx : Context) : V Unit := do
  let some impl := m.impls[ctx.impl]? | reject .root s!"context {ctx.decl}: no such implementation"
  checkAnnotationShape m impl ctx
  checkResultShape m impl ctx
  checkContentShape m impl ctx
  let env : PEnv := ⟨m, impl, ctx, []⟩
  let ((), st) ← (do
      let (_, _) ← rpBlockValue env [] impl.body
      if impl.body.value.isSome then
        let actual ← liftV (env.access.blockResultRoots impl.body)
        liftV (checkResultChannels env actual) : P Unit).run ⟨impl.params.size, {}⟩
  checkSummary m impl ctx st.eff


def initImpl : Impl := ⟨"", #[], #[], #[], .mk 0 [] none, .unknown⟩

def initContext : Context := ⟨0, "", [], [], []⟩


def checkInitRoots (m : Module) (g : GlobalId) : V Unit :=
  match m.globals[g]? with
  | none => pure ()
  | some gl => do
    let (_, st) ← (rpExpr ⟨m, initImpl, initContext, []⟩ gl.init).run ⟨0, {}⟩
    if st.eff.unknown then
      reject .call s!"initializer of global {gl.name} calls an implementation whose effects are unknown"
    forAll (st.eff.reads ++ st.eff.writes ++ st.eff.grows ++ st.eff.shrinks) fun t =>
      match t with
      | .global h =>
        unless h < g do
          reject .call s!"initializer of global {gl.name} reaches global {h}, which is not initialized before it"
      | .param _ => pure ()

end Goose.Construct
