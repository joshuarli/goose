import Goose.Core.Roots

namespace Goose.Core

mutual
def Place.variables : Place → List VarId
  | .var x => [x]
  | .global _ => []
  | .deref e => e.variables
  | .elem v i _ => v.variables ++ i.variables
  | .field p _ => p.variables

termination_by x => sizeOf x

def View.variables : View → List VarId
  | .of p => p.variables
  | .val e => e.variables

termination_by x => sizeOf x

def Bound.variables : Bound → List VarId
  | .expr e | .fromEnd e => e.variables
  | .omitted => []

termination_by x => sizeOf x

def Expr.variables : Expr → List VarId
  | .lit .. | .bool _ => []
  | .read p | .ref _ p | .pop p _ => p.variables
  | .slice _ v lo hi _ => v.variables ++ lo.variables ++ hi.variables
  | .len v => v.variables
  | .un _ e _ | .not e | .conv _ _ e _ | .fill _ e => e.variables
  | .bin _ a b _ | .cmp _ a b | .and a b | .or a b => a.variables ++ b.variables
  | .call _ args _ => args.flatMap Arg.variables
  | .push p e _ => p.variables ++ e.variables
  | .ifE c t f => c.variables ++ t.variables ++ f.variables
  | .blockE b => b.variables
  | .arrLit _ es | .structLit _ es => es.flatMap Expr.variables

termination_by x => sizeOf x

def Arg.variables : Arg → List VarId
  | .byVal e => e.variables
  | .byRef _ p => p.variables

termination_by x => sizeOf x

def PrintArg.variables : PrintArg → List VarId
  | .text _ => []
  | .expr e => e.variables

termination_by x => sizeOf x

def Stmt.variables : Stmt → List VarId
  | .letS _ e _ | .rebind _ e _ | .expr e _ | .assertS e _ | .exit e _ => e.variables
  | .assign p e _ | .assignOp _ p e _ | .popN p e _ | .assignWhole p e _ => p.variables ++ e.variables
  | .resize p size fill _ => p.variables ++ size.variables ++ (match fill with | none => [] | some e => e.variables)
  | .clear p _ => p.variables
  | .append p v _ => p.variables ++ v.variables
  | .ifS c t f _ => c.variables ++ t.variables ++ (match f with | none => [] | some b => b.variables)
  | .while c b _ => c.variables ++ b.variables
  | .forRange _ lo hi b _ => lo.variables ++ hi.variables ++ b.variables
  | .forEach _ _ v _ b _ => v.variables ++ b.variables
  | .ret e _ => match e with | none => [] | some x => x.variables
  | .brk _ | .cont _ | .abort .. => []
  | .print args _ => args.flatMap PrintArg.variables

termination_by x => sizeOf x

def Block.variables : Block → List VarId
  | .mk _ ss value => ss.flatMap Stmt.variables ++ (match value with | none => [] | some e => e.variables)
termination_by x => sizeOf x

end

inductive AliasSource
  | variable (id : VarId)
  | operand (path : List Nat)
  | iteration (scope : Nat)
  deriving Repr

/-- A reference or sampled run kept until a consuming evaluation completes. -/
structure RetainedAlias where
  ty : Ty
  roots : List RootRef
  source : AliasSource
  deriving Repr

def Ty.interiorTarget? : Ty → Option Ty
  | .ref _ t => if t.ownerElem?.isSome then none else some t
  | .slice _ t => some t
  | _ => none

inductive DemandPhase
  | expression
  | place
  | view
  | bound
  | statement
  | block
  | mutation
  | call
  deriving DecidableEq, Repr

/-- Points follow evaluation order. Child positions extend the syntax path;
branches are visited in source order and loop bodies once with enclosing demand.
Only bindings active at loop entry contribute backedge demand. The wire supplies
no demand annotations, so a producer cannot suppress retained operands. -/
structure DemandPoint where
  path : List Nat
  phase : DemandPhase
  active : List VarId
  future : List VarId
  retained : List RetainedAlias
  deriving Repr

structure DemandOwner where
  ty : Option Ty
  roots : List RootRef
  deriving Repr

structure DemandEnv where
  access : AccessEnv
  active : List VarId
  future : List VarId
  retained : List RetainedAlias
  forbidden : List DemandOwner := []

abbrev DemandCheck := StateT (Array DemandPoint) V

def demandReject (rule : Rule) (message : String) : DemandCheck α := throw ⟨rule, message⟩

def demandLift (check : V α) : DemandCheck α := fun points => do
  let value ← check
  pure (value, points)

def recordDemand (env : DemandEnv) (path : List Nat) (phase : DemandPhase) : DemandCheck Unit :=
  modify fun points => points.push ⟨path, phase, env.active, env.future, env.retained⟩

def DemandEnv.withFuture (env : DemandEnv) (variables : List VarId) : DemandEnv :=
  { env with future := variables ++ env.future }

def DemandEnv.withAliases (env : DemandEnv) (aliases : List RetainedAlias) : DemandEnv :=
  { env with retained := aliases ++ env.retained }

def AccessEnv.aliasVariable (env : AccessEnv) (x : VarId) : V (Option RetainedAlias) := do
  let some lv := env.impl.vars[x]? | reject .type "demand names a missing variable"
  if lv.ty.isRefSlice then
    let roots ← env.contentRoots x
    match lv.ty with
    | .ref _ (.slice mu e) => pure (some ⟨.slice mu e, roots, .variable x⟩)
    | _ => reject .type "slice-reference variable has another type"
  else if lv.ty.interiorTarget?.isSome then
    pure (some ⟨lv.ty, ← env.variableRoots x, .variable x⟩)
  else pure none

def AccessEnv.aliasExpr (env : AccessEnv) (path : List Nat) (e : Expr) : V (List RetainedAlias) := do
  let some t := env.exprType? e | reject .type "retained expression has no checked type"
  if t.interiorTarget?.isSome then pure [⟨t, ← env.exprRoots e, .operand path⟩]
  else pure []

def AccessEnv.aliasPlace (env : AccessEnv) (path : List Nat) (p : Place) : V (List RetainedAlias) := do
  let some t := env.placeType? p | reject .type "retained place has no checked type"
  let rt := Ty.ref .mutable t
  if rt.interiorTarget?.isSome then pure [⟨rt, ← env.placeRoots p, .operand path⟩]
  else pure []

def AccessEnv.aliasView (env : AccessEnv) (path : List Nat) (v : View) : V (List RetainedAlias) := do
  let some t := env.viewElement? v | reject .type "retained run has no checked type"
  pure [⟨.slice .readOnly t, ← env.viewRoots v, .operand path⟩]

def AccessEnv.aliasArg (env : AccessEnv) (path : List Nat) : Arg → V (List RetainedAlias)
  | .byVal e => env.aliasExpr path e
  | .byRef _ p => do
    match env.placeType? p with
    | some (.slice mu e) => pure [⟨.slice mu e, ← env.exprRoots (.read p), .operand path⟩]
    | _ => env.aliasPlace path p

def AccessEnv.rootType? (env : AccessEnv) : RootRef → Option Ty
  | .local x => (env.impl.vars[x]?).map (·.ty)
  | .global g => (env.mod.globals[g]?).map (·.ty)
  | .param i => do
    let p ← env.impl.params[i]?
    let v ← env.impl.vars[p.var]?
    match v.ty with
    | .ref _ t => some t
    | _ => none

mutual
def Ty.containsFlat (whole part : Ty) : Bool :=
  whole == part || match whole with
    | .arr e _ => e.containsFlat part
    | .structT _ ts => ts.containsFlat part
    | _ => false

def TyList.containsFlat : TyList → Ty → Bool
  | .nil, _ => false
  | .cons t ts, part => t.containsFlat part || ts.containsFlat part
end

def rootsMayOverlap : RootRef → RootRef → Bool
  | .local x, .local y => x == y
  | .global x, .global y => x == y
  | .local _, .global _ | .global _, .local _ => false
  | .local _, .param _ | .param _, .local _ => false
  | .param _, _ | _, .param _ => true

def DemandOwner.invalidates (owner : DemandOwner) : Bool :=
  match owner.ty with
  | some (.grow _) | some (.growshrink _) | none => true
  | some _ => false

def DemandOwner.compatible (owner : DemandOwner) (alias : RetainedAlias) : Bool :=
  match owner.ty.bind Ty.ownerElem?, alias.ty.interiorTarget? with
  | some e, some t => e.containsFlat t
  | _, some _ => true
  | _, none => false

def DemandOwner.conflicts (owner : DemandOwner) (alias : RetainedAlias) : Bool :=
  owner.invalidates && owner.compatible alias &&
    owner.roots.any (fun target => alias.roots.any (rootsMayOverlap target))

def checkShrinkPoint (env : DemandEnv) (path : List Nat) (owner : DemandOwner) : DemandCheck Unit := do
  recordDemand env path .mutation
  for x in env.future do
    if env.active.contains x then
      match ← demandLift (env.access.aliasVariable x) with
      | none => pure ()
      | some alias =>
        if owner.conflicts alias then demandReject .shrink s!"shrink conflicts with demanded variable {x}"
  for alias in env.retained do
    if owner.conflicts alias then demandReject .shrink s!"shrink conflicts with retained {repr alias.source}"

def checkWholeRoots (env : DemandEnv) (roots : List RootRef) : DemandCheck Unit := do
  for owner in env.forbidden do
    if owner.roots.any (fun a => roots.any (rootsMayOverlap a)) then
      demandReject .whole "whole replacement depends on the cleared owner"

def AccessEnv.owner (env : AccessEnv) (p : Place) : V DemandOwner := do
  let some t := env.placeType? p | reject .type "shrink owner has no checked type"
  pure ⟨some t, ← env.placeRoots p⟩

def AccessEnv.targetOwners (env : AccessEnv) (callee : Impl) (ctx : Context)
    (actual : List (List RootRef)) (targets : List Target) : V (List DemandOwner) := do
  let mut owners := []
  for target in targets do
    match target with
    | .global g =>
      let some global := env.mod.globals[g]? | reject .summary "summary names a missing global"
      owners := owners ++ [⟨some global.ty, [.global g]⟩]
    | .param i =>
      let some roots := actual[i]? | reject .summary "summary names a missing argument"
      let globals := (paramGlobals callee ctx i).filterMap fun
        | .global g => some (.global g)
        | _ => none
      for root in roots ++ globals do
        owners := owners ++ [⟨env.rootType? root, [root]⟩]
  pure owners

def AccessEnv.unknownOwners (env : AccessEnv) (actual : List (List RootRef)) : List DemandOwner :=
  let globals := env.mod.globals.toList.zipIdx |>.filterMap fun (g, i) =>
    if g.ty.ownerElem?.isSome then some ⟨some g.ty, [.global i]⟩ else none
  globals ++ actual.flatten.map (fun r => ⟨env.rootType? r, [r]⟩)

def checkCallDemand (env : DemandEnv) (path : List Nat) (context : ContextId) (args : List Arg) : DemandCheck Unit := do
  recordDemand env path .call
  let some ctx := env.access.mod.contexts[context]? | demandReject .call "call has no context"
  let some callee := env.access.mod.impls[ctx.impl]? | demandReject .call "call has no implementation"
  let actual ← demandLift (env.access.argsRoots args)
  let owners ← match callee.summary with
    | .unknown => pure (env.access.unknownOwners actual)
    | .known sm => demandLift (env.access.targetOwners callee ctx actual sm.shrinks)
  for owner in owners do checkShrinkPoint env path owner
  unless env.forbidden.isEmpty do
    let effects ← match callee.summary with
      | .unknown => pure (env.access.unknownOwners actual)
      | .known sm => demandLift (env.access.targetOwners callee ctx actual
          (sm.reads ++ sm.writes ++ sm.grows ++ sm.shrinks ++ sm.rebinds))
    for owner in effects do checkWholeRoots env owner.roots

mutual
def demandPlace (env : DemandEnv) (path : List Nat) (p : Place) : DemandCheck Unit := do
  recordDemand env path .place
  checkWholeRoots env (← demandLift (env.access.placeRoots p))
  match p with
  | .var _ | .global _ => pure ()
  | .deref e => demandExpr env (path ++ [0]) e
  | .field owner _ => demandPlace env (path ++ [0]) owner
  | .elem v i _ =>
    demandView (env.withFuture i.variables) (path ++ [0]) v
    let aliases ← demandLift (env.access.aliasView (path ++ [0]) v)
    demandExpr (env.withAliases aliases) (path ++ [1]) i
termination_by sizeOf p

def demandView (env : DemandEnv) (path : List Nat) (v : View) : DemandCheck Unit := do
  recordDemand env path .view
  match v with
  | .of p => demandPlace env (path ++ [0]) p
  | .val e => demandExpr env (path ++ [0]) e
termination_by sizeOf v

def demandBound (env : DemandEnv) (path : List Nat) (b : Bound) : DemandCheck Unit := do
  recordDemand env path .bound
  match b with
  | .omitted => pure ()
  | .expr e | .fromEnd e => demandExpr env (path ++ [0]) e
termination_by sizeOf b

def demandExpr (env : DemandEnv) (path : List Nat) (e : Expr) : DemandCheck Unit := do
  recordDemand env path .expression
  match e with
  | .lit .. | .bool _ => pure ()
  | .read p =>
    demandPlace env (path ++ [0]) p
    checkWholeRoots env (← demandLift (env.access.exprRoots e))
  | .ref _ p => demandPlace env (path ++ [0]) p
  | .len v => demandView env (path ++ [0]) v
  | .slice _ v lo hi _ =>
    demandView (env.withFuture (lo.variables ++ hi.variables)) (path ++ [0]) v
    let aliases ← demandLift (env.access.aliasView (path ++ [0]) v)
    demandBound ((env.withAliases aliases).withFuture hi.variables) (path ++ [1]) lo
    demandBound (env.withAliases aliases) (path ++ [2]) hi
  | .un _ a _ | .not a | .conv _ _ a _ | .fill _ a => demandExpr env (path ++ [0]) a
  | .bin _ a b _ | .cmp _ a b | .and a b | .or a b =>
    demandExpr (env.withFuture b.variables) (path ++ [0]) a
    let aliases ← demandLift (env.access.aliasExpr (path ++ [0]) a)
    demandExpr (env.withAliases aliases) (path ++ [1]) b
  | .call c args _ =>
    let aliases ← demandArgs env path 0 args
    checkCallDemand (env.withAliases aliases) path c args
  | .push p a _ =>
    demandPlace (env.withFuture a.variables) (path ++ [0]) p
    let aliases ← demandLift (env.access.aliasPlace (path ++ [0]) p)
    demandExpr (env.withAliases aliases) (path ++ [1]) a
  | .pop p _ =>
    demandPlace env (path ++ [0]) p
    checkShrinkPoint env path (← demandLift (env.access.owner p))
  | .ifE c t f =>
    demandExpr (env.withFuture (t.variables ++ f.variables)) (path ++ [0]) c
    demandBlock env (path ++ [1]) t
    demandBlock env (path ++ [2]) f
  | .blockE b => demandBlock env (path ++ [0]) b
  | .arrLit _ es | .structLit _ es => demandExprs env path 0 es
termination_by sizeOf e

def demandExprs (env : DemandEnv) (path : List Nat) (index : Nat) (es : List Expr) : DemandCheck Unit :=
  match es with
  | [] => pure ()
  | e :: rest => do
    demandExpr (env.withFuture (rest.flatMap Expr.variables)) (path ++ [index]) e
    let aliases ← demandLift (env.access.aliasExpr (path ++ [index]) e)
    demandExprs (env.withAliases aliases) path (index + 1) rest
termination_by sizeOf es

def demandArgs (env : DemandEnv) (path : List Nat) (index : Nat) (args : List Arg) : DemandCheck (List RetainedAlias) :=
  match args with
  | [] => pure []
  | arg :: rest => do
    let current := env.withFuture (rest.flatMap Arg.variables)
    match arg with
    | .byVal e => demandExpr current (path ++ [index]) e
    | .byRef _ p => demandPlace current (path ++ [index]) p
    let aliases ← demandLift (env.access.aliasArg (path ++ [index]) arg)
    let later ← demandArgs (env.withAliases aliases) path (index + 1) rest
    pure (aliases ++ later)
termination_by sizeOf args

def demandPrintArgs (env : DemandEnv) (path : List Nat) (index : Nat) (args : List PrintArg) : DemandCheck Unit :=
  match args with
  | [] => pure ()
  | arg :: rest => do
    match arg with
    | .text _ => pure ()
    | .expr e => demandExpr (env.withFuture (rest.flatMap PrintArg.variables)) (path ++ [index]) e
    demandPrintArgs env path (index + 1) rest
termination_by sizeOf args

def demandStmt (env : DemandEnv) (path : List Nat) (stmt : Stmt) : DemandCheck DemandEnv := do
  recordDemand env path .statement
  match stmt with
  | .letS x e _ =>
    demandExpr env (path ++ [0]) e
    pure { env with active := x :: env.active }
  | .rebind _ e _ | .expr e _ | .assertS e _ | .exit e _ =>
    demandExpr env (path ++ [0]) e
    pure env
  | .assign p e _ | .assignOp _ p e _ =>
    demandPlace (env.withFuture e.variables) (path ++ [0]) p
    let aliases ← demandLift (env.access.aliasPlace (path ++ [0]) p)
    demandExpr (env.withAliases aliases) (path ++ [1]) e
    pure env
  | .append p v _ =>
    demandPlace (env.withFuture v.variables) (path ++ [0]) p
    let aliases ← demandLift (env.access.aliasPlace (path ++ [0]) p)
    demandView (env.withAliases aliases) (path ++ [1]) v
    pure env
  | .popN p count _ =>
    demandPlace (env.withFuture count.variables) (path ++ [0]) p
    let aliases ← demandLift (env.access.aliasPlace (path ++ [0]) p)
    demandExpr (env.withAliases aliases) (path ++ [1]) count
    checkShrinkPoint env path (← demandLift (env.access.owner p))
    pure env
  | .resize p size fill _ =>
    let fillVars := match fill with | none => [] | some e => e.variables
    demandPlace (env.withFuture (size.variables ++ fillVars)) (path ++ [0]) p
    let aliases ← demandLift (env.access.aliasPlace (path ++ [0]) p)
    demandExpr ((env.withAliases aliases).withFuture fillVars) (path ++ [1]) size
    match fill with
    | none => pure ()
    | some e => demandExpr (env.withAliases aliases) (path ++ [2]) e
    checkShrinkPoint env path (← demandLift (env.access.owner p))
    pure env
  | .clear p _ =>
    demandPlace env (path ++ [0]) p
    checkShrinkPoint env path (← demandLift (env.access.owner p))
    pure env
  | .assignWhole p e _ =>
    demandPlace (env.withFuture e.variables) (path ++ [0]) p
    let owner ← demandLift (env.access.owner p)
    checkShrinkPoint env path owner
    demandExpr { env with forbidden := owner :: env.forbidden } (path ++ [1]) e
    pure env
  | .ifS c t f _ =>
    let later := t.variables ++ (match f with | none => [] | some b => b.variables)
    demandExpr (env.withFuture later) (path ++ [0]) c
    demandBlock env (path ++ [1]) t
    match f with | none => pure () | some b => demandBlock env (path ++ [2]) b
    pure env
  | .while c b _ =>
    let loopEnv := env.withFuture ((c.variables ++ b.variables).filter env.active.contains)
    demandExpr loopEnv (path ++ [0]) c
    demandBlock loopEnv (path ++ [1]) b
    pure env
  | .forRange x lo hi b _ =>
    demandExpr (env.withFuture (hi.variables ++ b.variables)) (path ++ [0]) lo
    demandExpr (env.withFuture b.variables) (path ++ [1]) hi
    demandBlock { env.withFuture (b.variables.filter env.active.contains) with active := x :: env.active } (path ++ [2]) b
    pure env
  | .forEach x idx v byRef b _ =>
    demandView (env.withFuture b.variables) (path ++ [0]) v
    let sampled ← match v with
      | .of p =>
        match env.access.placeType? p with
        | some (.grow _) | some (.growshrink _) => pure []
        | _ => demandLift (env.access.aliasView (path ++ [0]) v)
      | .val _ => demandLift (env.access.aliasView (path ++ [0]) v)
    let _ := byRef
    let loopEnv := (env.withAliases sampled).withFuture (b.variables.filter env.active.contains)
    demandBlock { loopEnv with active := x :: idx.toList ++ env.active } (path ++ [1]) b
    pure env
  | .ret value _ =>
    match value with | none => pure () | some e => demandExpr env (path ++ [0]) e
    pure env
  | .brk _ | .cont _ | .abort .. => pure env
  | .print args _ =>
    demandPrintArgs env path 0 args
    pure env
termination_by sizeOf stmt

def demandStmts (env : DemandEnv) (path : List Nat) (index : Nat) (ss : List Stmt) : DemandCheck DemandEnv :=
  match ss with
  | [] => pure env
  | stmt :: rest => do
    let next ← demandStmt (env.withFuture (rest.flatMap Stmt.variables)) (path ++ [index]) stmt
    demandStmts { env with active := next.active } path (index + 1) rest
termination_by sizeOf ss

def demandBlock (env : DemandEnv) (path : List Nat) (b : Block) : DemandCheck Unit := do
  recordDemand env path .block
  match b with
  | .mk _ ss value =>
    let valueVars := match value with | none => [] | some e => e.variables
    let next ← demandStmts (env.withFuture valueVars) path 0 ss
    match value with
    | none => pure ()
    | some e => demandExpr { env with active := next.active } (path ++ [ss.length]) e
termination_by sizeOf b
end

/-- Derive checked per-point demand for each invocation context and initializer. -/
def deriveModuleDemand (m : Module) : V (Array (Array DemandPoint)) := do
  if m.profile == .pilot then return #[]
  let mut plans := #[]
  for ctx in m.contexts do
    let some impl := m.impls[ctx.impl]? | reject .call "demand context has no implementation"
    let env : DemandEnv := ⟨⟨m, impl, ctx⟩, impl.params.toList.map (·.var), [], [], []⟩
    let (_, plan) ← (demandBlock env [] impl.body).run #[]
    plans := plans.push plan
  for global in m.globals do
    let env : DemandEnv := ⟨⟨m, initImpl, initContext⟩, [], [], [], []⟩
    let (_, plan) ← (demandExpr env [] global.init).run #[]
    plans := plans.push plan
  pure plans

def checkModuleDemand (m : Module) : V Unit := do
  let _ ← deriveModuleDemand m
  pure ()

end Goose.Core
