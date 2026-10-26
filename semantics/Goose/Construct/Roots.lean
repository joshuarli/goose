import Goose.Construct.Access
import Goose.Construct.Targets



namespace Goose.Construct
open Goose.Core (V reject forAll Rule VarId GlobalId ContextId BinOp Request)


structure Eff where
  reads : List Target := []
  writes : List Target := []
  grows : List Target := []
  shrinks : List Target := []
  rebinds : List Target := []
  constructs : List Nat := []
  escapeRoots : List (Nat × List (List RootRef)) := []
  aborts : Bool := false
  outputs : Bool := false
  
  unknown : Bool := false
  storageReads : List RootRef := []
  storageWrites : List RootRef := []
  storageGrows : List RootRef := []
  storageShrinks : List RootRef := []
  namedRoots : List RootRef := []
  calls : List (ContextId × List (List RootRef)) := []

structure RState where
  
  nextVar : Nat
  eff : Eff
  valueBreakRoots : List RootRef := []

abbrev P := StateT RState V

structure PEnv where
  mod : Module
  impl : Impl
  ctx : Context
  
  scopes : List Nat
  valueBlock : Option Nat := none
  escaping : Array (List (Nat × List (List RootRef))) := #[]
  targetEscapes : Array (List Nat) := #[]
  aliases : List (RootRef × RootRef) := []
  calleeNames : Array (List RootRef) := #[]
  initializing : List VarId := []

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
  addRoots rs fun e ts => { e with reads := addTargets e.reads ts, storageReads := (e.storageReads ++ rs).eraseDups }

def addWrites (rs : List RootRef) : P Unit :=
  addRoots rs fun e ts => { e with writes := addTargets e.writes ts, storageWrites := (e.storageWrites ++ rs).eraseDups }

def addGrows (rs : List RootRef) : P Unit :=
  addRoots rs fun e ts => { e with grows := addTargets e.grows ts, storageGrows := (e.storageGrows ++ rs).eraseDups }

def addShrinks (rs : List RootRef) : P Unit :=
  addRoots rs fun e ts => { e with shrinks := addTargets e.shrinks ts, storageShrinks := (e.storageShrinks ++ rs).eraseDups }

def PEnv.access (env : PEnv) : AccessEnv := ⟨env.mod, env.impl, env.ctx⟩

def PEnv.limitedOwner (env : PEnv) (p : Place) : V Bool :=
  match env.access.placeType? p with
  | some (.limited ..) => pure true
  | some _ => pure false
  | none => reject .type "owner has no checked declaration type"

def noteAborts : P Unit := modify fun s => { s with eff := { s.eff with aborts := true } }

def noteResultConstruction (env : PEnv) : P Unit :=
  let positions := env.impl.results.toList.zipIdx.filterMap fun (result, position) =>
    if result.ty.nonfixed then some position else none
  modify fun state => { state with eff := { state.eff with
    constructs := (state.eff.constructs ++ positions).eraseDups } }

def noteOutputs : P Unit := modify fun s => { s with eff := { s.eff with outputs := true } }

def unionRoots (a b : List RootRef) : List RootRef :=
  b.foldl (fun acc r => if acc.contains r then acc else acc ++ [r]) a

def subsetRoots (a b : List RootRef) : Bool := a.all b.contains

mutual
private def expressionParameterRebindings : Expr → List (VarId × Expr)
  | .lit .. | .bool _ | .bytes .. | .resultLocal .. => []
  | .read place | .ref _ place | .copy _ place _ | .pop place _ => placeParameterRebindings place
  | .slice _ view lo hi _ => viewParameterRebindings view ++ boundParameterRebindings lo ++ boundParameterRebindings hi
  | .len view => viewParameterRebindings view
  | .un _ expression _ | .not expression | .conv _ _ expression _ | .fill _ expression _ =>
      expressionParameterRebindings expression
  | .bin _ left right _ | .cmp _ left right | .and left right | .or left right =>
      expressionParameterRebindings left ++ expressionParameterRebindings right
  | .call _ arguments _ => argumentParameterRebindings arguments
  | .push place expression _ => placeParameterRebindings place ++ expressionParameterRebindings expression
  | .ifE condition left right _ =>
      expressionParameterRebindings condition ++ blockParameterRebindings left ++ blockParameterRebindings right
  | .blockE block _ => blockParameterRebindings block
  | .arrLit _ expressions _ | .structLit _ expressions | .values expressions =>
      expressionsParameterRebindings expressions
  | .str _ arguments _ => printParameterRebindings arguments

private def placeParameterRebindings : Place → List (VarId × Expr)
  | .var _ | .global _ => []
  | .deref expression => expressionParameterRebindings expression
  | .elem view index _ => viewParameterRebindings view ++ expressionParameterRebindings index
  | .field place _ => placeParameterRebindings place

private def viewParameterRebindings : View → List (VarId × Expr)
  | .of place => placeParameterRebindings place
  | .val expression => expressionParameterRebindings expression

private def boundParameterRebindings : Bound → List (VarId × Expr)
  | .expr expression | .fromEnd expression => expressionParameterRebindings expression
  | .omitted => []

private def expressionsParameterRebindings : List Expr → List (VarId × Expr)
  | [] => []
  | expression :: rest => expressionParameterRebindings expression ++ expressionsParameterRebindings rest

private def argumentParameterRebindings : List Arg → List (VarId × Expr)
  | [] => []
  | .byVal expression :: rest | .construct expression :: rest =>
      expressionParameterRebindings expression ++ argumentParameterRebindings rest
  | .byRef _ place :: rest => placeParameterRebindings place ++ argumentParameterRebindings rest

private def blockParameterRebindings : Block → List (VarId × Expr)
  | .mk _ statements tail => statementParameterRebindings statements ++
      (match tail with | none => [] | some expression => expressionParameterRebindings expression)

private def statementParameterRebindings : List Stmt → List (VarId × Expr)
  | [] => []
  | statement :: rest =>
      (match statement with
      | .rebind variableId expression _ => (variableId, expression) :: expressionParameterRebindings expression
      | .letS _ expression _ | .expr expression _ | .assertS expression _ | .exit expression _ |
        .receive _ expression _ | .retForward expression _ | .breakValue expression _ |
        .returnFromForward _ expression _ => expressionParameterRebindings expression
      | .assign place expression _ | .assignOp _ place expression _ | .assignWhole place expression _ |
        .appendValue place expression _ | .appendConstruct place expression _ | .popN place expression _ =>
          placeParameterRebindings place ++ expressionParameterRebindings expression
      | .append place view _ => placeParameterRebindings place ++ viewParameterRebindings view
      | .clear place _ => placeParameterRebindings place
      | .resize place size fill _ => placeParameterRebindings place ++ expressionParameterRebindings size ++
          (match fill with | none => [] | some expression => expressionParameterRebindings expression)
      | .ifS condition left right _ => expressionParameterRebindings condition ++ blockParameterRebindings left ++
          (match right with | none => [] | some block => blockParameterRebindings block)
      | .while condition body _ => expressionParameterRebindings condition ++ blockParameterRebindings body
      | .forRange _ lo hi body _ =>
          expressionParameterRebindings lo ++ expressionParameterRebindings hi ++ blockParameterRebindings body
      | .forEach _ _ view _ body _ => viewParameterRebindings view ++ blockParameterRebindings body
      | .ret expression _ => match expression with | none => [] | some expression => expressionParameterRebindings expression
      | .retValues expressions _ | .returnFrom _ expressions _ => expressionsParameterRebindings expressions
      | .print arguments _ => printParameterRebindings arguments
      | .brk _ | .cont _ | .abort .. => []) ++ statementParameterRebindings rest

private def printParameterRebindings : List PrintArg → List (VarId × Expr)
  | [] => []
  | .text _ :: rest => printParameterRebindings rest
  | .expr expression :: rest => expressionParameterRebindings expression ++ printParameterRebindings rest
  | .view view :: rest => viewParameterRebindings view ++ printParameterRebindings rest
end

private def mutableValueParameter (impl : Impl) (variableId : VarId) : Bool :=
  (impl.vars[variableId]?).any (fun localVar => localVar.kind == .mutable && localVar.ty.isRefLike) &&
    impl.params.any (fun parameter => parameter.var == variableId && parameter.mode == .byValue)

def mutableParameterRebindings (impl : Impl) : List (VarId × Expr) :=
  (blockParameterRebindings impl.body).filter fun (variableId, _) => mutableValueParameter impl variableId

def parameterBodyRootContext (module : Module) (impl : Impl) (context : Context) : V Context := do
  if !(impl.params.any fun parameter => mutableValueParameter impl parameter.var) then return context
  let assignments := mutableParameterRebindings impl
  let mut current := context
  let bound := impl.params.size * (module.globals.size + impl.vars.size + impl.params.size + 1) + 1
  for _ in [0:bound] do
    let mut next := current
    for (variableId, expression) in assignments do
      let roots ← (AccessEnv.mk module impl current).exprRoots expression
      next := { next with varRoots := next.varRoots.map fun (id, previous) =>
        (id, if id == variableId then unionRoots previous roots else previous) }
    if next.varRoots == current.varRoots then return current
    current := next
  reject .root "mutable parameter root closure did not converge"

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

private def maximumElements : Ty → Option Nat
  | .arr _ count => some count
  | .limited _ capacity => some capacity
  | .varr _ => some (2 ^ 32 - 1)
  | _ => none

mutual
private def expressionMaximum (env : PEnv) : Expr → Option Nat
  | .bytes _ data _ | .arrLit _ data _ => some data.length
  | .fill ty _ _ => maximumElements ty
  | .copy _ source _ => (env.access.placeType? source).bind maximumElements
  | .ifE _ left right _ => do
      let a ← blockMaximum env left
      let b ← blockMaximum env right
      pure (max a b)
  | .blockE block _ => blockMaximum env block
  | .str _ parts _ => parts.foldlM (fun count part => match part with
      | .text text => some (count + text.toUTF8.size)
      | _ => none) 0
  | .call contextId _ _ => do
      let context ← env.mod.contexts[contextId]?
      let implementation ← env.mod.impls[context.impl]?
      match implementation.results.toList with
      | [descriptor] => match descriptor.ty, descriptor.request with
        | .varr _, .elementRun => none
        | _, _ => maximumElements descriptor.ty
      | _ => none
  | expression => (env.access.exprType? expression).bind maximumElements

private def blockMaximum (env : PEnv) : Block → Option Nat
  | .mk _ _ none => none
  | .mk _ _ (some expression) => expressionMaximum env expression
end

private def receivingCapacity : Ty → Request → Option Nat
  | .limited _ capacity, _ => some capacity
  | .varr _, .value => some (2 ^ 32 - 1)
  | _, _ => none

private def noteReceivingCapacity (env : PEnv) (ty : Ty) (request : Request) (expression : Expr) : P Unit :=
  match receivingCapacity ty request with
  | none => pure ()
  | some capacity => match expressionMaximum env expression with
    | some maximum => if maximum > capacity then noteAborts else pure ()
    | none => noteAborts

private def noteOperandCapacities (env : PEnv) (descriptors : List ResultDescriptor) (operands : List Expr) : P Unit :=
  for (descriptor, operand) in descriptors.zip operands do
    noteReceivingCapacity env descriptor.ty descriptor.request operand

private def descriptorMaximum (descriptor : ResultDescriptor) : Option Nat :=
  match descriptor.ty, descriptor.request with
  | .varr _, .elementRun => none
  | ty, _ => maximumElements ty

private def mergeProducerMaxima (left right : List (Option Nat)) : V (List (Option Nat)) := do
  if left.isEmpty then pure right
  else if right.isEmpty then pure left
  else
    if left.length != right.length then reject .result "capacity analysis branch result count mismatch"
    pure ((left.zip right).map fun (a,b) => do pure (max (← a) (← b)))

mutual
private def producerMaximum (env : PEnv) : Expr → V (List (Option Nat))
  | .values operands => pure (operands.map (expressionMaximum env))
  | .call contextId _ _ => do
      let some context := env.mod.contexts[contextId]? | reject .call "capacity analysis call context outside table"
      let some implementation := env.mod.impls[context.impl]? | reject .call "capacity analysis callee outside table"
      pure (implementation.results.toList.map descriptorMaximum)
  | .ifE _ left right _ => do
      let a ← blockProducerMaximum env left
      let b ← blockProducerMaximum env right
      mergeProducerMaxima a b
  | .blockE block _ => do
      let maxima ← blockProducerMaximum env block
      if maxima.isEmpty then
        let some types := blockResultTypes? 10000 env.access.declarations block |
          reject .type "cannot determine block capacity channels"
        pure (types.map maximumElements)
      else pure maxima
  | expression => pure [expressionMaximum env expression]

private def blockProducerMaximum (env : PEnv) : Block → V (List (Option Nat))
  | .mk _ statements tail => do
      let breaks ← statementBreakMaximum env statements
      let normal ← match tail with | none => pure [] | some expression => producerMaximum env expression
      mergeProducerMaxima breaks normal

private def statementBreakMaximum (env : PEnv) : List Stmt → V (List (Option Nat))
  | [] => pure []
  | statement :: rest => do
      let current ← match statement with
        | .breakValue expression _ => producerMaximum env expression
        | .ifS _ (.mk _ left _) right _ => do
            let left ← statementBreakMaximum env left
            let right ← match right with
              | none => pure []
              | some (.mk _ statements _) => statementBreakMaximum env statements
            mergeProducerMaxima left right
        | .while _ (.mk _ statements _) _ |
          .forRange _ _ _ (.mk _ statements _) _ |
          .forEach _ _ _ _ (.mk _ statements _) _ => statementBreakMaximum env statements
        | _ => pure []
      mergeProducerMaxima current (← statementBreakMaximum env rest)
end

private def noteProducerCapacities (env : PEnv) (descriptors : List ResultDescriptor) (producer : Expr) : P Unit := do
  let maxima ← liftV (producerMaximum env producer)
  if maxima.length != descriptors.length then rejP .result "capacity analysis result channel count mismatch"
  for (descriptor, maximum) in descriptors.zip maxima do
    match receivingCapacity descriptor.ty descriptor.request, maximum with
    | none, _ => pure ()
    | some capacity, some maximum => if maximum > capacity then noteAborts
    | some _, none => noteAborts

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


private def joinEscapeRoots (old incoming : List (Nat × List (List RootRef))) :
    List (Nat × List (List RootRef)) :=
  incoming.foldl (fun accumulated (target, channels) =>
    match accumulated.find? (fun fact => fact.1 == target) with
    | none => accumulated ++ [(target, channels)]
    | some (_, previous) => accumulated.map fun fact =>
        if fact.1 == target then (target, (previous.zip channels).map fun (a,b) => unionRoots a b)
        else fact) old

private def receiveEscapeRoots (env : PEnv) (targetId : Nat) (channels : List (List RootRef)) : P Unit := do
  let some target := env.mod.targets[targetId]? | rejP .call "escape root target outside table"
  for roots in channels do liftV (checkNoLocal roots)
  if target.contains env.ctx.impl then
    liftV (checkResultChannels env channels)
  else
    modify fun state => { state with eff := { state.eff with
      escapeRoots := joinEscapeRoots state.eff.escapeRoots [(targetId,channels)] } }

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


private def mappedStorage (callee : Impl) (context : Context) (arguments : List (List RootRef))
    (targets : List Target) : List RootRef :=
  targets.flatMap fun target => match target with
    | .global id => [.global id]
    | .param position =>
        match arguments[position]? with
        | none => []
        | some roots => roots ++ (paramGlobals callee context position).filterMap fun target =>
            match target with | .global id => some (.global id) | .param _ => none

private def mergeEffects (a b : Eff) : Eff := {
  reads := addTargets a.reads b.reads
  writes := addTargets a.writes b.writes
  grows := addTargets a.grows b.grows
  shrinks := addTargets a.shrinks b.shrinks
  rebinds := addTargets a.rebinds b.rebinds
  constructs := (a.constructs ++ b.constructs).eraseDups
  escapeRoots := joinEscapeRoots a.escapeRoots b.escapeRoots
  aborts := a.aborts || b.aborts
  outputs := a.outputs || b.outputs
  unknown := a.unknown || b.unknown
  storageReads := (a.storageReads ++ b.storageReads).eraseDups
  storageWrites := (a.storageWrites ++ b.storageWrites).eraseDups
  storageGrows := (a.storageGrows ++ b.storageGrows).eraseDups
  storageShrinks := (a.storageShrinks ++ b.storageShrinks).eraseDups
  namedRoots := (a.namedRoots ++ b.namedRoots).eraseDups
  calls := (a.calls ++ b.calls).eraseDups }

private def captureEffects (action : P α) : P (α × Eff) := fun state => do
  let (value, result) ← action { state with eff := {} }
  pure ((value, result.eff), { result with eff := mergeEffects state.eff result.eff })

private def noteNamed (roots : List RootRef) : P Unit :=
  modify fun state => { state with eff := { state.eff with
    namedRoots := (state.eff.namedRoots ++ roots).eraseDups } }

private def rootsMayAlias (aliases : List (RootRef × RootRef)) (left right : RootRef) : Bool :=
  left == right || aliases.contains (left, right) || aliases.contains (right, left)

private def overlaps (aliases : List (RootRef × RootRef)) (receiver accessed : List RootRef) : Bool :=
  receiver.any fun root => accessed.any (rootsMayAlias aliases root)

private def unknownGlobalAccess (env : PEnv) (receiver : List RootRef) (effects : Eff) : Bool :=
  effects.unknown && receiver.any fun root =>
    (List.range env.mod.globals.size).any fun global => rootsMayAlias env.aliases root (.global global)

private def checkNoGrowth (env : PEnv) (receiver : List RootRef) (effects : Eff) : P Unit :=
  if overlaps env.aliases receiver (effects.storageGrows ++ effects.storageShrinks) || unknownGlobalAccess env receiver effects then
    rejP .call "C-NOGROW: constructor resizes its open receiving owner"
  else pure ()

private def checkWholeAccess (env : PEnv) (receiver : List RootRef) (effects : Eff) : P Unit :=
  if overlaps env.aliases receiver (effects.namedRoots ++ effects.storageReads ++ effects.storageWrites ++
      effects.storageGrows ++ effects.storageShrinks) || unknownGlobalAccess env receiver effects then
    rejP .whole "whole assignment replacement reaches its receiver"
  else pure ()

private def mapNamedRoots (callee : Impl) (context : Context) (arguments : List (List RootRef))
    (roots : List RootRef) : List RootRef :=
  roots.flatMap fun root => match root with
    | .local _ => []
    | .static => [.static]
    | .global global => [.global global]
    | .param position => mappedStorage callee context arguments [.param position]

def callEffects (callee : Impl) (cctx : Context) (argRoots : List (List RootRef)) (e : Eff) : Eff :=
  match callee.summary with
  | .unknown =>
    { e with
      writes := addTargets e.writes (rootsTargets argRoots.flatten)
      unknown := true
      storageReads := (e.storageReads ++ argRoots.flatten).eraseDups
      storageWrites := (e.storageWrites ++ argRoots.flatten).eraseDups
      storageGrows := (e.storageGrows ++ argRoots.flatten).eraseDups
      storageShrinks := (e.storageShrinks ++ argRoots.flatten).eraseDups }
  | .known sm =>
    { e with
      reads := addTargets e.reads (mapCallTargets callee cctx argRoots sm.reads)
      writes := addTargets e.writes (mapCallTargets callee cctx argRoots sm.writes)
      grows := addTargets e.grows (mapCallTargets callee cctx argRoots sm.grows)
      shrinks := addTargets e.shrinks (mapCallTargets callee cctx argRoots sm.shrinks)
      rebinds := addTargets e.rebinds (mapCallTargets callee cctx argRoots sm.rebinds)
      aborts := e.aborts || sm.aborts
      outputs := e.outputs || sm.outputs
      storageReads := (e.storageReads ++ mappedStorage callee cctx argRoots sm.reads).eraseDups
      storageWrites := (e.storageWrites ++ mappedStorage callee cctx argRoots sm.writes).eraseDups
      storageGrows := (e.storageGrows ++ mappedStorage callee cctx argRoots sm.grows).eraseDups
      storageShrinks := (e.storageShrinks ++ mappedStorage callee cctx argRoots sm.shrinks).eraseDups }


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

private def interiorAliasType : Ty → Bool
  | .ref _ (.grow _) | .ref _ (.growshrink _) | .ref _ (.limited _ _) => false
  | .ref .. | .slice .. => true
  | _ => false

private def checkRetainedShrinks (env : PEnv) (retained : List RootRef) (effects : Eff) : P Unit :=
  if overlaps env.aliases retained effects.storageShrinks || unknownGlobalAccess env retained effects then
    rejP .shrink "shrink may invalidate a retained reference or slice"
  else pure ()

private def checkScopedShrinkAliases (env : PEnv) (effects : Eff) : P Unit := do
  let declared := (← get).nextVar
  for h : id in [0:env.impl.vars.size] do
    let localVar := env.impl.vars[id]
    if id < declared && !env.initializing.contains id && env.scopes.contains localVar.scope && interiorAliasType localVar.ty then
      let roots ← liftV (env.access.variableRoots id)
      let roots := roots ++ (env.cont id).getD []
      checkRetainedShrinks env roots effects

private def checkDirectShrinkAliases (env : PEnv) (roots : List RootRef) : P Unit :=
  checkScopedShrinkAliases env { storageShrinks := roots }

private def argumentInteriorRoots (env : PEnv) (argument : Arg) (roots : List RootRef) : V (List RootRef) := do
  match argument with
  | .byVal expression =>
      pure (if (env.access.exprType? expression).any interiorAliasType then roots else [])
  | .construct _ => pure []
  | .byRef mutability place =>
      let some ty := env.access.placeType? place | reject .type "argument place type missing"
      if interiorAliasType (.ref mutability ty) then
        pure (roots ++ (← env.access.exprRoots (.read place)))
      else pure []

mutual

def rpPlace (env : PEnv) : Place → P (List RootRef)
  | .var x => do noteNamed [.local x]; pure [.local x]
  | .global g => do noteNamed [.global g]; pure [.global g]
  | .deref e => do
    let roots ← rpExpr env e
    noteNamed roots
    pure roots
  | .field owner _ => rpPlace env owner
  | .elem v i _ => do
    let rho ← rpView env v
    let (_, effects) ← captureEffects (rpExpr env i)
    checkRetainedShrinks env rho effects
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
    let roots ← readRoots env p
    noteNamed roots
    pure roots
  | .ref _ p => rpPlace env p
  | .slice _ v lo hi _ => do
    let rho ← rpView env v
    let (_, effects) ← captureEffects (do rpBound env lo; rpBound env hi)
    checkRetainedShrinks env rho effects
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
    let some context := env.mod.contexts[c]? | rejP .call "call context outside table"
    let some callee := env.mod.impls[context.impl]? | rejP .call "callee outside table"
    for (parameter, argument) in callee.params.toList.zip args do
      match argument with
      | .construct expression =>
          let some localVar := callee.vars[parameter.var]? | rejP .call "parameter outside variable table"
          noteReceivingCapacity env localVar.ty .value expression
      | _ => pure ()
    liftV (checkContents env c args argRoots)
    let escapes := env.targetEscapes[context.impl]?.getD []
    if escapes.any (fun target => (env.mod.targets[target]?).any (·.contains env.ctx.impl)) then
      noteResultConstruction env
    rpCall env c argRoots
  | .push owner a _ => do
    let rho ← rpPlace env owner
    let (_, effects) ← captureEffects (rpExpr env a)
    if ((env.access.placeType? owner).bind Ty.ownerElem?).any (·.nonfixed) then
      checkNoGrowth env rho effects
    addGrows rho
    addWrites rho
    if (← liftV (env.limitedOwner owner)) then noteAborts
    pure rho
  | .pop owner _ => do
    let rho ← rpPlace env owner
    addReads rho
    checkDirectShrinkAliases env rho
    addShrinks rho
    noteAborts
    pure []
  | .ifE c t f _ => do
    let _ ← rpExpr env c
    let (rt, lt) ← rpBlockValue env [] t
    let (rf, lf) ← rpBlockValue env [] f
    let _ := (lt, lf)
    pure (unionRoots rt rf)
  | .blockE b _ => do
    let previous := (← get).valueBreakRoots
    modify fun state => { state with valueBreakRoots := [] }
    let .mk scope _ _ := b
    let (rho, _) ← rpBlockValue { env with valueBlock := some scope } [] b
    modify fun state => { state with valueBreakRoots := previous }
    pure rho
  | .arrLit ty es _ => do
    rpExprs env es
    match ty with
    | .limited _ capacity => if es.length > capacity then noteAborts
    | _ => pure ()
    pure []
  | .structLit _ es => do
    rpExprs env es
    pure []
  | .fill _ a _ => do
    let _ ← rpExpr env a
    pure []
  | .bytes ty data _ => match ty with
    | .slice .. => pure [.static]
    | .limited _ capacity => do
        if data.length > capacity then noteAborts
        pure []
    | _ => pure []
  | .str ty args _ => do
    rpPrintArgs env args
    if (match ty with | .limited .. => true | _ => false) then noteAborts
    pure []
  | .copy ty source _ => do
    if (match ty with | .limited .. => true | _ => false) then noteAborts
    let roots ← rpPlace env source
    addReads roots
    addReads (← readRoots env source)
    pure []
  | .resultLocal _ _ => pure []
  | .values operands => do
    rpExprs env operands
    let roots ← liftV (env.access.resultRoots (.values operands))
    pure roots.flatten.eraseDups

def rpExprs (env : PEnv) : List Expr → P Unit
  | [] => pure ()
  | e :: rest => do
    let roots ← rpExpr env e
    let (_, effects) ← captureEffects (rpExprs env rest)
    if (env.access.exprType? e).any interiorAliasType then checkRetainedShrinks env roots effects


def rpArgs (env : PEnv) : List Arg → P (List (List RootRef))
  | [] => pure []
  | .byVal e :: rest | .construct e :: rest => do
    let rho ← rpExpr env e
    let (remaining, effects) ← captureEffects (rpArgs env rest)
    let retained ← liftV (argumentInteriorRoots env (.byVal e) rho)
    checkRetainedShrinks env retained effects
    pure (rho :: remaining)
  | .byRef mutability p :: rest => do
    let rho ← rpPlace env p
    let (remaining, effects) ← captureEffects (rpArgs env rest)
    let retained ← liftV (argumentInteriorRoots env (.byRef mutability p) rho)
    checkRetainedShrinks env retained effects
    pure (rho :: remaining)


def rpCall (env : PEnv) (c : ContextId) (argRoots : List (List RootRef)) : P (List RootRef) := do
  let some cctx := env.mod.contexts[c]? | rejP .call s!"call of context {c}, outside the context table"
  let some callee := env.mod.impls[cctx.impl]? | rejP .call s!"context {c} names a missing implementation"
  liftV (forAll (List.range callee.params.size) (checkArgRoots callee cctx argRoots))
  let rawEffects := callEffects callee cctx argRoots {}
  let effects ← match callee.summary with
    | .known _ => pure rawEffects
    | .unknown => do
      let mut invalidating := []
      for (parameter, roots) in callee.params.toList.zip argRoots do
        let some localVar := callee.vars[parameter.var]? | rejP .call "parameter outside variable table"
        let mayShrink := match localVar.ty with
          | .ref _ (.slice .mutable element) => element.nonfixed
          | .ref _ ty => ty.nonfixed || (ty matches .limited ..)
          | .slice .mutable element => element.nonfixed
          | _ => false
        if mayShrink then invalidating := invalidating ++ roots
      pure { rawEffects with storageShrinks := invalidating }
  checkScopedShrinkAliases env effects
  for (parameter, roots) in callee.params.toList.zip argRoots do
    let some localVar := callee.vars[parameter.var]? | rejP .call "parameter outside variable table"
    if interiorAliasType localVar.ty then checkRetainedShrinks env roots effects
  modify fun state =>
    let effects := callEffects callee cctx argRoots state.eff
    { state with eff := { effects with
      calls := (effects.calls ++ [(c, argRoots)]).eraseDups
      namedRoots := (effects.namedRoots ++
        mapNamedRoots callee cctx argRoots (env.calleeNames[c]?.getD [])).eraseDups } }
  for (targetId, channels) in env.escaping[c]?.getD [] do
    let mapped ← liftV (channels.mapM (mapResultRoots argRoots []))
    receiveEscapeRoots env targetId mapped
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
    let rho := if env.valueBlock == some sc then unionRoots rho st1.valueBreakRoots else rho
    liftV (checkBlockValue st0.nextVar st1.nextVar rho)
    pure (rho, (st0.nextVar, st1.nextVar))

def rpReturnOperands (env : PEnv) : List (List RootRef) → List Expr → P Unit
  | [], [] => pure ()
  | roots :: channels, operand :: operands => do
      let actual ← rpExpr env operand
      liftV (checkNoLocal actual)
      if !subsetRoots actual roots then rejP .result "returned roots exceed declared channel roots"
      let (_, effects) ← captureEffects (rpReturnOperands env channels operands)
      if (env.access.exprType? operand).any interiorAliasType then checkRetainedShrinks env actual effects
  | _, _ => rejP .result "returned roots channel count mismatch"

def rpNoLocalOperands (env : PEnv) : List Expr → P Unit
  | [] => pure ()
  | operand :: operands => do
      let roots ← rpExpr env operand
      liftV (checkNoLocal roots)
      let (_, effects) ← captureEffects (rpNoLocalOperands env operands)
      if (env.access.exprType? operand).any interiorAliasType then checkRetainedShrinks env roots effects

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
    let rho ← rpExpr { env with initializing := x :: env.initializing } e
    match env.impl.vars[x]? with
    | some lv =>
      noteReceivingCapacity env lv.ty .value e
      if lv.ty.isRefLike then bindRoots env env.scopes x rho
    | none => rejP .root s!"variable {x} outside the variable table"
  | .assign p e _ => do
    let rho ← rpPlace env p
    let (stored, effects) ← captureEffects (rpExpr env e)
    checkRetainedShrinks env rho effects
    liftV (checkStore env p stored)
    addWrites rho

    modify fun s => { s with eff := { s.eff with rebinds := addTargets s.eff.rebinds (storeRebinds env p) } }
  | .assignOp op p e _ => do
    let rho ← rpPlace env p
    let (_, effects) ← captureEffects (rpExpr env e)
    checkRetainedShrinks env rho effects
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
    checkDirectShrinkAliases env rho
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
    checkDirectShrinkAliases env rho
    addShrinks rho
    noteAborts
  | .clear owner _ => do
    let rho ← rpPlace env owner
    addReads rho
    checkDirectShrinkAliases env rho
    addShrinks rho
  | .assignWhole owner replacement _ => do
    let rho ← rpPlace env owner
    addReads rho
    checkDirectShrinkAliases env rho
    addShrinks rho
    let (_, effects) ← captureEffects (rpExpr env replacement)
    checkWholeAccess env rho effects
    let some ty := env.access.placeType? owner | rejP .type "whole receiver type missing"
    noteReceivingCapacity env ty .value replacement
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
    let (body, effects) ← captureEffects (rpBlockValue env [] b)
    checkRetainedShrinks env rho effects
    liftV (checkBlockValue st0.nextVar body.2.1 body.1)
  | .receive ids producer _ => do
    let _ ← rpExpr env producer
    let descriptors ← liftV (ids.mapM fun id => do
      let some localVar := env.impl.vars[id]? | reject .type "receive variable outside table"
      pure ({ ty := localVar.ty, request := if localVar.ty.nonfixed then .value else .register, namedLocal := none } : ResultDescriptor))
    noteProducerCapacities env descriptors producer
    for id in ids do
      modify fun state => { state with nextVar := state.nextVar + 1 }
      let some localVar := env.impl.vars[id]? | rejP .type "receive variable outside table"
      if localVar.ty.isRefLike then
        let roots ← liftV (env.access.resultRoots producer)
        let position := ids.idxOf id
        let some actual := roots[position]? | rejP .result "receive result channel missing"
        bindRoots env env.scopes id actual
  | .appendValue owner producer _ => do
    let roots ← rpPlace env owner
    let _ ← rpExpr env producer
    addGrows roots
    addWrites roots
    if (← liftV (env.limitedOwner owner)) then noteAborts
  | .appendConstruct owner producer _ => do
    let roots ← rpPlace env owner
    let (_, effects) ← captureEffects (rpExpr env producer)
    checkNoGrowth env roots effects
    addGrows roots
    addWrites roots
    if (← liftV (env.limitedOwner owner)) then noteAborts
  | .retValues operands _ => do
    noteResultConstruction env
    if operands.length != env.impl.results.size then rejP .result "result count mismatch"
    noteOperandCapacities env env.impl.results.toList operands
    rpReturnOperands env env.ctx.resultRoots operands
  | .retForward producer _ => do
    noteResultConstruction env
    let _ ← rpExpr env producer
    noteProducerCapacities env env.impl.results.toList producer
    let actual ← liftV (env.access.resultRoots producer)
    liftV (checkResultChannels env actual)
  | .returnFrom targetId operands _ => do
    let some target := env.mod.targets[targetId]? | rejP .call "target outside table"
    let some implementation := env.mod.impls[target.first]? | rejP .call "target member outside table"
    if target.contains env.ctx.impl then noteResultConstruction env
    if operands.length != implementation.results.size then rejP .result "target result count mismatch"
    noteOperandCapacities env implementation.results.toList operands
    rpNoLocalOperands env operands
    receiveEscapeRoots env targetId (← liftV (env.access.resultRoots (.values operands)))
  | .returnFromForward targetId producer _ => do
    let roots ← rpExpr env producer
    let some target := env.mod.targets[targetId]? | rejP .call "target outside table"
    let some implementation := env.mod.impls[target.first]? | rejP .call "target implementation outside table"
    if target.contains env.ctx.impl then noteResultConstruction env
    noteProducerCapacities env implementation.results.toList producer
    liftV (checkNoLocal roots)
    receiveEscapeRoots env targetId (← liftV (env.access.resultRoots producer))
  | .breakValue expression _ => do
    let roots ← rpExpr env expression
    modify fun state => { state with valueBreakRoots := unionRoots state.valueBreakRoots roots }
  | .ret e _ => do
    noteResultConstruction env
    match e with
    | none => pure ()
    | some e => do
      let rho ← rpExpr env e
      noteOperandCapacities env env.impl.results.toList [e]
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
    forAll s.constructs fun position =>
      unless (impl.results[position]?).any (·.ty.nonfixed) do
        reject .summary s!"{impl.name}: construction summary names a fixed or missing result"
    forAll eff.constructs fun position =>
      unless s.constructs.contains position do
        reject .summary s!"{impl.name}: construction summary omits result {position}"
    if eff.unknown then
      reject .summary s!"{impl.name} calls an implementation whose summary is unknown, so its own summary cannot be known"
    effWithin impl.name "reads" eff.reads (expandTargets impl ctx s.reads)
    effWithin impl.name "writes" eff.writes (expandTargets impl ctx s.writes)
    effWithin impl.name "grows" eff.grows (expandTargets impl ctx s.grows)
    effWithin impl.name "shrinks" eff.shrinks (expandTargets impl ctx s.shrinks)
    effWithin impl.name "rebinds" eff.rebinds s.rebinds
    if eff.aborts && !s.aborts then reject .summary s!"{impl.name} may abort, which its summary omits"
    if eff.outputs && !s.outputs then reject .summary s!"{impl.name} prints, which its summary omits"


private def checkContextFacts (m : Module) (ctx : Context)
    (escaping : Array (List (Nat × List (List RootRef))))
    (aliases : List (RootRef × RootRef)) (names : Array (List RootRef)) : V Eff := do
  let some impl := m.impls[ctx.impl]? | reject .root s!"context {ctx.decl}: no such implementation"
  checkAnnotationShape m impl ctx
  checkResultShape m impl ctx
  checkContentShape m impl ctx
  let actualEscapes ← match bodyTargets m with
    | .ok escapes => pure escapes
    | .error message => reject .call message
  let bodyContext ← parameterBodyRootContext m impl ctx
  let env : PEnv := ⟨m, impl, bodyContext, [], none, escaping, actualEscapes, aliases, names, []⟩
  let ((), st) ← (do
      let (_, _) ← rpBlockValue env [] impl.body
      if let some expression := impl.body.value then
        noteResultConstruction env
        noteProducerCapacities env impl.results.toList expression
        let actual ← liftV (env.access.blockResultRoots impl.body)
        liftV (checkResultChannels env actual) : P Unit).run ⟨impl.params.size, {}, []⟩
  checkSummary m impl ctx st.eff
  pure st.eff

def checkContextEscapes (m : Module) (ctx : Context)
    (escaping : Array (List (Nat × List (List RootRef)))) : V (List (Nat × List (List RootRef))) := do
  pure (← checkContextFacts m ctx escaping [] #[]).escapeRoots

def checkContext (m : Module) (ctx : Context) : V Unit := do
  let _ ← checkContextEscapes m ctx #[]

def initImpl : Impl := ⟨"", #[], #[], #[], .mk 0 [] none, .unknown⟩

def initContext : Context := ⟨0, "", [], [], []⟩


private def checkInitFacts (m : Module) (g : GlobalId) (names : Array (List RootRef)) : V Eff :=
  match m.globals[g]? with
  | none => pure {}
  | some gl => do
    let env : PEnv := ⟨m, initImpl, initContext, [], none, #[], #[], [], names, []⟩
    let (_, st) ← (do
      let roots ← rpExpr env gl.init
      noteReceivingCapacity env gl.ty .value gl.init
      pure roots : P (List RootRef)).run ⟨0, {}, []⟩
    if st.eff.unknown then
      reject .call s!"initializer of global {gl.name} calls an implementation whose effects are unknown"
    forAll (st.eff.reads ++ st.eff.writes ++ st.eff.grows ++ st.eff.shrinks) fun t =>
      match t with
      | .global h =>
        unless h < g do
          reject .call s!"initializer of global {gl.name} reaches global {h}, which is not initialized before it"
      | .param _ => pure ()

    pure st.eff

def checkInitRoots (m : Module) (g : GlobalId) : V Unit := do
  let _ ← checkInitFacts m g #[]

private def addArgumentAliases (module : Module) (caller : List (RootRef × RootRef))
    (arguments : List (List RootRef)) (argument : List RootRef × Nat)
    (initial : List (RootRef × RootRef)) : List (RootRef × RootRef) := Id.run do
  let (roots, position) := argument
  let mut pairs := initial
  for (earlier, previous) in (arguments.take position).zipIdx do
    if overlaps caller roots earlier then
      pairs := (pairs ++ [(RootRef.param position, RootRef.param previous)]).eraseDups
  for global in List.range module.globals.size do
    if overlaps caller roots [.global global] then
      pairs := (pairs ++ [(RootRef.param position, RootRef.global global)]).eraseDups
  if overlaps caller roots [.static] then
    pairs := (pairs ++ [(RootRef.param position, RootRef.static)]).eraseDups
  return pairs

private def addCallAliases (module : Module) (caller : List (RootRef × RootRef))
    (called : ContextId × List (List RootRef)) (aliases : Array (List (RootRef × RootRef))) :
    Array (List (RootRef × RootRef)) := Id.run do
  let (context, arguments) := called
  let mut pairs := aliases[context]?.getD []
  for argument in arguments.zipIdx do
    pairs := addArgumentAliases module caller arguments argument pairs
  return aliases.set! context pairs

private def addCallsAliases (module : Module) (caller : List (RootRef × RootRef))
    (calls : List (ContextId × List (List RootRef))) (aliases : Array (List (RootRef × RootRef))) :
    Array (List (RootRef × RootRef)) :=
  calls.foldl (fun accumulated called => addCallAliases module caller called accumulated) aliases

private structure ModuleRootPassState where
  escaping : Array (List (Nat × List (List RootRef)))
  aliases : Array (List (RootRef × RootRef))
  names : Array (List RootRef)

private def checkContextRootPass (module : Module) (escaping : Array (List (Nat × List (List RootRef))))
    (aliases : Array (List (RootRef × RootRef))) (names : Array (List RootRef))
    (row : Context × Nat) (current : ModuleRootPassState) : V (ForInStep ModuleRootPassState) := do
  let facts ← checkContextFacts module row.1 escaping aliases[row.2]! names
  pure (.yield ⟨current.escaping.push (joinEscapeRoots escaping[row.2]! facts.escapeRoots),
    addCallsAliases module aliases[row.2]! facts.calls current.aliases,
    current.names.set! row.2 (names[row.2]! ++ facts.namedRoots).eraseDups⟩)

private def checkInitRootPass (module : Module) (names : Array (List RootRef))
    (global : GlobalId) (current : ModuleRootPassState) : V (ForInStep ModuleRootPassState) := do
  let facts ← checkInitFacts module global names
  pure (.yield { current with aliases := addCallsAliases module [] facts.calls current.aliases })

private def checkModuleRootPass (module : Module) (escaping : Array (List (Nat × List (List RootRef))))
    (aliases : Array (List (RootRef × RootRef))) (names : Array (List RootRef)) : V ModuleRootPassState := do
  let next ← forIn module.contexts.toList.zipIdx (ModuleRootPassState.mk #[] aliases names)
    (checkContextRootPass module escaping aliases names)
  forIn (List.range module.globals.size) next (checkInitRootPass module names)

def checkModuleExitRoots (module : Module) : V Unit := do
  let largestResults := module.impls.foldl (fun largest impl => max largest impl.results.size) 0
  let largestParams := module.impls.foldl (fun largest impl => max largest impl.params.size) 0
  let largestVars := module.impls.foldl (fun largest impl => max largest impl.vars.size) 0
  let externalRoots := module.globals.size + largestParams + 1
  let escapeFacts := module.contexts.size * (module.targets.size + 1) * (largestResults + 1) *
    (externalRoots + 1)
  let aliasFacts := module.contexts.size * externalRoots * externalRoots
  let nameFacts := module.contexts.size * (externalRoots + largestVars + 1)
  let bound := escapeFacts + aliasFacts + nameFacts + 1
  let mut escaping := Array.replicate module.contexts.size []
  let mut aliases := Array.replicate module.contexts.size []
  let mut names := Array.replicate module.contexts.size []
  for _ in [0:bound] do
    let next ← checkModuleRootPass module escaping aliases names
    if next.escaping == escaping && next.aliases == aliases && next.names == names then return ()
    escaping := next.escaping
    aliases := next.aliases
    names := next.names
  reject .root "construction root and escape closure did not converge"

def RootAlias (aliases : List (RootRef × RootRef)) (left right : RootRef) : Prop :=
  left = right ∨ (left, right) ∈ aliases ∨ (right, left) ∈ aliases

def RootSetsOverlap (aliases : List (RootRef × RootRef)) (left right : List RootRef) : Prop :=
  ∃ a ∈ left, ∃ b ∈ right, RootAlias aliases a b

structure AliasClosure (caller callee : List (RootRef × RootRef))
    (arguments : List (List RootRef)) (globalCount : Nat) : Prop where
  parameters : ∀ left right a b, arguments[left]? = some a → arguments[right]? = some b →
    RootSetsOverlap caller a b → RootAlias callee (.param left) (.param right)
  globals : ∀ index roots global, arguments[index]? = some roots → global < globalCount →
    RootSetsOverlap caller roots [.global global] → RootAlias callee (.param index) (.global global)
  static : ∀ index roots, arguments[index]? = some roots →
    RootSetsOverlap caller roots [.static] → RootAlias callee (.param index) .static

private theorem rootSetsOverlap_checked (aliases : List (RootRef × RootRef)) (left right : List RootRef) :
    RootSetsOverlap aliases left right ↔ overlaps aliases left right = true := by
  constructor
  · rintro ⟨a, aMember, b, bMember, alias⟩
    apply List.any_eq_true.mpr
    refine ⟨a, aMember, List.any_eq_true.mpr ⟨b, bMember, ?_⟩⟩
    simpa [rootsMayAlias, RootAlias, or_assoc] using alias
  · intro checked
    obtain ⟨a, aMember, checked⟩ := List.any_eq_true.mp checked
    obtain ⟨b, bMember, alias⟩ := List.any_eq_true.mp checked
    exact ⟨a, aMember, b, bMember, by simpa [rootsMayAlias, RootAlias, or_assoc] using alias⟩

private theorem idForIn_preserves {α β : Type} (rows : List α) (initial : β) (update : α → β → β)
    (invariant : β → Prop) (valid : invariant initial)
    (preserved : ∀ row before, invariant before → invariant (update row before)) :
    invariant (forIn (m := Id) rows initial (fun row before => pure (.yield (update row before)))) := by
  induction rows generalizing initial with
  | nil => exact valid
  | cons row rows ih =>
    simp only [List.forIn_cons, bind, pure]
    exact ih _ (preserved row initial valid)

private theorem idForIn_member {α β : Type} (rows : List α) (initial : β) (update : α → β → β)
    (invariant : β → Prop)
    (preserved : ∀ row before, invariant before → invariant (update row before))
    (selected : α) (member : selected ∈ rows) (established : ∀ before, invariant (update selected before)) :
    invariant (forIn (m := Id) rows initial (fun row before => pure (.yield (update row before)))) := by
  induction rows generalizing initial with
  | nil => cases member
  | cons row rows ih =>
    simp only [List.forIn_cons, bind, pure]
    rcases List.mem_cons.mp member with equal | member
    · subst row
      exact idForIn_preserves rows _ update invariant (established initial) preserved
    · exact ih _ member

private theorem addArgumentAliases_extends (module : Module) (caller : List (RootRef × RootRef))
    (arguments : List (List RootRef)) (argument : List RootRef × Nat)
    (initial : List (RootRef × RootRef)) : initial ⊆ addArgumentAliases module caller arguments argument initial := by
  intro pair member
  unfold addArgumentAliases
  simp only [Id.run, bind, pure]
  have earlier := idForIn_preserves (arguments.take argument.2).zipIdx initial
    (fun previous pairs => if overlaps caller argument.1 previous.1 then
      (pairs ++ [(RootRef.param argument.2, RootRef.param previous.2)]).eraseDups else pairs)
    (fun pairs => pair ∈ pairs) member (by intro previous pairs retained; split <;> simp_all)
  simp only [apply_ite, pure] at earlier
  have globals := idForIn_preserves (List.range module.globals.size) _
    (fun global pairs => if overlaps caller argument.1 [.global global] then
      (pairs ++ [(.param argument.2, .global global)]).eraseDups else pairs)
    (fun pairs => pair ∈ pairs) earlier (by intro global pairs retained; split <;> simp_all)
  simp only [apply_ite, pure] at globals
  split <;> simp_all

private theorem addArgumentAliases_parameter (module : Module) (caller : List (RootRef × RootRef))
    (arguments : List (List RootRef)) (roots earlier : List RootRef) (position previous : Nat)
    (initial : List (RootRef × RootRef))
    (member : (earlier, previous) ∈ (arguments.take position).zipIdx)
    (overlap : overlaps caller roots earlier = true) :
    (RootRef.param position, RootRef.param previous) ∈
      addArgumentAliases module caller arguments (roots, position) initial := by
  unfold addArgumentAliases
  simp only [Id.run, bind, pure]
  let pair := (RootRef.param position, RootRef.param previous)
  have earlierAliases := idForIn_member (arguments.take position).zipIdx initial
    (fun earlier pairs => if overlaps caller roots earlier.1 then
      (pairs ++ [(RootRef.param position, RootRef.param earlier.2)]).eraseDups else pairs)
    (fun pairs => pair ∈ pairs) (by intro row pairs retained; split <;> simp_all)
    (earlier, previous) member (by intro pairs; simp [pair, overlap])
  simp only [apply_ite, pure] at earlierAliases
  have globals := idForIn_preserves (List.range module.globals.size) _
    (fun global pairs => if overlaps caller roots [.global global] then
      (pairs ++ [(RootRef.param position, RootRef.global global)]).eraseDups else pairs)
    (fun pairs => pair ∈ pairs) earlierAliases (by intro row pairs retained; split <;> simp_all)
  simp only [apply_ite, pure] at globals
  split <;> simp_all [pair]

private theorem addArgumentAliases_global (module : Module) (caller : List (RootRef × RootRef))
    (arguments : List (List RootRef)) (roots : List RootRef) (position global : Nat)
    (initial : List (RootRef × RootRef)) (bound : global < module.globals.size)
    (overlap : overlaps caller roots [.global global] = true) :
    (RootRef.param position, RootRef.global global) ∈
      addArgumentAliases module caller arguments (roots, position) initial := by
  unfold addArgumentAliases
  simp only [Id.run, bind, pure]
  let pair := (RootRef.param position, RootRef.global global)
  let earlierAliases : List (RootRef × RootRef) := Id.run do
    forIn (m := Id) (arguments.take position).zipIdx initial fun earlier pairs =>
      pure (.yield (if overlaps caller roots earlier.1 then
        (pairs ++ [(RootRef.param position, RootRef.param earlier.2)]).eraseDups else pairs))
  have globals := idForIn_member (List.range module.globals.size) earlierAliases
    (fun global pairs => if overlaps caller roots [.global global] then
      (pairs ++ [(RootRef.param position, RootRef.global global)]).eraseDups else pairs)
    (fun pairs => pair ∈ pairs) (by intro row pairs retained; split <;> simp_all)
    global (List.mem_range.mpr bound) (by intro pairs; simp [pair, overlap])
  simp only [apply_ite, pure] at globals
  split <;> simp_all [pair, earlierAliases, apply_ite, pure, Id.run]

private theorem addArgumentAliases_static (module : Module) (caller : List (RootRef × RootRef))
    (arguments : List (List RootRef)) (roots : List RootRef) (position : Nat)
    (initial : List (RootRef × RootRef)) (overlap : overlaps caller roots [.static] = true) :
    (RootRef.param position, RootRef.static) ∈
      addArgumentAliases module caller arguments (roots, position) initial := by
  simp [addArgumentAliases, overlap, Id.run, bind, pure]

private def AliasRowsExtend (before after : Array (List (RootRef × RootRef))) : Prop :=
  before.size = after.size ∧ ∀ index, index < before.size → before[index]! ⊆ after[index]!

private theorem addCallAliases_extends (module : Module) (caller : List (RootRef × RootRef))
    (called : ContextId × List (List RootRef)) (aliases : Array (List (RootRef × RootRef))) :
    AliasRowsExtend aliases (addCallAliases module caller called aliases) := by
  constructor
  · simp [addCallAliases, Id.run, bind, pure]
  · intro index bound pair member
    unfold addCallAliases
    simp only [Id.run, bind, pure]
    by_cases selected : called.1 = index
    · subst index
      rw [Array.getElem!_set!_self _ _ _ bound]
      have initial : pair ∈ (aliases[called.1]?).getD [] := by
        rw [Array.getElem?_eq_getElem bound]
        simpa only [Option.getD_some, getElem!_pos aliases called.1 bound] using member
      exact idForIn_preserves called.2.zipIdx _ _ (fun pairs => pair ∈ pairs) initial
        (fun argument before retained => addArgumentAliases_extends module caller called.2 argument before retained)
    · rw [Array.getElem!_set!_ne _ _ _ _ selected]
      exact member

private theorem addCallAliases_member (module : Module) (caller : List (RootRef × RootRef))
    (called : ContextId × List (List RootRef)) (aliases : Array (List (RootRef × RootRef)))
    (bound : called.1 < aliases.size) (argument : List RootRef × Nat)
    (member : argument ∈ called.2.zipIdx) (pair : RootRef × RootRef)
    (generated : ∀ initial, pair ∈ addArgumentAliases module caller called.2 argument initial) :
    pair ∈ (addCallAliases module caller called aliases)[called.1]! := by
  unfold addCallAliases
  simp only [Id.run, bind, pure]
  rw [Array.getElem!_set!_self _ _ _ bound]
  exact idForIn_member called.2.zipIdx _ _ (fun pairs => pair ∈ pairs)
    (fun argument before retained => addArgumentAliases_extends module caller called.2 argument before retained)
    argument member generated

private theorem rootSetsOverlap_symm {aliases : List (RootRef × RootRef)} {left right : List RootRef}
    (overlap : RootSetsOverlap aliases left right) : RootSetsOverlap aliases right left := by
  obtain ⟨a, aMember, b, bMember, alias⟩ := overlap
  refine ⟨b, bMember, a, aMember, ?_⟩
  rcases alias with equal | forward | backward
  · exact Or.inl equal.symm
  · exact Or.inr (.inr forward)
  · exact Or.inr (.inl backward)

private theorem argument_zipIdx {arguments : List (List RootRef)} {index : Nat} {roots : List RootRef}
    (present : arguments[index]? = some roots) : (roots, index) ∈ arguments.zipIdx := by
  apply List.mem_of_getElem? (i := index)
  simp [List.getElem?_zipIdx, present]

private theorem argument_take_zipIdx {arguments : List (List RootRef)} {index cutoff : Nat} {roots : List RootRef}
    (present : arguments[index]? = some roots) (earlier : index < cutoff) :
    (roots, index) ∈ (arguments.take cutoff).zipIdx := by
  apply List.mem_of_getElem? (i := index)
  simp [List.getElem?_zipIdx, earlier, present]

private theorem addCallAliases_closes (module : Module) (caller : List (RootRef × RootRef))
    (called : ContextId × List (List RootRef)) (aliases : Array (List (RootRef × RootRef)))
    (bound : called.1 < aliases.size) :
    AliasClosure caller (addCallAliases module caller called aliases)[called.1]! called.2 module.globals.size := by
  constructor
  · intro left right a b leftAt rightAt overlap
    by_cases same : left = right
    · exact Or.inl (congrArg RootRef.param same)
    · by_cases earlier : right < left
      · right; left
        exact addCallAliases_member module caller called aliases bound (a, left) (argument_zipIdx leftAt) _
          (fun initial => addArgumentAliases_parameter module caller called.2 a b left right initial
            (argument_take_zipIdx rightAt earlier) ((rootSetsOverlap_checked caller a b).mp overlap))
      · right; right
        have before : left < right := by omega
        exact addCallAliases_member module caller called aliases bound (b, right) (argument_zipIdx rightAt) _
          (fun initial => addArgumentAliases_parameter module caller called.2 b a right left initial
            (argument_take_zipIdx leftAt before)
              ((rootSetsOverlap_checked caller b a).mp (rootSetsOverlap_symm overlap)))
  · intro index roots global present globalBound overlap
    right; left
    exact addCallAliases_member module caller called aliases bound (roots, index) (argument_zipIdx present) _
      (fun initial => addArgumentAliases_global module caller called.2 roots index global initial globalBound
        ((rootSetsOverlap_checked caller roots [.global global]).mp overlap))
  · intro index roots present overlap
    right; left
    exact addCallAliases_member module caller called aliases bound (roots, index) (argument_zipIdx present) _
      (fun initial => addArgumentAliases_static module caller called.2 roots index initial
        ((rootSetsOverlap_checked caller roots [.static]).mp overlap))

private theorem aliasRowsExtend_refl (aliases : Array (List (RootRef × RootRef))) :
    AliasRowsExtend aliases aliases := ⟨rfl, fun _ _ {_} member => member⟩

private theorem aliasRowsExtend_trans {first second third : Array (List (RootRef × RootRef))}
    (left : AliasRowsExtend first second) (right : AliasRowsExtend second third) : AliasRowsExtend first third := by
  refine ⟨left.1.trans right.1, ?_⟩
  intro index bound pair member
  exact right.2 index (left.1 ▸ bound) (left.2 index bound member)

private theorem aliasClosure_mono {caller lower upper : List (RootRef × RootRef)}
    {arguments : List (List RootRef)} {globals : Nat} (included : lower ⊆ upper)
    (closed : AliasClosure caller lower arguments globals) : AliasClosure caller upper arguments globals := by
  have extend : ∀ a b, RootAlias lower a b → RootAlias upper a b := by
    intro a b alias
    rcases alias with equal | forward | backward
    · exact Or.inl equal
    · exact Or.inr (.inl (included forward))
    · exact Or.inr (.inr (included backward))
  exact ⟨fun left right a b leftAt rightAt overlap => extend _ _ (closed.parameters left right a b leftAt rightAt overlap),
    fun index roots global present bound overlap => extend _ _ (closed.globals index roots global present bound overlap),
    fun index roots present overlap => extend _ _ (closed.static index roots present overlap)⟩

private theorem addCallsAliases_sound (module : Module) (caller : List (RootRef × RootRef))
    (calls : List (ContextId × List (List RootRef))) (initial : Array (List (RootRef × RootRef))) :
    AliasRowsExtend initial (addCallsAliases module caller calls initial) ∧
      ∀ called ∈ calls, called.1 < initial.size →
        AliasClosure caller (addCallsAliases module caller calls initial)[called.1]! called.2 module.globals.size := by
  induction calls generalizing initial with
  | nil => exact ⟨aliasRowsExtend_refl initial, fun _ absent => by cases absent⟩
  | cons called calls ih =>
    have first := addCallAliases_extends module caller called initial
    obtain ⟨extended, covered⟩ := ih (addCallAliases module caller called initial)
    refine ⟨aliasRowsExtend_trans first extended, ?_⟩
    intro selected member bound
    rcases List.mem_cons.mp member with equal | member
    · subst selected
      exact aliasClosure_mono (extended.2 called.1 (first.1 ▸ bound))
        (addCallAliases_closes module caller called initial bound)
    · exact covered selected member (first.1 ▸ bound)

private theorem addCallsAliases_forIn (module : Module) (caller : List (RootRef × RootRef))
    (calls : List (ContextId × List (List RootRef))) (aliases : Array (List (RootRef × RootRef))) :
    forIn calls aliases (fun called current =>
      (pure (.yield (addCallAliases module caller called current)) : V (ForInStep (Array (List (RootRef × RootRef)))))) =
        .ok (addCallsAliases module caller calls aliases) := by
  induction calls generalizing aliases with
  | nil => rfl
  | cons called calls ih =>
    simp only [List.forIn_cons, pure, Except.pure, bind, Except.bind]
    exact ih _

private theorem addCallAliases_expanded (module : Module) (caller : List (RootRef × RootRef))
    (called : ContextId × List (List RootRef)) (aliases : Array (List (RootRef × RootRef))) :
    addCallAliases module caller called aliases = (Id.run do
      let (context, arguments) := called
      let mut pairs := aliases[context]?.getD []
      for (roots, position) in arguments.zipIdx do
        for (earlier, previous) in (arguments.take position).zipIdx do
          if overlaps caller roots earlier then
            pairs := (pairs ++ [(RootRef.param position, RootRef.param previous)]).eraseDups
        for global in List.range module.globals.size do
          if overlaps caller roots [.global global] then
            pairs := (pairs ++ [(RootRef.param position, RootRef.global global)]).eraseDups
        if overlaps caller roots [.static] then
          pairs := (pairs ++ [(RootRef.param position, RootRef.static)]).eraseDups
      return aliases.set! context pairs) := by
  simp only [addCallAliases, addArgumentAliases, Id.run, bind, pure, apply_ite]

private theorem checkContextRootPass_expanded (module : Module)
    (escaping : Array (List (Nat × List (List RootRef)))) (aliases : Array (List (RootRef × RootRef)))
    (names : Array (List RootRef)) (row : Context × Nat) (current : ModuleRootPassState) :
    checkContextRootPass module escaping aliases names row current = (do
      let facts ← checkContextFacts module row.1 escaping aliases[row.2]! names
      let nextEscaping := current.escaping.push (joinEscapeRoots escaping[row.2]! facts.escapeRoots)
      let nextNames := current.names.set! row.2 (names[row.2]! ++ facts.namedRoots).eraseDups
      let nextAliases ← forIn facts.calls current.aliases fun called accumulated =>
        pure (.yield (addCallAliases module aliases[row.2]! called accumulated))
      pure (.yield (ModuleRootPassState.mk nextEscaping nextAliases nextNames))) := by
  unfold checkContextRootPass
  cases checked : checkContextFacts module row.1 escaping aliases[row.2]! names with
  | error error => rfl
  | ok facts =>
    simp only [bind, Except.bind, pure, Except.pure]
    have loop := addCallsAliases_forIn module aliases[row.2]! facts.calls current.aliases
    simp only [pure, Except.pure] at loop
    rw [loop]

private theorem checkInitRootPass_expanded (module : Module) (names : Array (List RootRef))
    (global : GlobalId) (current : ModuleRootPassState) :
    checkInitRootPass module names global current = (do
      let facts ← checkInitFacts module global names
      let nextAliases ← forIn facts.calls current.aliases fun called accumulated =>
        pure (.yield (addCallAliases module [] called accumulated))
      pure (.yield (ModuleRootPassState.mk current.escaping nextAliases current.names))) := by
  unfold checkInitRootPass
  cases checked : checkInitFacts module global names with
  | error error => rfl
  | ok facts =>
    simp only [bind, Except.bind, pure, Except.pure]
    have loop := addCallsAliases_forIn module [] facts.calls current.aliases
    simp only [pure, Except.pure] at loop
    rw [loop]

private theorem checkModuleRootPass_expanded (module : Module)
    (escaping : Array (List (Nat × List (List RootRef)))) (aliases : Array (List (RootRef × RootRef)))
    (names : Array (List RootRef)) :
    checkModuleRootPass module escaping aliases names = (do
      let next ← forIn module.contexts.toList.zipIdx (ModuleRootPassState.mk #[] aliases names) fun row current => do
        let facts ← checkContextFacts module row.1 escaping aliases[row.2]! names
        let nextEscaping := current.escaping.push (joinEscapeRoots escaping[row.2]! facts.escapeRoots)
        let nextNames := current.names.set! row.2 (names[row.2]! ++ facts.namedRoots).eraseDups
        let nextAliases ← forIn facts.calls current.aliases fun called accumulated =>
          pure (.yield (addCallAliases module aliases[row.2]! called accumulated))
        pure (.yield (ModuleRootPassState.mk nextEscaping nextAliases nextNames))
      forIn (List.range module.globals.size) next fun global current => do
        let facts ← checkInitFacts module global names
        let nextAliases ← forIn facts.calls current.aliases fun called accumulated =>
          pure (.yield (addCallAliases module [] called accumulated))
        pure (.yield (ModuleRootPassState.mk current.escaping nextAliases current.names))) := by
  unfold checkModuleRootPass
  change (do
    let next ← forIn module.contexts.toList.zipIdx (ModuleRootPassState.mk #[] aliases names)
      (fun row current => checkContextRootPass module escaping aliases names row current)
    forIn (List.range module.globals.size) next (fun global current => checkInitRootPass module names global current)) = _
  simp only [checkContextRootPass_expanded, checkInitRootPass_expanded]

def ContextRootFactsAt (module : Module) (context : Context) (aliases : List (RootRef × RootRef))
    (calls : List (ContextId × List (List RootRef)))
    (escaping : Array (List (Nat × List (List RootRef)))) (names : Array (List RootRef)) : Prop :=
  ∃ facts, checkContextFacts module context escaping aliases names = .ok facts ∧ facts.calls = calls

def ContextRootFacts (module : Module) (context : Context) (aliases : List (RootRef × RootRef))
    (calls : List (ContextId × List (List RootRef))) : Prop :=
  ∃ escaping names, ContextRootFactsAt module context aliases calls escaping names

def InitializerRootFacts (module : Module) (global : GlobalId)
    (calls : List (ContextId × List (List RootRef))) : Prop :=
  ∃ names facts, checkInitFacts module global names = .ok facts ∧ facts.calls = calls

def ModuleRootFacts (module : Module) : Prop :=
  ∃ aliases : Array (List (RootRef × RootRef)), aliases.size = module.contexts.size ∧
    (∀ row ∈ module.contexts.toList.zipIdx, ∃ calls, ContextRootFacts module row.1 aliases[row.2]! calls ∧
      ∀ called ∈ calls, called.1 < module.contexts.size →
        AliasClosure aliases[row.2]! aliases[called.1]! called.2 module.globals.size) ∧
    ∀ global, global < module.globals.size → ∃ calls, InitializerRootFacts module global calls ∧
      ∀ called ∈ calls, called.1 < module.contexts.size →
        AliasClosure [] aliases[called.1]! called.2 module.globals.size

private def ContextCallsCovered (module : Module) (snapshot : Array (List (RootRef × RootRef)))
    (row : Context × Nat) (current : ModuleRootPassState) : Prop :=
  ∃ calls, ContextRootFacts module row.1 snapshot[row.2]! calls ∧
    ∀ called ∈ calls, called.1 < module.contexts.size →
      AliasClosure snapshot[row.2]! current.aliases[called.1]! called.2 module.globals.size

private def InitializerCallsCovered (module : Module) (global : GlobalId) (current : ModuleRootPassState) : Prop :=
  ∃ calls, InitializerRootFacts module global calls ∧
    ∀ called ∈ calls, called.1 < module.contexts.size →
      AliasClosure [] current.aliases[called.1]! called.2 module.globals.size

private theorem contextCallsCovered_mono (module : Module) (snapshot : Array (List (RootRef × RootRef)))
    (row : Context × Nat) (before after : ModuleRootPassState)
    (sized : before.aliases.size = module.contexts.size) (extended : AliasRowsExtend before.aliases after.aliases)
    (covered : ContextCallsCovered module snapshot row before) : ContextCallsCovered module snapshot row after := by
  obtain ⟨calls, checked, covered⟩ := covered
  refine ⟨calls, checked, ?_⟩
  intro called member bound
  exact aliasClosure_mono (extended.2 called.1 (sized ▸ bound)) (covered called member bound)

private theorem initializerCallsCovered_mono (module : Module) (global : GlobalId)
    (before after : ModuleRootPassState)
    (sized : before.aliases.size = module.contexts.size) (extended : AliasRowsExtend before.aliases after.aliases)
    (covered : InitializerCallsCovered module global before) : InitializerCallsCovered module global after := by
  obtain ⟨calls, checked, covered⟩ := covered
  refine ⟨calls, checked, ?_⟩
  intro called member bound
  exact aliasClosure_mono (extended.2 called.1 (sized ▸ bound)) (covered called member bound)

private theorem rootFacts_bind_success {α β : Type} (action : V α) (next : α → V β) (result : β) :
    (action >>= next) = .ok result ↔ ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action <;> simp [bind, Except.bind]

private theorem checkedForIn_properties {α β : Type} (rows : List α) (initial : β)
    (body : α → β → V (ForInStep β)) (invariant : β → Prop) (property : α → β → Prop)
    (valid : invariant initial)
    (sound : ∀ row before step, invariant before → body row before = .ok step →
      ∃ after, step = .yield after ∧ invariant after ∧ property row after ∧
        ∀ selected, property selected before → property selected after)
    (final : β) (checked : forIn rows initial body = .ok final) :
    invariant final ∧ (∀ selected, property selected initial → property selected final) ∧
      ∀ selected ∈ rows, property selected final := by
  induction rows generalizing initial with
  | nil =>
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at checked
    subst final
    exact ⟨valid, fun _ present => present, fun _ absent => by cases absent⟩
  | cons row rows ih =>
    rw [List.forIn_cons] at checked
    obtain ⟨step, evaluated, remaining⟩ := (rootFacts_bind_success _ _ _).mp checked
    obtain ⟨after, equal, afterValid, established, preserved⟩ := sound row initial step valid evaluated
    subst step
    obtain ⟨finalValid, carried, covered⟩ := ih after afterValid remaining
    refine ⟨finalValid, fun selected present => carried selected (preserved selected present), ?_⟩
    intro selected member
    rcases List.mem_cons.mp member with equal | member
    · subst selected
      exact carried row established
    · exact covered selected member

private theorem checkContextRootPass_sound (module : Module)
    (escaping : Array (List (Nat × List (List RootRef)))) (aliases : Array (List (RootRef × RootRef)))
    (names : Array (List RootRef)) (row : Context × Nat) (before : ModuleRootPassState)
    (step : ForInStep ModuleRootPassState)
    (valid : before.aliases.size = module.contexts.size ∧ AliasRowsExtend aliases before.aliases)
    (checked : checkContextRootPass module escaping aliases names row before = .ok step) :
    ∃ after, step = .yield after ∧
      (after.aliases.size = module.contexts.size ∧ AliasRowsExtend aliases after.aliases) ∧
      ContextCallsCovered module aliases row after ∧
      ∀ selected, ContextCallsCovered module aliases selected before → ContextCallsCovered module aliases selected after := by
  unfold checkContextRootPass at checked
  obtain ⟨facts, accepted, completed⟩ := (rootFacts_bind_success _ _ _).mp checked
  simp only [pure, Except.pure, Except.ok.injEq] at completed
  subst step
  have generated := addCallsAliases_sound module aliases[row.2]! facts.calls before.aliases
  refine ⟨_, rfl, ⟨generated.1.1 ▸ valid.1, aliasRowsExtend_trans valid.2 generated.1⟩, ?_, ?_⟩
  · refine ⟨facts.calls, ⟨escaping, names, facts, accepted, rfl⟩, ?_⟩
    intro called member bound
    exact generated.2 called member (valid.1 ▸ bound)
  · intro selected covered
    exact contextCallsCovered_mono module aliases selected before _ valid.1 generated.1 covered

private def ModuleContextCoverage (module : Module) (snapshot : Array (List (RootRef × RootRef)))
    (current : ModuleRootPassState) : Prop :=
  current.aliases.size = module.contexts.size ∧ AliasRowsExtend snapshot current.aliases ∧
    ∀ row ∈ module.contexts.toList.zipIdx, ContextCallsCovered module snapshot row current

private theorem checkInitRootPass_sound (module : Module) (aliases : Array (List (RootRef × RootRef)))
    (names : Array (List RootRef)) (global : GlobalId) (before : ModuleRootPassState)
    (step : ForInStep ModuleRootPassState) (valid : ModuleContextCoverage module aliases before)
    (checked : checkInitRootPass module names global before = .ok step) :
    ∃ after, step = .yield after ∧ ModuleContextCoverage module aliases after ∧
      InitializerCallsCovered module global after ∧
      ∀ selected, InitializerCallsCovered module selected before → InitializerCallsCovered module selected after := by
  unfold checkInitRootPass at checked
  obtain ⟨facts, accepted, completed⟩ := (rootFacts_bind_success _ _ _).mp checked
  simp only [pure, Except.pure, Except.ok.injEq] at completed
  subst step
  have generated := addCallsAliases_sound module [] facts.calls before.aliases
  refine ⟨_, rfl, ⟨generated.1.1 ▸ valid.1, aliasRowsExtend_trans valid.2.1 generated.1, ?_⟩, ?_, ?_⟩
  · intro row member
    exact contextCallsCovered_mono module aliases row before _ valid.1 generated.1 (valid.2.2 row member)
  · refine ⟨facts.calls, ⟨names, facts, accepted, rfl⟩, ?_⟩
    intro called member bound
    exact generated.2 called member (valid.1 ▸ bound)
  · intro selected covered
    exact initializerCallsCovered_mono module selected before _ valid.1 generated.1 covered

private theorem checkModuleRootPass_sound (module : Module)
    (escaping : Array (List (Nat × List (List RootRef)))) (aliases : Array (List (RootRef × RootRef)))
    (names : Array (List RootRef)) (final : ModuleRootPassState)
    (sized : aliases.size = module.contexts.size)
    (checked : checkModuleRootPass module escaping aliases names = .ok final) :
    ModuleContextCoverage module aliases final ∧
      ∀ global, global < module.globals.size → InitializerCallsCovered module global final := by
  unfold checkModuleRootPass at checked
  obtain ⟨next, contexts, initializers⟩ := (rootFacts_bind_success _ _ _).mp checked
  have contextResults := checkedForIn_properties module.contexts.toList.zipIdx
    (ModuleRootPassState.mk #[] aliases names) (checkContextRootPass module escaping aliases names)
    (fun current => current.aliases.size = module.contexts.size ∧ AliasRowsExtend aliases current.aliases)
    (ContextCallsCovered module aliases) ⟨sized, aliasRowsExtend_refl aliases⟩
    (checkContextRootPass_sound module escaping aliases names) next contexts
  have initialized : ModuleContextCoverage module aliases next :=
    ⟨contextResults.1.1, contextResults.1.2, contextResults.2.2⟩
  have initializerResults := checkedForIn_properties (List.range module.globals.size) next
    (checkInitRootPass module names) (ModuleContextCoverage module aliases) (InitializerCallsCovered module)
    initialized (checkInitRootPass_sound module aliases names) final initializers
  exact ⟨initializerResults.1, fun global bound => initializerResults.2.2 global (List.mem_range.mpr bound)⟩

private theorem checkModuleRootPass_closed (module : Module)
    (escaping : Array (List (Nat × List (List RootRef)))) (aliases : Array (List (RootRef × RootRef)))
    (names : Array (List RootRef)) (final : ModuleRootPassState)
    (sized : aliases.size = module.contexts.size)
    (checked : checkModuleRootPass module escaping aliases names = .ok final)
    (stable : final.aliases = aliases) : ModuleRootFacts module := by
  obtain ⟨covered, initializers⟩ := checkModuleRootPass_sound module escaping aliases names final sized checked
  refine ⟨aliases, sized, ?_, ?_⟩
  · intro row member
    obtain ⟨calls, accepted, closed⟩ := covered.2.2 row member
    exact ⟨calls, accepted, by simpa only [stable] using closed⟩
  · intro global bound
    obtain ⟨calls, accepted, closed⟩ := initializers global bound
    exact ⟨calls, accepted, by simpa only [stable] using closed⟩

private theorem checkedForIn_invariant {α β : Type} (rows : List α) (initial : β)
    (body : α → β → V (ForInStep β)) (invariant : β → Prop) (valid : invariant initial)
    (preserved : ∀ row before step, invariant before → body row before = .ok step → invariant step.value)
    (final : β) (checked : forIn rows initial body = .ok final) : invariant final := by
  induction rows generalizing initial with
  | nil =>
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at checked
    subst final
    exact valid
  | cons row rows ih =>
    rw [List.forIn_cons] at checked
    obtain ⟨step, evaluated, remaining⟩ := (rootFacts_bind_success _ _ _).mp checked
    have nextValid := preserved row initial step valid evaluated
    cases step with
    | done value =>
      simp only [pure, Except.pure, Except.ok.injEq] at remaining
      subst final
      exact nextValid
    | yield value => exact ih value nextValid remaining

theorem checkModuleExitRoots_facts (module : Module) (checked : checkModuleExitRoots module = .ok ()) :
    ModuleRootFacts module := by
  unfold checkModuleExitRoots at checked
  dsimp only [] at checked
  simp only [Std.Legacy.Range.forIn_eq_forIn_range'] at checked
  obtain ⟨final, loop, returned⟩ := (rootFacts_bind_success _ _ _).mp checked
  let invariant (current : Option Unit × Array (List (Nat × List (List RootRef))) ×
      Array (List (RootRef × RootRef)) × Array (List RootRef)) :=
    current.2.2.1.size = module.contexts.size ∧
      ∀ output, current.1 = some output → ModuleRootFacts module
  have initial : invariant (none, Array.replicate module.contexts.size [], Array.replicate module.contexts.size [],
      Array.replicate module.contexts.size []) :=
    ⟨by simp, fun _ absent => by cases absent⟩
  have maintained := checkedForIn_invariant _ _ _ invariant initial (by
    intro index current step valid evaluated
    obtain ⟨next, pass, completed⟩ := (rootFacts_bind_success _ _ _).mp evaluated
    split at completed
    · rename_i stable
      have aliasStable : next.aliases = current.2.2.1 := by
        have both := ((Bool.and_eq_true _ _).mp stable).1
        exact eq_of_beq (((Bool.and_eq_true _ _).mp both).2)
      have facts := checkModuleRootPass_closed module current.2.1 current.2.2.1 current.2.2.2 next valid.1 pass aliasStable
      simp only [pure, Except.pure, Except.ok.injEq] at completed
      subst step
      exact ⟨valid.1, fun _ _ => facts⟩
    · have sound := checkModuleRootPass_sound module current.2.1 current.2.2.1 current.2.2.2 next valid.1 pass
      simp only [pure, Except.pure, Except.ok.injEq] at completed
      subst step
      exact ⟨sound.1.1, fun _ absent => by cases absent⟩) final loop
  cases output : final.1 with
  | none => simp [output, Goose.Core.reject] at returned
  | some value => exact maintained.2 value output

theorem contextRootFactsAt_bodyRoots (module : Module) (context : Context)
    (aliases : List (RootRef × RootRef)) (calls : List (ContextId × List (List RootRef)))
    (escaping : Array (List (Nat × List (List RootRef)))) (names : Array (List RootRef))
    (facts : ContextRootFactsAt module context aliases calls escaping names) :
    ∃ implementation bodyContext actualEscapes value state,
      module.impls[context.impl]? = some implementation ∧
      parameterBodyRootContext module implementation context = .ok bodyContext ∧
      bodyTargets module = .ok actualEscapes ∧
      (rpBlockValue { mod := module, impl := implementation, ctx := bodyContext, scopes := [], escaping := escaping, targetEscapes := actualEscapes, aliases := aliases, calleeNames := names }
        [] implementation.body).run ⟨implementation.params.size, {}, []⟩ = .ok (value, state) := by
  obtain ⟨facts, checked, _⟩ := facts
  unfold checkContextFacts at checked
  cases present : module.impls[context.impl]? with
  | none => simp [present, Goose.Core.reject] at checked
  | some implementation =>
    simp only [present] at checked
    obtain ⟨_, _, checked⟩ := (rootFacts_bind_success _ _ _).mp checked
    obtain ⟨_, _, checked⟩ := (rootFacts_bind_success _ _ _).mp checked
    obtain ⟨_, _, checked⟩ := (rootFacts_bind_success _ _ _).mp checked
    cases targets : bodyTargets module with
    | error message => simp [targets, reject, bind, Except.bind] at checked
    | ok actualEscapes =>
      simp only [targets] at checked
      obtain ⟨resolvedEscapes, escaped, checked⟩ := (rootFacts_bind_success _ _ _).mp checked
      simp only [pure, Except.pure, Except.ok.injEq] at escaped
      subst resolvedEscapes
      obtain ⟨bodyContext, closed, checked⟩ := (rootFacts_bind_success _ _ _).mp checked
      obtain ⟨⟨token, final⟩, bodyChecked, _⟩ := (rootFacts_bind_success _ _ _).mp checked
      obtain ⟨⟨value, state⟩, replay, _⟩ := (rootFacts_bind_success _ _ _).mp bodyChecked
      exact ⟨implementation, bodyContext, actualEscapes, value, state, rfl, closed, rfl, replay⟩

theorem contextRootFacts_bodyRoots (module : Module) (context : Context)
    (aliases : List (RootRef × RootRef)) (calls : List (ContextId × List (List RootRef)))
    (facts : ContextRootFacts module context aliases calls) :
    ∃ implementation bodyContext escaping actualEscapes names value state,
      module.impls[context.impl]? = some implementation ∧
      parameterBodyRootContext module implementation context = .ok bodyContext ∧
      bodyTargets module = .ok actualEscapes ∧
      (rpBlockValue { mod := module, impl := implementation, ctx := bodyContext, scopes := [], escaping := escaping, targetEscapes := actualEscapes, aliases := aliases, calleeNames := names }
        [] implementation.body).run ⟨implementation.params.size, {}, []⟩ = .ok (value, state) := by
  obtain ⟨escaping, names, checked⟩ := facts
  obtain ⟨implementation, bodyContext, actualEscapes, value, state, present, closed, targets, bodyChecked⟩ :=
    contextRootFactsAt_bodyRoots module context aliases calls escaping names checked
  exact ⟨implementation, bodyContext, escaping, actualEscapes, names, value, state,
    present, closed, targets, bodyChecked⟩

theorem contextRootFacts_annotationShape (module : Module) (context : Context)
    (aliases : List (RootRef × RootRef)) (calls : List (ContextId × List (List RootRef)))
    (facts : ContextRootFacts module context aliases calls) (implementation : Impl)
    (present : module.impls[context.impl]? = some implementation) :
    checkAnnotationShape module implementation context = .ok () := by
  obtain ⟨escaping, names, facts, checked, _⟩ := facts
  unfold checkContextFacts at checked
  simp only [present] at checked
  obtain ⟨value, accepted, _⟩ := (rootFacts_bind_success _ _ _).mp checked
  cases value
  exact accepted

end Goose.Construct
