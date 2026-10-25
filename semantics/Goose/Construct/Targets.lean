import Goose.Construct.Syntax

namespace Goose.Construct
open Goose.Core (ContextId ImplId)

structure ControlFacts where
  calls : List ContextId := []
  returnsFrom : List Nat := []
  deriving DecidableEq, Repr

def ControlFacts.join (a b : ControlFacts) : ControlFacts :=
  ⟨a.calls ++ b.calls, a.returnsFrom ++ b.returnsFrom⟩

mutual
def exprControl : Expr → ControlFacts
  | .lit .. | .bool _ | .resultLocal .. | .bytes .. => {}
  | .read p | .ref _ p | .copy _ p _ => placeControl p
  | .slice _ v lo hi _ => (viewControl v).join ((boundControl lo).join (boundControl hi))
  | .len v => viewControl v
  | .un _ e _ | .not e | .conv _ _ e _ | .fill _ e _ => exprControl e
  | .bin _ a b _ | .cmp _ a b | .and a b | .or a b => (exprControl a).join (exprControl b)
  | .call context args _ => (ControlFacts.mk [context] []).join (argsControl args)
  | .push owner e _ => (placeControl owner).join (exprControl e)
  | .pop owner _ => placeControl owner
  | .ifE condition left right _ => (exprControl condition).join ((blockControl left).join (blockControl right))
  | .blockE block _ => blockControl block
  | .arrLit _ elements _ | .structLit _ elements | .values elements => exprsControl elements
  | .str _ args _ => printControl args

def placeControl : Place → ControlFacts
  | .var _ | .global _ => {}
  | .deref e => exprControl e
  | .elem v index _ => (viewControl v).join (exprControl index)
  | .field owner _ => placeControl owner

def viewControl : View → ControlFacts
  | .of place => placeControl place
  | .val e => exprControl e

def boundControl : Bound → ControlFacts
  | .expr e | .fromEnd e => exprControl e
  | .omitted => {}

def exprsControl : List Expr → ControlFacts
  | [] => {}
  | expression :: rest => (exprControl expression).join (exprsControl rest)

def argsControl : List Arg → ControlFacts
  | [] => {}
  | .byVal expression :: rest | .construct expression :: rest =>
      (exprControl expression).join (argsControl rest)
  | .byRef _ place :: rest => (placeControl place).join (argsControl rest)

def blockControl : Block → ControlFacts
  | .mk _ statements tail => (stmtsControl statements).join (match tail with
      | none => {}
      | some expression => exprControl expression)

def stmtsControl : List Stmt → ControlFacts
  | [] => {}
  | statement :: rest => (stmtControl statement).join (stmtsControl rest)

def printControl : List PrintArg → ControlFacts
  | [] => {}
  | .text _ :: rest => printControl rest
  | .expr expression :: rest => (exprControl expression).join (printControl rest)
  | .view view :: rest => (viewControl view).join (printControl rest)

def stmtControl : Stmt → ControlFacts
  | .letS _ e _ | .rebind _ e _ | .expr e _ | .assertS e _ | .exit e _ |
    .receive _ e _ | .retForward e _ | .breakValue e _ => exprControl e
  | .assign owner e _ | .assignOp _ owner e _ | .assignWhole owner e _ |
    .appendValue owner e _ | .appendConstruct owner e _ => (placeControl owner).join (exprControl e)
  | .append owner view _ => (placeControl owner).join (viewControl view)
  | .popN owner count _ => (placeControl owner).join (exprControl count)
  | .resize owner count fill _ =>
      (placeControl owner).join ((exprControl count).join (match fill with
        | none => {}
        | some expression => exprControl expression))
  | .clear owner _ => placeControl owner
  | .ifS condition left right _ =>
      (exprControl condition).join ((blockControl left).join (match right with
        | none => {}
        | some block => blockControl block))
  | .while condition body _ => (exprControl condition).join (blockControl body)
  | .forRange _ low high body _ =>
      (exprControl low).join ((exprControl high).join (blockControl body))
  | .forEach _ _ view _ body _ => (viewControl view).join (blockControl body)
  | .ret expression _ => match expression with | none => {} | some e => exprControl e
  | .retValues operands _ => exprsControl operands
  | .returnFrom target operands _ => (ControlFacts.mk [] [target]).join (exprsControl operands)
  | .returnFromForward target producer _ => (ControlFacts.mk [] [target]).join (exprControl producer)
  | .brk _ | .cont _ | .abort .. => {}
  | .print args _ => printControl args
end

private def canonical (targets : List Nat) : List Nat :=
  targets.mergeSort.eraseDups

def handledTargets (module : Module) (implementation : ImplId) : List Nat :=
  (module.targets.toList.zipIdx.filterMap fun (target, id) =>
    if target.contains implementation then some id else none)

private def externalTargets (module : Module) (implementation : ImplId) (targets : List Nat) : List Nat :=
  targets.filter fun target => !(handledTargets module implementation).contains target

private def summaryNeeds (module : Module) (implementation : ImplId) : List Nat :=
  match module.impls[implementation]? with
  | some impl => match impl.summary with
    | .known summary => summary.needs
    | .unknown => (List.range module.targets.size)
  | none => List.range module.targets.size

def requiredTargetStep (module : Module) (requirements : Array (List Nat)) :
    Except String (Array (List Nat)) :=
  module.impls.mapIdxM fun id impl => do
    let facts := blockControl impl.body
    let mut needed := facts.returnsFrom
    for contextId in facts.calls do
      let some context := module.contexts[contextId]? | throw "call context outside table"
      let some required := requirements[context.impl]? | throw "call implementation outside table"
      needed := needed ++ required
    pure (canonical (externalTargets module id needed ++ summaryNeeds module id))

def requiredTargets (module : Module) : Except String (Array (List Nat)) := do
  let mut requirements := Array.replicate module.impls.size []
  for _ in [0:module.impls.size * module.targets.size + 1] do
    requirements ← requiredTargetStep module requirements
  pure requirements

def bodyTargetStep (module : Module) (requirements : Array (List Nat)) :
    Except String (Array (List Nat)) :=
  module.impls.mapIdxM fun id impl => do
    let facts := blockControl impl.body
    let mut needed := facts.returnsFrom
    for contextId in facts.calls do
      let some context := module.contexts[contextId]? | throw "call context outside table"
      let some required := requirements[context.impl]? | throw "call implementation outside table"
      needed := needed ++ required
    pure (canonical (externalTargets module id needed))

def bodyTargets (module : Module) : Except String (Array (List Nat)) := do
  let mut requirements := Array.replicate module.impls.size []
  for _ in [0:module.impls.size * module.targets.size + 1] do
    requirements ← bodyTargetStep module requirements
  pure requirements

def checkTargetSummaries (module : Module) : Except String Unit := do
  let actual ← bodyTargets module
  for h : id in [0:module.impls.size] do
    let impl := module.impls[id]
    let some needed := actual[id]? | throw "target summary analysis lost an implementation"
    match impl.summary with
    | .unknown => pure ()
    | .known summary =>
        if !(needed.all summary.needs.contains) then
          throw "V-SUMMARY: missing required nonlocal target"
        if !(needed.all summary.escapes.contains) then
          throw "V-SUMMARY: missing propagated nonlocal target"

def checkTargetProtocols (module : Module) : Except String Unit := do
  for target in module.targets do
    let some first := module.impls[target.first]? | throw "target member outside implementation table"
    for member in target.rest do
      let some impl := module.impls[member]? | throw "target member outside implementation table"
      if (impl.results.toList.map fun r => (r.ty, r.request)) !=
          (first.results.toList.map fun r => (r.ty, r.request)) then
        throw "V-RESULT: target members have different result protocols"

def checkTargetAvailability (module : Module) : Except String Unit := do
  checkTargetProtocols module
  checkTargetSummaries module
  let requirements ← requiredTargets module
  let some entry := module.contexts[module.entry]? | throw "entry context outside table"
  let some entryRequirements := requirements[entry.impl]? | throw "entry implementation outside table"
  if !entryRequirements.isEmpty then throw "V-CALL: entry requires an inactive nonlocal target"
  for global in module.globals do
    let facts := exprControl global.init
    if !facts.returnsFrom.isEmpty then throw "V-CALL: global initializer returns to an inactive target"
    for contextId in facts.calls do
      let some context := module.contexts[contextId]? | throw "initializer call context outside table"
      let some needed := requirements[context.impl]? | throw "initializer call implementation outside table"
      if !needed.isEmpty then throw "V-CALL: initializer call requires an inactive nonlocal target"

end Goose.Construct
