import Goose.Construct.Targets

namespace Goose.Construct
open Goose.Core (VarId ImplId)

mutual
def expressionVariables : Expr → List VarId
  | .lit .. | .bool _ | .bytes .. => []
  | .resultLocal id _ => [id]
  | .read place | .ref _ place | .copy _ place _ => placeVariables place
  | .slice _ view low high _ => viewVariables view ++ boundVariables low ++ boundVariables high
  | .len view => viewVariables view
  | .un _ expression _ | .not expression | .conv _ _ expression _ | .fill _ expression _ => expressionVariables expression
  | .bin _ left right _ | .cmp _ left right | .and left right | .or left right =>
      expressionVariables left ++ expressionVariables right
  | .call _ arguments _ => argumentVariables arguments
  | .push owner expression _ => placeVariables owner ++ expressionVariables expression
  | .pop owner _ => placeVariables owner
  | .ifE condition left right _ => expressionVariables condition ++ blockVariables left ++ blockVariables right
  | .blockE block _ => blockVariables block
  | .arrLit _ elements _ | .structLit _ elements | .values elements => expressionsVariables elements
  | .str _ arguments _ => printVariables arguments

def placeVariables : Place → List VarId
  | .var id => [id]
  | .global _ => []
  | .deref expression => expressionVariables expression
  | .elem view index _ => viewVariables view ++ expressionVariables index
  | .field owner _ => placeVariables owner

def viewVariables : View → List VarId
  | .of place => placeVariables place
  | .val expression => expressionVariables expression

def boundVariables : Bound → List VarId
  | .expr expression | .fromEnd expression => expressionVariables expression
  | .omitted => []

def expressionsVariables : List Expr → List VarId
  | [] => []
  | expression :: rest => expressionVariables expression ++ expressionsVariables rest

def argumentVariables : List Arg → List VarId
  | [] => []
  | .byVal expression :: rest | .construct expression :: rest => expressionVariables expression ++ argumentVariables rest
  | .byRef _ place :: rest => placeVariables place ++ argumentVariables rest

def printVariables : List PrintArg → List VarId
  | [] => []
  | .text _ :: rest => printVariables rest
  | .expr expression :: rest => expressionVariables expression ++ printVariables rest
  | .view view :: rest => viewVariables view ++ printVariables rest

def blockVariables : Block → List VarId
  | .mk _ statements tail => statementsVariables statements ++ (match tail with
      | none => []
      | some expression => expressionVariables expression)

def statementsVariables : List Stmt → List VarId
  | [] => []
  | statement :: rest => statementVariables statement ++ statementsVariables rest

def statementVariables : Stmt → List VarId
  | .letS _ expression _ | .rebind _ expression _ | .expr expression _ | .assertS expression _ |
      .exit expression _ | .receive _ expression _ | .retForward expression _ | .breakValue expression _ |
      .returnFromForward _ expression _ => expressionVariables expression
  | .assign owner expression _ | .assignOp _ owner expression _ | .assignWhole owner expression _ |
      .appendValue owner expression _ | .appendConstruct owner expression _ => placeVariables owner ++ expressionVariables expression
  | .append owner view _ => placeVariables owner ++ viewVariables view
  | .popN owner count _ => placeVariables owner ++ expressionVariables count
  | .resize owner count fill _ => placeVariables owner ++ expressionVariables count ++ (match fill with
      | none => []
      | some expression => expressionVariables expression)
  | .clear owner _ => placeVariables owner
  | .ifS condition left right _ => expressionVariables condition ++ blockVariables left ++ (match right with
      | none => []
      | some block => blockVariables block)
  | .while condition body _ => expressionVariables condition ++ blockVariables body
  | .forRange _ low high body _ => expressionVariables low ++ expressionVariables high ++ blockVariables body
  | .forEach _ _ view _ body _ => viewVariables view ++ blockVariables body
  | .ret expression _ => match expression with | none => [] | some value => expressionVariables value
  | .retValues operands _ | .returnFrom _ operands _ => expressionsVariables operands
  | .brk _ | .cont _ | .abort .. => []
  | .print arguments _ => printVariables arguments
end

inductive NamedSite
  | operands (values : List Expr)
  | forwarded
  | alias (id : VarId) (initializer : Expr)

mutual
def nestedExpressionReturns (module : Module) (implementation : ImplId) : Expr → List NamedSite
  | .lit .. | .bool _ | .bytes .. | .resultLocal .. => []
  | .read place | .ref _ place | .copy _ place _ => nestedPlaceReturns module implementation place
  | .slice _ view low high _ => nestedViewReturns module implementation view ++
      nestedBoundReturns module implementation low ++ nestedBoundReturns module implementation high
  | .len view => nestedViewReturns module implementation view
  | .un _ expression _ | .not expression | .conv _ _ expression _ | .fill _ expression _ =>
      nestedExpressionReturns module implementation expression
  | .bin _ left right _ | .cmp _ left right | .and left right | .or left right =>
      nestedExpressionReturns module implementation left ++ nestedExpressionReturns module implementation right
  | .call context arguments org =>
      (arguments.flatMap fun argument => match argument with
        | .byRef .mutable place =>
            (placeVariables place).map fun id => .alias id (.call context arguments org)
        | _ => []) ++ nestedArgumentReturns module implementation arguments
  | .push owner expression _ => nestedPlaceReturns module implementation owner ++ nestedExpressionReturns module implementation expression
  | .pop owner _ => nestedPlaceReturns module implementation owner
  | .ifE condition left right _ => nestedExpressionReturns module implementation condition ++
      nestedBlockReturns module implementation left ++ nestedBlockReturns module implementation right
  | .blockE block _ => nestedBlockReturns module implementation block
  | .arrLit _ elements _ | .structLit _ elements | .values elements => nestedExpressionsReturns module implementation elements
  | .str _ arguments _ => nestedPrintReturns module implementation arguments

def nestedPlaceReturns (module : Module) (implementation : ImplId) : Place → List NamedSite
  | .var _ | .global _ => []
  | .deref expression => nestedExpressionReturns module implementation expression
  | .elem view index _ => nestedViewReturns module implementation view ++ nestedExpressionReturns module implementation index
  | .field owner _ => nestedPlaceReturns module implementation owner

def nestedViewReturns (module : Module) (implementation : ImplId) : View → List NamedSite
  | .of place => nestedPlaceReturns module implementation place
  | .val expression => nestedExpressionReturns module implementation expression

def nestedBoundReturns (module : Module) (implementation : ImplId) : Bound → List NamedSite
  | .omitted => []
  | .expr expression | .fromEnd expression => nestedExpressionReturns module implementation expression

def nestedExpressionsReturns (module : Module) (implementation : ImplId) : List Expr → List NamedSite
  | [] => []
  | expression :: rest => nestedExpressionReturns module implementation expression ++ nestedExpressionsReturns module implementation rest

def nestedArgumentReturns (module : Module) (implementation : ImplId) : List Arg → List NamedSite
  | [] => []
  | .byVal expression :: rest | .construct expression :: rest => nestedExpressionReturns module implementation expression ++
      nestedArgumentReturns module implementation rest
  | .byRef _ place :: rest => nestedPlaceReturns module implementation place ++ nestedArgumentReturns module implementation rest

def nestedPrintReturns (module : Module) (implementation : ImplId) : List PrintArg → List NamedSite
  | [] => []
  | .text _ :: rest => nestedPrintReturns module implementation rest
  | .expr expression :: rest => nestedExpressionReturns module implementation expression ++ nestedPrintReturns module implementation rest
  | .view view :: rest => nestedViewReturns module implementation view ++ nestedPrintReturns module implementation rest

def nestedBlockReturns (module : Module) (implementation : ImplId) : Block → List NamedSite
  | .mk _ statements tail => nestedStatementsReturns module implementation statements ++ (match tail with
      | none => []
      | some expression => nestedExpressionReturns module implementation expression)

def nestedStatementsReturns (module : Module) (implementation : ImplId) : List Stmt → List NamedSite
  | [] => []
  | statement :: rest => nestedStatementReturns module implementation statement ++ nestedStatementsReturns module implementation rest

def nestedStatementReturns (module : Module) (implementation : ImplId) : Stmt → List NamedSite
  | .ret none _ => [.operands []]
  | .ret (some expression) _ => .operands [expression] :: nestedExpressionReturns module implementation expression
  | .retValues operands _ => .operands operands :: nestedExpressionsReturns module implementation operands
  | .retForward producer _ => .forwarded :: nestedExpressionReturns module implementation producer
  | .returnFrom target operands _ =>
      (if (module.targets[target]?).any (fun target => target.contains implementation) then [.operands operands] else []) ++
        nestedExpressionsReturns module implementation operands
  | .returnFromForward target producer _ =>
      (if (module.targets[target]?).any (fun target => target.contains implementation) then [.forwarded] else []) ++
        nestedExpressionReturns module implementation producer
  | .letS id expression _ | .rebind id expression _ =>
      .alias id expression :: nestedExpressionReturns module implementation expression
  | .receive ids expression _ => ids.map (fun id => .alias id expression) ++
      nestedExpressionReturns module implementation expression
  | .expr expression _ | .assertS expression _ | .exit expression _ | .breakValue expression _ =>
      nestedExpressionReturns module implementation expression
  | .assign owner expression _ | .assignOp _ owner expression _ | .assignWhole owner expression _ |
      .appendValue owner expression _ | .appendConstruct owner expression _ => nestedPlaceReturns module implementation owner ++
        nestedExpressionReturns module implementation expression
  | .append owner view _ => nestedPlaceReturns module implementation owner ++ nestedViewReturns module implementation view
  | .popN owner count _ => nestedPlaceReturns module implementation owner ++ nestedExpressionReturns module implementation count
  | .resize owner count fill _ => nestedPlaceReturns module implementation owner ++ nestedExpressionReturns module implementation count ++
      (match fill with
        | none => []
        | some expression => nestedExpressionReturns module implementation expression)
  | .clear owner _ => nestedPlaceReturns module implementation owner
  | .ifS condition left right _ => nestedExpressionReturns module implementation condition ++
      nestedBlockReturns module implementation left ++ (match right with
        | none => []
        | some block => nestedBlockReturns module implementation block)
  | .while condition body _ => nestedExpressionReturns module implementation condition ++ nestedBlockReturns module implementation body
  | .forRange _ low high body _ => nestedExpressionReturns module implementation low ++
      nestedExpressionReturns module implementation high ++ nestedBlockReturns module implementation body
  | .forEach _ _ view _ body _ => nestedViewReturns module implementation view ++ nestedBlockReturns module implementation body
  | .brk _ | .cont _ | .abort .. => []
  | .print arguments _ => nestedPrintReturns module implementation arguments
end

private def bodyDeclared (body : Block) (id : VarId) : Bool :=
  body.stmts.any fun statement => match statement with
    | .letS localVar _ _ => localVar == id
    | _ => false

private def aliases (module : Module) (id : ImplId) (implementation : Impl) : List (VarId × List VarId) :=
  (nestedBlockReturns module id implementation.body).filterMap fun site => match site with
    | .alias variableId expression =>
        match implementation.vars[variableId]?.map (·.ty) with
        | some (Ty.ref _ _) | some (Ty.slice _ _) => some (variableId, expressionVariables expression)
        | _ => none
    | _ => none

private def reachesLocal (module : Module) (id : ImplId) (implementation : Impl)
    (candidate : VarId) (variables : List VarId) : Bool := Id.run do
  let mut reached := variables
  for _ in [0:implementation.vars.size] do
    for (alias, sources) in aliases module id implementation do
      if reached.contains alias then reached := (reached ++ sources).eraseDups
  return reached.contains candidate

private def siteCandidate (position : Nat) : NamedSite → Option VarId
  | .forwarded | .alias .. => none
  | .operands operands => match operands[position]? with
    | some (.resultLocal id _) => some id
    | _ => none

private def independentSite (module : Module) (id : ImplId) (implementation : Impl) (position candidate : Nat) : NamedSite → Bool
  | .forwarded | .alias .. => false
  | .operands operands => match operands[position]? with
    | none => false
    | some (.resultLocal id _) => id == candidate
    | some expression => !reachesLocal module id implementation candidate (expressionVariables expression)

private def candidatesFor (module : Module) (id : ImplId) (implementation : Impl) (position : Nat) : List VarId :=
  let sites := nestedBlockReturns module id implementation.body ++ (match implementation.body.value with
    | none => []
    | some (.values operands) => [.operands operands]
    | some expression => [.operands [expression]])
  let sites := sites.filter fun site => match site with
    | .alias .. => false
    | _ => true
  let candidates := sites.filterMap (siteCandidate position)
  candidates.eraseDups.filter fun candidate =>
    bodyDeclared implementation.body candidate &&
      sites.all (independentSite module id implementation position candidate)

def discoverNamedResults (module : Module) (id : ImplId) (implementation : Impl) : List (Option VarId) := Id.run do
  let mut used : List VarId := []
  let mut found : List (Option VarId) := []
  for (descriptor, position) in implementation.results.toList.zipIdx do
    let candidate := if descriptor.ty.nonfixed && descriptor.request == .value then
      (candidatesFor module id implementation position).find? fun candidate =>
        !used.contains candidate && (implementation.vars[candidate]?).any fun localVar =>
          localVar.ty == descriptor.ty || match localVar.ty, descriptor.ty with
            | .grow element, .varr resultElement | .growshrink element, .varr resultElement |
              .limited element _, .varr resultElement => element == resultElement
            | _, _ => false
      else none
    if let some localVar := candidate then used := localVar :: used
    found := found ++ [candidate]
  return found

def checkNamedResults (module : Module) : Except String Unit :=
  module.impls.toList.zipIdx.forM fun (implementation, id) => do
    if implementation.results.toList.map (·.namedLocal) != discoverNamedResults module id implementation then
      throw "V-RESULT: named result aliases disagree with structural eligibility"

end Goose.Construct
