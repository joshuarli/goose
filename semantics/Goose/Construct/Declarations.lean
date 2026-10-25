import Goose.Construct.Syntax

namespace Goose.Construct

def Ty.storageType : Ty → Bool
  | .int _ | .bool => true
  | .arr element _ | .varr element | .grow element => element.flat || element.variableElement
  | .growshrink element | .limited element _ => element.flat
  | .structT _ fields => fields.flat
  | _ => false

def Ty.storable (ty : Ty) : Bool :=
  match ty with
  | .ref _ target => target.storageType
  | .slice _ element => element.flat || element.variableElement
  | _ => ty.storageType

def Ty.element? : Ty → Option Ty
  | .arr element _ | .varr element | .grow element | .growshrink element |
      .limited element _ | .slice _ element => some element
  | _ => none

def Ty.growing : Ty → Bool
  | .grow _ | .growshrink _ | .limited _ _ => true
  | _ => false

def Ty.adaptsTo (source target : Ty) : Bool :=
  source == target || match source, target with
    | .arr a countA, .arr b countB => a == b && countA == countB
    | _, .arr .. => false
    | _, _ => match source.element?, target.element? with
      | some a, some b => a == b && source.storageType && target.storageType
      | _, _ => false

def Ty.passesTo (source target : Ty) : Bool :=
  match source, target with
  | .ref sourceMut a, .ref targetMut b | .slice sourceMut a, .slice targetMut b =>
      a == b && (sourceMut == .mutable || targetMut == .readOnly)
  | _, _ => source.adaptsTo target

def Ty.ownerElem? : Ty → Option Ty
  | .grow element | .growshrink element | .limited element _ => some element
  | _ => none

structure DeclarationEnv where
  module : Module
  variables : Array LocalVar

private inductive StatementFlow
  | next
  | breakLoop
  | continueLoop
  | valueBreak
  | escape
  deriving DecidableEq

private def continueFlow (first second : List StatementFlow) : List StatementFlow :=
  first.flatMap fun flow => if flow == .next then second else [flow]

private def escapesFlow (flow : StatementFlow) : Bool :=
  flow == .escape || flow == .valueBreak

mutual
private def statementsFlow : Nat → List Stmt → List StatementFlow
  | 0, _ => [.next]
  | _ + 1, [] => [.next]
  | fuel + 1, statement :: rest =>
      continueFlow (statementFlow fuel statement) (statementsFlow fuel rest)

private def blockFlow : Nat → Block → List StatementFlow
  | 0, _ => [.next]
  | fuel + 1, .mk _ statements tail =>
      continueFlow (statementsFlow fuel statements)
        (match tail with | none => [.next] | some expression => expressionFlow fuel expression)

private def statementFlow : Nat → Stmt → List StatementFlow
  | 0, _ => [.next]
  | fuel + 1, .ret expression _ =>
      continueFlow (match expression with | none => [.next] | some expression => expressionFlow fuel expression) [.escape]
  | fuel + 1, .retValues expressions _ | fuel + 1, .returnFrom _ expressions _ =>
      continueFlow (expressionsFlow fuel expressions) [.escape]
  | fuel + 1, .retForward expression _ | fuel + 1, .returnFromForward _ expression _ |
    fuel + 1, .exit expression _ => continueFlow (expressionFlow fuel expression) [.escape]
  | fuel + 1, .breakValue expression _ => continueFlow (expressionFlow fuel expression) [.valueBreak]
  | _ + 1, .abort .. => [.escape]
  | _ + 1, .brk _ => [.breakLoop]
  | _ + 1, .cont _ => [.continueLoop]
  | fuel + 1, .ifS condition left right _ =>
      continueFlow (expressionFlow fuel condition)
        (blockFlow fuel left ++ (match right with | some block => blockFlow fuel block | none => [.next]))
  | fuel + 1, .while condition body _ =>
      let bodyFlow := blockFlow fuel body
      let escapes := bodyFlow.filter escapesFlow
      continueFlow (expressionFlow fuel condition)
        (if (match condition with | .bool true => true | _ => false) && !bodyFlow.contains .breakLoop then escapes else .next :: escapes)
  | fuel + 1, .forRange _ first last body _ =>
      continueFlow (expressionFlow fuel first) (continueFlow (expressionFlow fuel last)
        (.next :: (blockFlow fuel body).filter escapesFlow))
  | fuel + 1, .forEach _ _ view _ body _ =>
      continueFlow (viewFlow fuel view) (.next :: (blockFlow fuel body).filter escapesFlow)
  | fuel + 1, .letS _ expression _ | fuel + 1, .rebind _ expression _ |
    fuel + 1, .expr expression _ | fuel + 1, .receive _ expression _ |
    fuel + 1, .assertS expression _ => expressionFlow fuel expression
  | fuel + 1, .assign place expression _ | fuel + 1, .assignOp _ place expression _ |
    fuel + 1, .popN place expression _ | fuel + 1, .assignWhole place expression _ |
    fuel + 1, .appendValue place expression _ | fuel + 1, .appendConstruct place expression _ =>
      continueFlow (placeFlow fuel place) (expressionFlow fuel expression)
  | fuel + 1, .append place view _ => continueFlow (placeFlow fuel place) (viewFlow fuel view)
  | fuel + 1, .resize place expression fill _ =>
      continueFlow (placeFlow fuel place) (continueFlow (expressionFlow fuel expression)
        (match fill with | none => [.next] | some value => expressionFlow fuel value))
  | fuel + 1, .clear place _ => placeFlow fuel place
  | fuel + 1, .print arguments _ => printArgumentsFlow fuel arguments

private def expressionFlow : Nat → Expr → List StatementFlow
  | 0, _ => [.next]
  | fuel + 1, .read place | fuel + 1, .ref _ place | fuel + 1, .copy _ place _ |
    fuel + 1, .pop place _ => placeFlow fuel place
  | fuel + 1, .slice _ view lo hi _ =>
      continueFlow (viewFlow fuel view) (continueFlow (boundFlow fuel lo) (boundFlow fuel hi))
  | fuel + 1, .len view => viewFlow fuel view
  | fuel + 1, .un _ expression _ | fuel + 1, .not expression |
    fuel + 1, .conv _ _ expression _ | fuel + 1, .fill _ expression _ => expressionFlow fuel expression
  | fuel + 1, .bin _ left right _ | fuel + 1, .cmp _ left right =>
      continueFlow (expressionFlow fuel left) (expressionFlow fuel right)
  | fuel + 1, .and left right =>
      continueFlow (expressionFlow fuel left) (match left with
        | .bool false => [.next]
        | .bool true => expressionFlow fuel right
        | _ => .next :: expressionFlow fuel right)
  | fuel + 1, .or left right =>
      continueFlow (expressionFlow fuel left) (match left with
        | .bool true => [.next]
        | .bool false => expressionFlow fuel right
        | _ => .next :: expressionFlow fuel right)
  | fuel + 1, .call _ arguments _ => argumentsFlow fuel arguments
  | fuel + 1, .push place expression _ => continueFlow (placeFlow fuel place) (expressionFlow fuel expression)
  | fuel + 1, .ifE condition left right _ =>
      continueFlow (expressionFlow fuel condition) (blockFlow fuel left ++ blockFlow fuel right)
  | fuel + 1, .blockE block _ =>
      (blockFlow fuel block).map fun flow => if flow == .valueBreak then .next else flow
  | fuel + 1, .arrLit _ expressions _ | fuel + 1, .structLit _ expressions |
    fuel + 1, .values expressions => expressionsFlow fuel expressions
  | fuel + 1, .str _ arguments _ => printArgumentsFlow fuel arguments
  | _, _ => [.next]

private def expressionsFlow : Nat → List Expr → List StatementFlow
  | 0, _ => [.next]
  | _ + 1, [] => [.next]
  | fuel + 1, expression :: rest => continueFlow (expressionFlow fuel expression) (expressionsFlow fuel rest)

private def placeFlow : Nat → Place → List StatementFlow
  | 0, _ => [.next]
  | fuel + 1, .deref expression => expressionFlow fuel expression
  | fuel + 1, .elem view expression _ => continueFlow (viewFlow fuel view) (expressionFlow fuel expression)
  | fuel + 1, .field place _ => placeFlow fuel place
  | _, _ => [.next]

private def viewFlow : Nat → View → List StatementFlow
  | 0, _ => [.next]
  | fuel + 1, .of place => placeFlow fuel place
  | fuel + 1, .val expression => expressionFlow fuel expression

private def boundFlow : Nat → Bound → List StatementFlow
  | 0, _ => [.next]
  | fuel + 1, .expr expression | fuel + 1, .fromEnd expression => expressionFlow fuel expression
  | _, _ => [.next]

private def argumentsFlow : Nat → List Arg → List StatementFlow
  | 0, _ => [.next]
  | _ + 1, [] => [.next]
  | fuel + 1, argument :: rest => continueFlow (argumentFlow fuel argument) (argumentsFlow fuel rest)

private def argumentFlow : Nat → Arg → List StatementFlow
  | 0, _ => [.next]
  | fuel + 1, .byVal expression | fuel + 1, .construct expression => expressionFlow fuel expression
  | fuel + 1, .byRef _ place => placeFlow fuel place

private def printArgumentsFlow : Nat → List PrintArg → List StatementFlow
  | 0, _ => [.next]
  | _ + 1, [] => [.next]
  | fuel + 1, argument :: rest => continueFlow (printArgumentFlow fuel argument) (printArgumentsFlow fuel rest)

private def printArgumentFlow : Nat → PrintArg → List StatementFlow
  | 0, _ => [.next]
  | fuel + 1, .expr expression => expressionFlow fuel expression
  | fuel + 1, .view view => viewFlow fuel view
  | _, _ => [.next]
end

def blockEscapes (fuel : Nat) (block : Block) : Bool :=
  (blockFlow fuel block).all (· != .next)

mutual
def expressionQueryBudget : Expr → Nat
  | .read place | .ref _ place | .copy _ place _ | .pop place _ => placeQueryBudget place + 1
  | .slice _ view lo hi _ => viewQueryBudget view + boundQueryBudget lo + boundQueryBudget hi + 1
  | .len view => viewQueryBudget view + 1
  | .un _ expression _ | .not expression | .conv _ _ expression _ | .fill _ expression _ => expressionQueryBudget expression + 1
  | .bin _ left right _ | .cmp _ left right | .and left right | .or left right => expressionQueryBudget left + expressionQueryBudget right + 1
  | .call _ arguments _ => argumentsQueryBudget arguments + 1
  | .push place expression _ => placeQueryBudget place + expressionQueryBudget expression + 1
  | .ifE condition left right _ => expressionQueryBudget condition + blockQueryBudget left + blockQueryBudget right + 1
  | .blockE block _ => blockQueryBudget block + 1
  | .arrLit _ expressions _ | .structLit _ expressions | .values expressions => expressionListQueryBudget expressions + 1
  | .str _ arguments _ => printArgumentsQueryBudget arguments + 1
  | _ => 1

private def expressionListQueryBudget : List Expr → Nat
  | [] => 0 + 1
  | expression :: rest => expressionQueryBudget expression + expressionListQueryBudget rest + 1

def blockQueryBudget : Block → Nat
  | .mk _ statements tail => statementsQueryBudget statements + (match tail with | none => 1 | some expression => expressionQueryBudget expression) + 1

private def statementsQueryBudget : List Stmt → Nat
  | [] => 0 + 1
  | statement :: rest => statementQueryBudget statement + statementsQueryBudget rest + 1

private def statementQueryBudget : Stmt → Nat
  | .ret expression _ => (match expression with | none => 1 | some expression => expressionQueryBudget expression) + 1
  | .retValues expressions _ | .returnFrom _ expressions _ => expressionListQueryBudget expressions + 1
  | .retForward expression _ | .returnFromForward _ expression _ | .exit expression _ | .breakValue expression _ | .letS _ expression _ | .rebind _ expression _ | .expr expression _ | .receive _ expression _ | .assertS expression _ => expressionQueryBudget expression + 1
  | .ifS condition left right _ => expressionQueryBudget condition + blockQueryBudget left + (match right with | none => 1 | some block => blockQueryBudget block) + 1
  | .while condition body _ => expressionQueryBudget condition + blockQueryBudget body + 1
  | .forRange _ first last body _ => expressionQueryBudget first + expressionQueryBudget last + blockQueryBudget body + 1
  | .forEach _ _ view _ body _ => viewQueryBudget view + blockQueryBudget body + 1
  | .assign place expression _ | .assignOp _ place expression _ | .popN place expression _ | .assignWhole place expression _ | .appendValue place expression _ | .appendConstruct place expression _ => placeQueryBudget place + expressionQueryBudget expression + 1
  | .append place view _ => placeQueryBudget place + viewQueryBudget view + 1
  | .resize place expression fill _ => placeQueryBudget place + expressionQueryBudget expression + (match fill with | none => 1 | some value => expressionQueryBudget value) + 1
  | .clear place _ => placeQueryBudget place + 1
  | .print arguments _ => printArgumentsQueryBudget arguments + 1
  | _ => 1

private def placeQueryBudget : Place → Nat
  | .deref expression => expressionQueryBudget expression + 1
  | .elem view expression _ => viewQueryBudget view + expressionQueryBudget expression + 1
  | .field place _ => placeQueryBudget place + 1
  | _ => 1

private def viewQueryBudget : View → Nat
  | .of place => placeQueryBudget place + 1
  | .val expression => expressionQueryBudget expression + 1

private def boundQueryBudget : Bound → Nat
  | .expr expression | .fromEnd expression => expressionQueryBudget expression + 1
  | _ => 1

private def argumentsQueryBudget : List Arg → Nat
  | [] => 0 + 1
  | argument :: rest => argumentQueryBudget argument + argumentsQueryBudget rest + 1

private def argumentQueryBudget : Arg → Nat
  | .byVal expression | .construct expression => expressionQueryBudget expression + 1
  | .byRef _ place => placeQueryBudget place + 1

private def printArgumentsQueryBudget : List PrintArg → Nat
  | [] => 0 + 1
  | argument :: rest => printArgumentQueryBudget argument + printArgumentsQueryBudget rest + 1

private def printArgumentQueryBudget : PrintArg → Nat
  | .expr expression => expressionQueryBudget expression + 1
  | .view view => viewQueryBudget view + 1
  | _ => 1

end

mutual
def DeclarationEnv.placeType? (env : DeclarationEnv) : Place → Option Ty
  | .var x => (env.variables[x]?).map (·.ty)
  | .global g => (env.module.globals[g]?).map (·.ty)
  | .deref e => do
    match ← env.exprType? e with
    | .ref _ t => some t
    | _ => none
  | .elem v _ _ => env.viewElement? v
  | .field p i => do
    match ← env.placeType? p with
    | .structT sid _ => ((← env.module.structs[sid]?).fields[i]?).map (·.ty)
    | _ => none

termination_by place => 4 * sizeOf place
decreasing_by all_goals simp_wf <;> omega

def DeclarationEnv.viewElement? (env : DeclarationEnv) : View → Option Ty
  | .of p => do
    match ← env.placeType? p with
    | .arr t _ | .varr t | .grow t | .growshrink t | .limited t _ => some t
    | _ => none
  | .val e => do
    match ← env.exprType? e with
    | .slice _ t => some t
    | _ => none

termination_by view => 4 * sizeOf view
decreasing_by all_goals simp_wf <;> omega

def DeclarationEnv.exprType? (env : DeclarationEnv) : Expr → Option Ty
  | .lit t _ => some (.int t)
  | .bool _ | .cmp .. | .and .. | .or .. | .not _ => some .bool
  | .read p => env.placeType? p
  | .ref m p => (env.placeType? p).map (.ref m)
  | .slice m v _ _ _ => (env.viewElement? v).map (.slice m)
  | .len _ => some (.int .i64)
  | .un _ e _ => env.exprType? e
  | .bin _ a _ _ => env.exprType? a
  | .conv _ t _ _ => some t
  | .call c _ _ => do
    let context ← env.module.contexts[c]?
    let impl ← env.module.impls[context.impl]?
    match impl.results.toList with
    | [] => some .unit
    | [t] => some t.ty
    | _ => none
  | .push p _ _ => do some (.ref .mutable (← (← env.placeType? p).ownerElem?))
  | .pop p _ => do (← env.placeType? p).ownerElem?
  | .ifE _ left right _ =>
      let fuel := blockQueryBudget left + blockQueryBudget right + 1
      if blockEscapes fuel left && !blockEscapes fuel right then env.blockType? right
      else env.blockType? left
  | .blockE b _ => env.blockType? b
  | .arrLit t _ _ | .fill t _ _ | .structLit t _ | .bytes t _ _ | .str t _ _ | .copy t _ _ => some t
  | .resultLocal id _ => (env.variables[id]?).map (·.ty)
  | .values _ => none

termination_by expression => 4 * sizeOf expression + 1
decreasing_by all_goals simp_wf <;> omega

def DeclarationEnv.blockType? (env : DeclarationEnv) : Block → Option Ty
  | block =>
      match blockResultTypes? (blockQueryBudget block) env block with
      | some [ty] => some ty
      | _ => none
termination_by block => 4 * sizeOf block + 3
decreasing_by all_goals simp_wf <;> omega

def expressionResultTypes? : Nat → DeclarationEnv → Expr → Option (List Ty)
  | 0, _, _ => none
  | fuel + 1, env, .values expressions => do
      let channels ← expressionsResultTypes? fuel env expressions
      if channels.all (fun types => types.length == 1) then some channels.flatten else none
  | _, env, .call contextId _ _ => do
      let context ← env.module.contexts[contextId]?
      let implementation ← env.module.impls[context.impl]?
      some (implementation.results.toList.map (·.ty))
  | fuel + 1, env, .blockE block _ => blockResultTypes? fuel env block
  | fuel + 1, env, .ifE _ left right _ =>
      let leftTypes := blockResultTypes? fuel env left
      let rightTypes := blockResultTypes? fuel env right
      if blockEscapes fuel left then
        if blockEscapes fuel right then leftTypes <|> rightTypes else rightTypes
      else if blockEscapes fuel right then leftTypes
      else leftTypes <|> rightTypes
  | _ + 1, env, expression => (env.exprType? expression).map (fun ty => [ty])

termination_by _ _ expression => 4 * sizeOf expression + 2
decreasing_by all_goals simp_wf <;> omega

private def expressionsResultTypes? : Nat → DeclarationEnv → List Expr → Option (List (List Ty))
  | _, _, [] => some []
  | fuel, env, expression :: expressions => do
      pure ((← expressionResultTypes? fuel env expression) :: (← expressionsResultTypes? fuel env expressions))
termination_by _ _ expressions => 4 * sizeOf expressions
decreasing_by all_goals simp_wf <;> omega

def blockResultTypes? : Nat → DeclarationEnv → Block → Option (List Ty)
  | 0, _, _ => none
  | fuel + 1, env, .mk _ statements tail =>
      match tail with
      | some expression => expressionResultTypes? fuel env expression
      | none => firstValueBreakTypes fuel env statements <|> some [.unit]

termination_by _ _ block => 4 * sizeOf block + 2
decreasing_by all_goals simp_wf <;> omega

private def firstValueBreakTypes : Nat → DeclarationEnv → List Stmt → Option (List Ty)
  | 0, _, _ => none
  | _ + 1, _, [] => none
  | fuel + 1, env, statement :: rest =>
      let current := match statement with
        | .breakValue expression _ => expressionResultTypes? fuel env expression
        | .ifS _ (.mk _ left _) right _ =>
            firstValueBreakTypes fuel env left <|>
              (match right with
              | none => none
              | some (.mk _ statements _) => firstValueBreakTypes fuel env statements)
        | .while _ (.mk _ statements _) _ |
          .forRange _ _ _ (.mk _ statements _) _ |
          .forEach _ _ _ _ (.mk _ statements _) _ => firstValueBreakTypes fuel env statements
        | _ => none
      current <|> firstValueBreakTypes fuel env rest
termination_by _ _ statements => 4 * sizeOf statements
decreasing_by all_goals simp_wf <;> omega

end

set_option Elab.async false

theorem statementsFlow_transition (fuel : Nat) (input : List Stmt) :
    statementsFlow fuel input = (match fuel, input with
  | 0, _ => [.next]
  | _ + 1, [] => [.next]
  | fuel + 1, statement :: rest =>
      continueFlow (statementFlow fuel statement) (statementsFlow fuel rest)) := by
  cases fuel <;> cases input <;> rfl

theorem blockFlow_transition (fuel : Nat) (input : Block) :
    blockFlow fuel input = (match fuel, input with
  | 0, _ => [.next]
  | fuel + 1, .mk _ statements tail =>
      continueFlow (statementsFlow fuel statements)
        (match tail with | none => [.next] | some expression => expressionFlow fuel expression)) := by
  cases fuel <;> cases input <;> rfl

theorem statementFlow_transition (fuel : Nat) (input : Stmt) :
    statementFlow fuel input = (match fuel, input with
  | 0, _ => [.next]
  | fuel + 1, .ret expression _ =>
      continueFlow (match expression with | none => [.next] | some expression => expressionFlow fuel expression) [.escape]
  | fuel + 1, .retValues expressions _ | fuel + 1, .returnFrom _ expressions _ =>
      continueFlow (expressionsFlow fuel expressions) [.escape]
  | fuel + 1, .retForward expression _ | fuel + 1, .returnFromForward _ expression _ |
    fuel + 1, .exit expression _ => continueFlow (expressionFlow fuel expression) [.escape]
  | fuel + 1, .breakValue expression _ => continueFlow (expressionFlow fuel expression) [.valueBreak]
  | _ + 1, .abort .. => [.escape]
  | _ + 1, .brk _ => [.breakLoop]
  | _ + 1, .cont _ => [.continueLoop]
  | fuel + 1, .ifS condition left right _ =>
      continueFlow (expressionFlow fuel condition)
        (blockFlow fuel left ++ (match right with | some block => blockFlow fuel block | none => [.next]))
  | fuel + 1, .while condition body _ =>
      let bodyFlow := blockFlow fuel body
      let escapes := bodyFlow.filter escapesFlow
      continueFlow (expressionFlow fuel condition)
        (if (match condition with | .bool true => true | _ => false) && !bodyFlow.contains .breakLoop then escapes else .next :: escapes)
  | fuel + 1, .forRange _ first last body _ =>
      continueFlow (expressionFlow fuel first) (continueFlow (expressionFlow fuel last)
        (.next :: (blockFlow fuel body).filter escapesFlow))
  | fuel + 1, .forEach _ _ view _ body _ =>
      continueFlow (viewFlow fuel view) (.next :: (blockFlow fuel body).filter escapesFlow)
  | fuel + 1, .letS _ expression _ | fuel + 1, .rebind _ expression _ |
    fuel + 1, .expr expression _ | fuel + 1, .receive _ expression _ |
    fuel + 1, .assertS expression _ => expressionFlow fuel expression
  | fuel + 1, .assign place expression _ | fuel + 1, .assignOp _ place expression _ |
    fuel + 1, .popN place expression _ | fuel + 1, .assignWhole place expression _ |
    fuel + 1, .appendValue place expression _ | fuel + 1, .appendConstruct place expression _ =>
      continueFlow (placeFlow fuel place) (expressionFlow fuel expression)
  | fuel + 1, .append place view _ => continueFlow (placeFlow fuel place) (viewFlow fuel view)
  | fuel + 1, .resize place expression fill _ =>
      continueFlow (placeFlow fuel place) (continueFlow (expressionFlow fuel expression)
        (match fill with | none => [.next] | some value => expressionFlow fuel value))
  | fuel + 1, .clear place _ => placeFlow fuel place
  | fuel + 1, .print arguments _ => printArgumentsFlow fuel arguments) := by
  cases fuel <;> cases input <;> rfl

theorem expressionFlow_transition (fuel : Nat) (input : Expr) :
    expressionFlow fuel input = (match fuel, input with
  | 0, _ => [.next]
  | fuel + 1, .read place | fuel + 1, .ref _ place | fuel + 1, .copy _ place _ |
    fuel + 1, .pop place _ => placeFlow fuel place
  | fuel + 1, .slice _ view lo hi _ =>
      continueFlow (viewFlow fuel view) (continueFlow (boundFlow fuel lo) (boundFlow fuel hi))
  | fuel + 1, .len view => viewFlow fuel view
  | fuel + 1, .un _ expression _ | fuel + 1, .not expression |
    fuel + 1, .conv _ _ expression _ | fuel + 1, .fill _ expression _ => expressionFlow fuel expression
  | fuel + 1, .bin _ left right _ | fuel + 1, .cmp _ left right =>
      continueFlow (expressionFlow fuel left) (expressionFlow fuel right)
  | fuel + 1, .and left right =>
      continueFlow (expressionFlow fuel left) (match left with
        | .bool false => [.next]
        | .bool true => expressionFlow fuel right
        | _ => .next :: expressionFlow fuel right)
  | fuel + 1, .or left right =>
      continueFlow (expressionFlow fuel left) (match left with
        | .bool true => [.next]
        | .bool false => expressionFlow fuel right
        | _ => .next :: expressionFlow fuel right)
  | fuel + 1, .call _ arguments _ => argumentsFlow fuel arguments
  | fuel + 1, .push place expression _ => continueFlow (placeFlow fuel place) (expressionFlow fuel expression)
  | fuel + 1, .ifE condition left right _ =>
      continueFlow (expressionFlow fuel condition) (blockFlow fuel left ++ blockFlow fuel right)
  | fuel + 1, .blockE block _ =>
      (blockFlow fuel block).map fun flow => if flow == .valueBreak then .next else flow
  | fuel + 1, .arrLit _ expressions _ | fuel + 1, .structLit _ expressions |
    fuel + 1, .values expressions => expressionsFlow fuel expressions
  | fuel + 1, .str _ arguments _ => printArgumentsFlow fuel arguments
  | _, _ => [.next]) := by
  cases fuel <;> cases input <;> rfl

theorem expressionsFlow_transition (fuel : Nat) (input : List Expr) :
    expressionsFlow fuel input = (match fuel, input with
  | 0, _ => [.next]
  | _ + 1, [] => [.next]
  | fuel + 1, expression :: rest => continueFlow (expressionFlow fuel expression) (expressionsFlow fuel rest)) := by
  cases fuel <;> cases input <;> rfl

theorem placeFlow_transition (fuel : Nat) (input : Place) :
    placeFlow fuel input = (match fuel, input with
  | 0, _ => [.next]
  | fuel + 1, .deref expression => expressionFlow fuel expression
  | fuel + 1, .elem view expression _ => continueFlow (viewFlow fuel view) (expressionFlow fuel expression)
  | fuel + 1, .field place _ => placeFlow fuel place
  | _, _ => [.next]) := by
  cases fuel <;> cases input <;> rfl

theorem viewFlow_transition (fuel : Nat) (input : View) :
    viewFlow fuel input = (match fuel, input with
  | 0, _ => [.next]
  | fuel + 1, .of place => placeFlow fuel place
  | fuel + 1, .val expression => expressionFlow fuel expression) := by
  cases fuel <;> cases input <;> rfl

theorem boundFlow_transition (fuel : Nat) (input : Bound) :
    boundFlow fuel input = (match fuel, input with
  | 0, _ => [.next]
  | fuel + 1, .expr expression | fuel + 1, .fromEnd expression => expressionFlow fuel expression
  | _, _ => [.next]) := by
  cases fuel <;> cases input <;> rfl

theorem argumentsFlow_transition (fuel : Nat) (input : List Arg) :
    argumentsFlow fuel input = (match fuel, input with
  | 0, _ => [.next]
  | _ + 1, [] => [.next]
  | fuel + 1, argument :: rest => continueFlow (argumentFlow fuel argument) (argumentsFlow fuel rest)) := by
  cases fuel <;> cases input <;> rfl

theorem argumentFlow_transition (fuel : Nat) (input : Arg) :
    argumentFlow fuel input = (match fuel, input with
  | 0, _ => [.next]
  | fuel + 1, .byVal expression | fuel + 1, .construct expression => expressionFlow fuel expression
  | fuel + 1, .byRef _ place => placeFlow fuel place) := by
  cases fuel <;> cases input <;> rfl

theorem printArgumentsFlow_transition (fuel : Nat) (input : List PrintArg) :
    printArgumentsFlow fuel input = (match fuel, input with
  | 0, _ => [.next]
  | _ + 1, [] => [.next]
  | fuel + 1, argument :: rest => continueFlow (printArgumentFlow fuel argument) (printArgumentsFlow fuel rest)) := by
  cases fuel <;> cases input <;> rfl

theorem printArgumentFlow_transition (fuel : Nat) (input : PrintArg) :
    printArgumentFlow fuel input = (match fuel, input with
  | 0, _ => [.next]
  | fuel + 1, .expr expression => expressionFlow fuel expression
  | fuel + 1, .view view => viewFlow fuel view
  | _, _ => [.next]) := by
  cases fuel <;> cases input <;> rfl

theorem continueFlow_transition (first second : List StatementFlow) :
    continueFlow first second = first.flatMap (fun flow => if flow == .next then second else [flow]) := rfl

theorem escapesFlow_transition (flow : StatementFlow) :
    escapesFlow flow = (flow == .escape || flow == .valueBreak) := rfl

theorem expressionsResultTypes?_transition (fuel : Nat) (env : DeclarationEnv)
    (expressions : List Expr) :
    expressionsResultTypes? fuel env expressions = (match expressions with
      | [] => some []
      | expression :: rest => do
          pure ((← expressionResultTypes? fuel env expression) ::
            (← expressionsResultTypes? fuel env rest))) := by
  cases expressions <;> simp only [expressionsResultTypes?]

theorem firstValueBreakTypes_transition (fuel : Nat) (env : DeclarationEnv)
    (statements : List Stmt) :
    firstValueBreakTypes fuel env statements = (match fuel, statements with
      | 0, _ => none
      | _ + 1, [] => none
      | fuel + 1, statement :: rest =>
          let current := match statement with
            | .breakValue expression _ => expressionResultTypes? fuel env expression
            | .ifS _ (.mk _ left _) right _ =>
                firstValueBreakTypes fuel env left <|>
                  (match right with
                  | none => none
                  | some (.mk _ statements _) => firstValueBreakTypes fuel env statements)
            | .while _ (.mk _ statements _) _ |
              .forRange _ _ _ (.mk _ statements _) _ |
              .forEach _ _ _ _ (.mk _ statements _) _ => firstValueBreakTypes fuel env statements
            | _ => none
          current <|> firstValueBreakTypes fuel env rest) := by
  conv => lhs; unfold firstValueBreakTypes
  cases fuel <;> cases statements <;> rfl

private theorem statementsQueryBudget_pos (input : List Stmt) : 0 < statementsQueryBudget input := by
  cases input
  all_goals change 0 < _ + 1; exact Nat.zero_lt_succ _

private theorem blockQueryBudget_pos (input : Block) : 0 < blockQueryBudget input := by
  cases input
  case mk scope statements tail =>
    cases tail <;> change 0 < _ + 1 <;> exact Nat.zero_lt_succ _

private theorem statementQueryBudget_pos (input : Stmt) : 0 < statementQueryBudget input := by
  cases input
  case ret value origin =>
    cases value <;> change 0 < _ + 1 <;> exact Nat.zero_lt_succ _
  case ifS condition left right origin =>
    cases right <;> change 0 < _ + 1 <;> exact Nat.zero_lt_succ _
  case resize place value fill origin =>
    cases fill <;> change 0 < _ + 1 <;> exact Nat.zero_lt_succ _
  all_goals change 0 < _ + 1; exact Nat.zero_lt_succ _

private theorem expressionQueryBudget_pos (input : Expr) : 0 < expressionQueryBudget input := by
  cases input
  all_goals change 0 < _ + 1; exact Nat.zero_lt_succ _

private theorem expressionListQueryBudget_pos (input : List Expr) : 0 < expressionListQueryBudget input := by
  cases input
  all_goals change 0 < _ + 1; exact Nat.zero_lt_succ _

private theorem placeQueryBudget_pos (input : Place) : 0 < placeQueryBudget input := by
  cases input
  all_goals change 0 < _ + 1; exact Nat.zero_lt_succ _

private theorem viewQueryBudget_pos (input : View) : 0 < viewQueryBudget input := by
  cases input
  all_goals change 0 < _ + 1; exact Nat.zero_lt_succ _

private theorem boundQueryBudget_pos (input : Bound) : 0 < boundQueryBudget input := by
  cases input
  all_goals change 0 < _ + 1; exact Nat.zero_lt_succ _

private theorem argumentsQueryBudget_pos (input : List Arg) : 0 < argumentsQueryBudget input := by
  cases input
  all_goals change 0 < _ + 1; exact Nat.zero_lt_succ _

private theorem argumentQueryBudget_pos (input : Arg) : 0 < argumentQueryBudget input := by
  cases input
  all_goals change 0 < _ + 1; exact Nat.zero_lt_succ _

private theorem printArgumentsQueryBudget_pos (input : List PrintArg) : 0 < printArgumentsQueryBudget input := by
  cases input
  all_goals change 0 < _ + 1; exact Nat.zero_lt_succ _

private theorem printArgumentQueryBudget_pos (input : PrintArg) : 0 < printArgumentQueryBudget input := by
  cases input
  all_goals change 0 < _ + 1; exact Nat.zero_lt_succ _

mutual
theorem statementsFlow_budget (statements : List Stmt) (fuel other : Nat)
    (enough : statementsQueryBudget statements ≤ fuel) (also : statementsQueryBudget statements ≤ other) :
    statementsFlow fuel statements = statementsFlow other statements := by
  have positive := statementsQueryBudget_pos statements
  cases fuel with
  | zero => omega
  | succ fuel =>
    cases other with
    | zero => omega
    | succ other =>
      cases statements
      all_goals simp only [statementsQueryBudget] at enough also
      all_goals simp only [statementsFlow]
      all_goals first | rfl | simp (disch := omega) only [statementsFlow_budget (fuel := fuel) (other := other), statementFlow_budget (fuel := fuel) (other := other)]
termination_by fuel

theorem blockFlow_budget (block : Block) (fuel other : Nat)
    (enough : blockQueryBudget block ≤ fuel) (also : blockQueryBudget block ≤ other) :
    blockFlow fuel block = blockFlow other block := by
  have positive := blockQueryBudget_pos block
  cases fuel with
  | zero => omega
  | succ fuel =>
    cases other with
    | zero => omega
    | succ other =>
      cases block
      case mk scope statements tail =>
        cases tail
        all_goals simp only [blockQueryBudget] at enough also
        all_goals simp only [blockFlow]
        all_goals first | rfl | simp (disch := omega) only [statementsFlow_budget (fuel := fuel) (other := other), expressionFlow_budget (fuel := fuel) (other := other)]
termination_by fuel

theorem statementFlow_budget (statement : Stmt) (fuel other : Nat)
    (enough : statementQueryBudget statement ≤ fuel) (also : statementQueryBudget statement ≤ other) :
    statementFlow fuel statement = statementFlow other statement := by
  have positive := statementQueryBudget_pos statement
  cases fuel with
  | zero => omega
  | succ fuel =>
    cases other with
    | zero => omega
    | succ other =>
      cases statement
      case ret value origin =>
        cases value
        all_goals simp only [statementQueryBudget] at enough also
        all_goals simp only [statementFlow]
        all_goals first | rfl | simp (disch := omega) only [blockFlow_budget (fuel := fuel) (other := other), expressionFlow_budget (fuel := fuel) (other := other), expressionsFlow_budget (fuel := fuel) (other := other), placeFlow_budget (fuel := fuel) (other := other), viewFlow_budget (fuel := fuel) (other := other), printArgumentsFlow_budget (fuel := fuel) (other := other)]
      case ifS condition left right origin =>
        cases right
        all_goals simp only [statementQueryBudget] at enough also
        all_goals simp only [statementFlow]
        all_goals first | rfl | simp (disch := omega) only [blockFlow_budget (fuel := fuel) (other := other), expressionFlow_budget (fuel := fuel) (other := other), expressionsFlow_budget (fuel := fuel) (other := other), placeFlow_budget (fuel := fuel) (other := other), viewFlow_budget (fuel := fuel) (other := other), printArgumentsFlow_budget (fuel := fuel) (other := other)]
      case resize place value fill origin =>
        cases fill
        all_goals simp only [statementQueryBudget] at enough also
        all_goals simp only [statementFlow]
        all_goals first | rfl | simp (disch := omega) only [blockFlow_budget (fuel := fuel) (other := other), expressionFlow_budget (fuel := fuel) (other := other), expressionsFlow_budget (fuel := fuel) (other := other), placeFlow_budget (fuel := fuel) (other := other), viewFlow_budget (fuel := fuel) (other := other), printArgumentsFlow_budget (fuel := fuel) (other := other)]
      all_goals simp only [statementQueryBudget] at enough also
      all_goals simp only [statementFlow]
      all_goals first | rfl | simp (disch := omega) only [blockFlow_budget (fuel := fuel) (other := other), expressionFlow_budget (fuel := fuel) (other := other), expressionsFlow_budget (fuel := fuel) (other := other), placeFlow_budget (fuel := fuel) (other := other), viewFlow_budget (fuel := fuel) (other := other), printArgumentsFlow_budget (fuel := fuel) (other := other)]
termination_by fuel

theorem expressionFlow_budget (expression : Expr) (fuel other : Nat)
    (enough : expressionQueryBudget expression ≤ fuel) (also : expressionQueryBudget expression ≤ other) :
    expressionFlow fuel expression = expressionFlow other expression := by
  have positive := expressionQueryBudget_pos expression
  cases fuel with
  | zero => omega
  | succ fuel =>
    cases other with
    | zero => omega
    | succ other =>
      cases expression
      all_goals simp only [expressionQueryBudget] at enough also
      all_goals simp only [expressionFlow]
      all_goals first | rfl | simp (disch := omega) only [blockFlow_budget (fuel := fuel) (other := other), expressionFlow_budget (fuel := fuel) (other := other), expressionsFlow_budget (fuel := fuel) (other := other), placeFlow_budget (fuel := fuel) (other := other), viewFlow_budget (fuel := fuel) (other := other), boundFlow_budget (fuel := fuel) (other := other), argumentsFlow_budget (fuel := fuel) (other := other), printArgumentsFlow_budget (fuel := fuel) (other := other)]
termination_by fuel

theorem expressionsFlow_budget (expressions : List Expr) (fuel other : Nat)
    (enough : expressionListQueryBudget expressions ≤ fuel) (also : expressionListQueryBudget expressions ≤ other) :
    expressionsFlow fuel expressions = expressionsFlow other expressions := by
  have positive := expressionListQueryBudget_pos expressions
  cases fuel with
  | zero => omega
  | succ fuel =>
    cases other with
    | zero => omega
    | succ other =>
      cases expressions
      all_goals simp only [expressionListQueryBudget] at enough also
      all_goals simp only [expressionsFlow]
      all_goals first | rfl | simp (disch := omega) only [expressionFlow_budget (fuel := fuel) (other := other), expressionsFlow_budget (fuel := fuel) (other := other)]
termination_by fuel

theorem placeFlow_budget (place : Place) (fuel other : Nat)
    (enough : placeQueryBudget place ≤ fuel) (also : placeQueryBudget place ≤ other) :
    placeFlow fuel place = placeFlow other place := by
  have positive := placeQueryBudget_pos place
  cases fuel with
  | zero => omega
  | succ fuel =>
    cases other with
    | zero => omega
    | succ other =>
      cases place
      all_goals simp only [placeQueryBudget] at enough also
      all_goals simp only [placeFlow]
      all_goals first | rfl | simp (disch := omega) only [expressionFlow_budget (fuel := fuel) (other := other), placeFlow_budget (fuel := fuel) (other := other), viewFlow_budget (fuel := fuel) (other := other)]
termination_by fuel

theorem viewFlow_budget (view : View) (fuel other : Nat)
    (enough : viewQueryBudget view ≤ fuel) (also : viewQueryBudget view ≤ other) :
    viewFlow fuel view = viewFlow other view := by
  have positive := viewQueryBudget_pos view
  cases fuel with
  | zero => omega
  | succ fuel =>
    cases other with
    | zero => omega
    | succ other =>
      cases view
      all_goals simp only [viewQueryBudget] at enough also
      all_goals simp only [viewFlow]
      all_goals first | rfl | simp (disch := omega) only [expressionFlow_budget (fuel := fuel) (other := other), placeFlow_budget (fuel := fuel) (other := other)]
termination_by fuel

theorem boundFlow_budget (bound : Bound) (fuel other : Nat)
    (enough : boundQueryBudget bound ≤ fuel) (also : boundQueryBudget bound ≤ other) :
    boundFlow fuel bound = boundFlow other bound := by
  have positive := boundQueryBudget_pos bound
  cases fuel with
  | zero => omega
  | succ fuel =>
    cases other with
    | zero => omega
    | succ other =>
      cases bound
      all_goals simp only [boundQueryBudget] at enough also
      all_goals simp only [boundFlow]
      all_goals first | rfl | simp (disch := omega) only [expressionFlow_budget (fuel := fuel) (other := other)]
termination_by fuel

theorem argumentsFlow_budget (arguments : List Arg) (fuel other : Nat)
    (enough : argumentsQueryBudget arguments ≤ fuel) (also : argumentsQueryBudget arguments ≤ other) :
    argumentsFlow fuel arguments = argumentsFlow other arguments := by
  have positive := argumentsQueryBudget_pos arguments
  cases fuel with
  | zero => omega
  | succ fuel =>
    cases other with
    | zero => omega
    | succ other =>
      cases arguments
      all_goals simp only [argumentsQueryBudget] at enough also
      all_goals simp only [argumentsFlow]
      all_goals first | rfl | simp (disch := omega) only [argumentsFlow_budget (fuel := fuel) (other := other), argumentFlow_budget (fuel := fuel) (other := other)]
termination_by fuel

theorem argumentFlow_budget (argument : Arg) (fuel other : Nat)
    (enough : argumentQueryBudget argument ≤ fuel) (also : argumentQueryBudget argument ≤ other) :
    argumentFlow fuel argument = argumentFlow other argument := by
  have positive := argumentQueryBudget_pos argument
  cases fuel with
  | zero => omega
  | succ fuel =>
    cases other with
    | zero => omega
    | succ other =>
      cases argument
      all_goals simp only [argumentQueryBudget] at enough also
      all_goals simp only [argumentFlow]
      all_goals first | rfl | simp (disch := omega) only [expressionFlow_budget (fuel := fuel) (other := other), placeFlow_budget (fuel := fuel) (other := other)]
termination_by fuel

theorem printArgumentsFlow_budget (arguments : List PrintArg) (fuel other : Nat)
    (enough : printArgumentsQueryBudget arguments ≤ fuel) (also : printArgumentsQueryBudget arguments ≤ other) :
    printArgumentsFlow fuel arguments = printArgumentsFlow other arguments := by
  have positive := printArgumentsQueryBudget_pos arguments
  cases fuel with
  | zero => omega
  | succ fuel =>
    cases other with
    | zero => omega
    | succ other =>
      cases arguments
      all_goals simp only [printArgumentsQueryBudget] at enough also
      all_goals simp only [printArgumentsFlow]
      all_goals first | rfl | simp (disch := omega) only [printArgumentsFlow_budget (fuel := fuel) (other := other), printArgumentFlow_budget (fuel := fuel) (other := other)]
termination_by fuel

theorem printArgumentFlow_budget (argument : PrintArg) (fuel other : Nat)
    (enough : printArgumentQueryBudget argument ≤ fuel) (also : printArgumentQueryBudget argument ≤ other) :
    printArgumentFlow fuel argument = printArgumentFlow other argument := by
  have positive := printArgumentQueryBudget_pos argument
  cases fuel with
  | zero => omega
  | succ fuel =>
    cases other with
    | zero => omega
    | succ other =>
      cases argument
      all_goals simp only [printArgumentQueryBudget] at enough also
      all_goals simp only [printArgumentFlow]
      all_goals first | rfl | simp (disch := omega) only [expressionFlow_budget (fuel := fuel) (other := other), viewFlow_budget (fuel := fuel) (other := other)]
termination_by fuel

end

theorem blockEscapes_budget (block : Block) (fuel other : Nat)
    (enough : blockQueryBudget block ≤ fuel)
    (also : blockQueryBudget block ≤ other) :
    blockEscapes fuel block = blockEscapes other block := by
  unfold blockEscapes
  rw [blockFlow_budget block fuel other enough also]

end Goose.Construct
