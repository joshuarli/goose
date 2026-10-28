import Goose.Lower.TypedCall
import Goose.Lower.TypedGlobals

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Lower

inductive DemandLoweringAction where
  | expression (expression : Expr)
  | place (place : Place)
  | view (view : View)
  | bound (bound : Bound)
  | argument (argument : Arg)
  | eachSource (view : View)
  | statement (loop : Option LoopCtx) (statement : Stmt)
  | block (loop : Option LoopCtx) (parameters : List (SlotId × ValueId × OriginId)) (want : Bool) (block : Core.Block)

def DemandLoweringAction.node : DemandLoweringAction → DemandNode
  | .expression expr => .expression expr
  | .place location => .place location
  | .view source => .view source
  | .bound limit => .bound limit
  | .argument (.byVal expr) => .expression expr
  | .argument (.byRef _ location) => .place location
  | .eachSource source => .view source
  | .statement _ stmt => .statement stmt
  | .block _ _ _ body => .block body

def DemandLoweringAction.Result : DemandLoweringAction → Type
  | .expression _ | .place _ | .view _ | .argument _ | .block _ _ _ _ => ValueId
  | .bound _ => Bnd
  | .eachSource _ => Option ValueId × ValueId
  | .statement _ _ => Unit

def DemandLoweringAction.run (action : DemandLoweringAction) (le : LEnv) (before : LS) : action.Result × LS :=
  match action with
  | .expression expr => lowerExpr expr le before
  | .place location => lowerPlace location le before
  | .view source => lowerView source le before
  | .bound limit => lowerBound limit le before
  | .argument arg => lowerArg arg le before
  | .eachSource source => lowerEachSource source le before
  | .statement loop stmt => lowerStmt loop stmt le before
  | .block loop parameters want body => lowerBlock loop parameters want body le before

inductive DemandLoweringAction.FirstChild : DemandLoweringAction → DemandLoweringAction → Prop
  | expression {parent child : Expr}
      (found : DemandNode.child? (.expression parent) 0 = some (.expression child)) :
      FirstChild (.expression parent) (.expression child)
  | expressionPlace {parent : Expr} {child : Place}
      (found : DemandNode.child? (.expression parent) 0 = some (.place child)) :
      FirstChild (.expression parent) (.place child)
  | expressionView {parent : Expr} {child : View}
      (found : DemandNode.child? (.expression parent) 0 = some (.view child)) :
      FirstChild (.expression parent) (.view child)
  | expressionBlock (block : Core.Block) :
      FirstChild (.expression (.blockE block)) (.block none [] true block)
  | placeExpression {parent : Place} {child : Expr}
      (found : DemandNode.child? (.place parent) 0 = some (.expression child)) :
      FirstChild (.place parent) (.expression child)
  | place {parent child : Place}
      (found : DemandNode.child? (.place parent) 0 = some (.place child)) :
      FirstChild (.place parent) (.place child)
  | placeView {parent : Place} {child : View}
      (found : DemandNode.child? (.place parent) 0 = some (.view child)) :
      FirstChild (.place parent) (.view child)
  | viewExpression {parent : View} {child : Expr}
      (found : DemandNode.child? (.view parent) 0 = some (.expression child)) :
      FirstChild (.view parent) (.expression child)
  | viewPlace {parent : View} {child : Place}
      (found : DemandNode.child? (.view parent) 0 = some (.place child)) :
      FirstChild (.view parent) (.place child)
  | bound {parent : Bound} {child : Expr}
      (found : DemandNode.child? (.bound parent) 0 = some (.expression child)) :
      FirstChild (.bound parent) (.expression child)
  | ifCondition (loop : Option LoopCtx) (condition : Expr) (yes : Core.Block) (no : Option Core.Block) (origin : OriginId) :
      FirstChild (.statement loop (.ifS condition yes no origin)) (.expression condition)
  | discard (loop : Option LoopCtx) (expression : Expr) (origin : OriginId) :
      FirstChild (.statement loop (.expr expression origin)) (.expression expression)

theorem DemandLoweringAction.FirstChild.source {parent child : DemandLoweringAction}
    (first : parent.FirstChild child) : parent.node.child? 0 = some child.node := by
  cases first <;> simp only [node]
  all_goals first | assumption | rfl

def demandBlockStatementsBefore (le : LEnv) (before : LS) (parameters : List (SlotId × ValueId × OriginId))
    (block : Core.Block) : LS :=
  let entered := (emitEffect (.enter block.scope) le before).2
  (initSlots parameters le { entered with stack := block.scope :: entered.stack }).2

def demandWhileHeaderBefore (le : LEnv) (before : LS) : LS :=
  let header := newBlock [] le before
  let jumped := emitTerm (.br header.1.1 []) le header.2
  { jumped.2 with cur := some header.1.1 }

inductive GeneratedDemandOccurrence (m : Core.Module) :
    Func → LEnv → DemandNode → List Nat → DemandLoweringAction → LS → Prop
  | functionRoot {contextId : ContextId} {context : Context} {implementation : Impl}
      (contextAt : m.contexts[contextId]? = some context)
      (implementationAt : m.impls[context.impl]? = some implementation) :
      GeneratedDemandOccurrence m (lowerContextAt m context implementation)
        (lowerEnv m implementation.vars implementation.results.toList) (.block implementation.body) []
        (.block none (callPre implementation) false implementation.body) (callEntry implementation)
  | globalRoot {globalId : GlobalId} {global : Core.Global} (globalAt : m.globals[globalId]? = some global) :
      GeneratedDemandOccurrence m (lowerGlobal m global).init (lowerEnv m #[] [global.ty])
        (.expression global.init) [] (.expression global.init) startLS
  | first {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat}
      {parent child : DemandLoweringAction} {before : LS}
      (occurrence : GeneratedDemandOccurrence m function le root path parent before)
      (first : parent.FirstChild child) :
      GeneratedDemandOccurrence m function le root (path ++ [0]) child before
  | whileCondition {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {loop : Option LoopCtx} {condition : Expr} {body : Core.Block} {origin : OriginId}
      (occurrence : GeneratedDemandOccurrence m function le root path (.statement loop (.while condition body origin)) before) :
      GeneratedDemandOccurrence m function le root (path ++ [0]) (.expression condition) (demandWhileHeaderBefore le before)
  | binaryRight {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {operation : BinOp} {left right : Expr} {origin : OriginId}
      (occurrence : GeneratedDemandOccurrence m function le root path (.expression (.bin operation left right origin)) before) :
      GeneratedDemandOccurrence m function le root (path ++ [1]) (.expression right) (lowerExpr left le before).2
  | comparisonRight {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {operation : CmpOp} {left right : Expr}
      (occurrence : GeneratedDemandOccurrence m function le root path (.expression (.cmp operation left right)) before) :
      GeneratedDemandOccurrence m function le root (path ++ [1]) (.expression right) (lowerExpr left le before).2
  | shortCircuitRight {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {isAnd : Bool} {left right : Expr}
      (occurrence : GeneratedDemandOccurrence m function le root path
        (.expression (if isAnd then .and left right else .or left right)) before)
      (live : (lowerExpr left le before).2.cur.isSome = true) :
      GeneratedDemandOccurrence m function le root (path ++ [1]) (.expression right)
        { (scFork isAnd (lowerExpr left le before).1 le (lowerExpr left le before).2).2 with
          cur := some (scFork isAnd (lowerExpr left le before).1 le (lowerExpr left le before).2).1.1 }
  | ifThen {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {loop : Option LoopCtx} {condition : Expr} {yes : Core.Block} {no : Option Core.Block} {origin : OriginId}
      (occurrence : GeneratedDemandOccurrence m function le root path (.statement loop (.ifS condition yes no origin)) before)
      (live : (lowerExpr condition le before).2.cur.isSome = true) :
      GeneratedDemandOccurrence m function le root (path ++ [1]) (.block loop [] false yes)
        { (fork (lowerExpr condition le before).1 le (lowerExpr condition le before).2).2 with
          cur := some (fork (lowerExpr condition le before).1 le (lowerExpr condition le before).2).1.1 }
  | ifElse {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {loop : Option LoopCtx} {condition : Expr} {yes no : Core.Block} {origin : OriginId}
      (occurrence : GeneratedDemandOccurrence m function le root path (.statement loop (.ifS condition yes (some no) origin)) before)
      (live : (lowerExpr condition le before).2.cur.isSome = true) :
      GeneratedDemandOccurrence m function le root (path ++ [2]) (.block loop [] false no)
        { (lowerBlock loop [] false yes le
            { (fork (lowerExpr condition le before).1 le (lowerExpr condition le before).2).2 with
              cur := some (fork (lowerExpr condition le before).1 le (lowerExpr condition le before).2).1.1 }).2 with
          cur := some (fork (lowerExpr condition le before).1 le (lowerExpr condition le before).2).1.2 }
  | index {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {view : View} {index : Expr} {origin : OriginId}
      (occurrence : GeneratedDemandOccurrence m function le root path (.place (.elem view index origin)) before) :
      GeneratedDemandOccurrence m function le root (path ++ [1]) (.expression index) (lowerView view le before).2
  | sliceLower {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {mutability : Mutability} {view : View} {low high : Bound} {origin : OriginId}
      (occurrence : GeneratedDemandOccurrence m function le root path
        (.expression (.slice mutability view low high origin)) before) :
      GeneratedDemandOccurrence m function le root (path ++ [1]) (.bound low) (lowerView view le before).2
  | sliceUpper {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {mutability : Mutability} {view : View} {low high : Bound} {origin : OriginId}
      (occurrence : GeneratedDemandOccurrence m function le root path
        (.expression (.slice mutability view low high origin)) before) :
      GeneratedDemandOccurrence m function le root (path ++ [2]) (.bound high)
        (lowerBound low le (lowerView view le before).2).2
  | pushValue {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {owner : Place} {value : Expr} {origin : Option OriginId}
      (occurrence : GeneratedDemandOccurrence m function le root path (.expression (.push owner value origin)) before) :
      GeneratedDemandOccurrence m function le root (path ++ [1]) (.expression value) (lowerPlace owner le before).2
  | argument {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {context : ContextId} {arguments : List Arg} {origin : OriginId} {index : Nat} {argument : Arg}
      (occurrence : GeneratedDemandOccurrence m function le root path (.expression (.call context arguments origin)) before)
      (argumentAt : arguments[index]? = some argument) :
      GeneratedDemandOccurrence m function le root (path ++ [index]) (.argument argument)
        (lowerArgs (arguments.take index) le before).2
  | argumentValue {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS} {expression : Expr}
      (occurrence : GeneratedDemandOccurrence m function le root path (.argument (.byVal expression)) before) :
      GeneratedDemandOccurrence m function le root path (.expression expression) before
  | argumentPlace {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {mutability : Mutability} {place : Place}
      (occurrence : GeneratedDemandOccurrence m function le root path (.argument (.byRef mutability place)) before) :
      GeneratedDemandOccurrence m function le root path (.place place) before
  | eachView {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS} {view : View}
      (occurrence : GeneratedDemandOccurrence m function le root path (.eachSource view) before) :
      GeneratedDemandOccurrence m function le root path (.view view) before
  | blockStatement {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {loop : Option LoopCtx} {parameters : List (SlotId × ValueId × OriginId)} {want : Bool} {block : Core.Block}
      {index : Nat} {statement : Stmt}
      (occurrence : GeneratedDemandOccurrence m function le root path (.block loop parameters want block) before)
      (statementAt : block.stmts[index]? = some statement) :
      GeneratedDemandOccurrence m function le root (path ++ [index]) (.statement loop statement)
        (lowerStmts loop (block.stmts.take index) le (demandBlockStatementsBefore le before parameters block)).2
  | blockValue {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {loop : Option LoopCtx} {parameters : List (SlotId × ValueId × OriginId)} {want : Bool}
      {block : Core.Block} {expression : Expr}
      (occurrence : GeneratedDemandOccurrence m function le root path (.block loop parameters want block) before)
      (valueAt : block.value = some expression) :
      GeneratedDemandOccurrence m function le root (path ++ [block.stmts.length]) (.expression expression)
        (lowerStmts loop block.stmts le (demandBlockStatementsBefore le before parameters block)).2
  | assignmentPlace {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {loop : Option LoopCtx} {place : Place} {value : Expr} {origin : OriginId}
      (occurrence : GeneratedDemandOccurrence m function le root path (.statement loop (.assign place value origin)) before) :
      GeneratedDemandOccurrence m function le root (path ++ [0]) (.place place) before
  | assignmentValue {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {loop : Option LoopCtx} {place : Place} {value : Expr} {origin : OriginId}
      (occurrence : GeneratedDemandOccurrence m function le root path (.statement loop (.assign place value origin)) before) :
      GeneratedDemandOccurrence m function le root (path ++ [1]) (.expression value) (lowerPlace place le before).2
  | clearPlace {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {loop : Option LoopCtx} {place : Place} {origin : OriginId}
      (occurrence : GeneratedDemandOccurrence m function le root path (.statement loop (.clear place origin)) before) :
      GeneratedDemandOccurrence m function le root (path ++ [0]) (.place place) before

theorem GeneratedDemandOccurrence.source {m : Core.Module} {function : Func} {le : LEnv}
    {root : DemandNode} {path : List Nat} {action : DemandLoweringAction} {before : LS}
    (occurrence : GeneratedDemandOccurrence m function le root path action before) :
    DemandNodeAt root path action.node := by
  induction occurrence with
  | functionRoot => exact .here _
  | globalRoot => exact .here _
  | first occurrence first induction => exact induction.snoc 0 first.source
  | whileCondition occurrence induction => exact induction.snoc 0 rfl
  | binaryRight occurrence induction => exact induction.snoc 1 rfl
  | comparisonRight occurrence induction => exact induction.snoc 1 rfl
  | @shortCircuitRight function le root path before isAnd left right occurrence live induction =>
    cases isAnd <;> exact induction.snoc 1 rfl
  | ifThen occurrence live induction => exact induction.snoc 1 rfl
  | ifElse occurrence live induction => exact induction.snoc 2 rfl
  | index occurrence induction => exact induction.snoc 1 rfl
  | sliceLower occurrence induction => exact induction.snoc 1 rfl
  | sliceUpper occurrence induction => exact induction.snoc 2 rfl
  | pushValue occurrence induction => exact induction.snoc 1 rfl
  | @argument function le root path before context arguments origin index argument occurrence argumentAt induction =>
    apply induction.snoc index
    simp only [DemandLoweringAction.node, DemandNode.child?, DemandNode.children, List.getElem?_map, argumentAt]
    cases argument <;> rfl
  | argumentValue occurrence induction => exact induction
  | argumentPlace occurrence induction => exact induction
  | eachView occurrence induction => exact induction
  | @blockStatement function le root path before loop parameters want block index statement occurrence statementAt induction =>
    apply induction.snoc index
    have bound : index < block.stmts.length := (List.getElem?_eq_some_iff.mp statementAt).1
    cases block
    simp only [Core.Block.stmts] at bound statementAt ⊢
    simp only [DemandLoweringAction.node, DemandNode.child?, DemandNode.children]
    rw [List.getElem?_append_left (by simpa using bound)]
    simp only [List.getElem?_map, statementAt, Option.map_some, Function.comp_apply, Option.join_some]
  | @blockValue function le root path before loop parameters want block expression occurrence valueAt induction =>
    apply induction.snoc block.stmts.length
    cases block
    simp only [Core.Block.stmts, Core.Block.value] at valueAt ⊢
    simp only [DemandLoweringAction.node, DemandNode.child?, DemandNode.children]
    rw [List.getElem?_append_right (by simp)]
    simp only [List.length_map, Nat.sub_self, List.getElem?_cons_zero, Option.join_some, valueAt, Option.map_some]
  | assignmentPlace occurrence induction => exact induction.snoc 0 rfl
  | assignmentValue occurrence induction => exact induction.snoc 1 rfl
  | clearPlace occurrence induction => exact induction.snoc 0 rfl

end Goose.Lower
