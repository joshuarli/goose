import Goose.Core.Demand
import Goose.Lower.Validation.ReplacementControl
import Goose.Lower.Validation.ReplacementEmissionMap
import Goose.Lower.GeneratedBuilder

set_option Elab.async false

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR

inductive Fragment
  | expression (syntaxExpr : Expr)
  | place (sourcePlace : Place)
  | view (sourceView : View)
  | bound (sourceBound : Bound)
  | statement (loop : Option LoopCtx) (sourceStatement : Stmt)
  | block (loop : Option LoopCtx) (bindings : List (SlotId × ValueId × OriginId))
      (want : Bool) (sourceBlock : Core.Block)

def Fragment.node : Fragment → DemandNode
  | .expression syntaxExpr => .expression syntaxExpr
  | .place sourcePlace => .place sourcePlace
  | .view sourceView => .view sourceView
  | .bound sourceBound => .bound sourceBound
  | .statement _ sourceStatement => .statement sourceStatement
  | .block _ _ _ sourceBlock => .block sourceBlock

def Fragment.finish (fragment : Fragment) (env : LEnv) (before : LS) : LS :=
  match fragment with
  | .expression syntaxExpr => (lowerExpr syntaxExpr env before).2
  | .place sourcePlace => (lowerPlace sourcePlace env before).2
  | .view sourceView => (lowerView sourceView env before).2
  | .bound sourceBound => (lowerBound sourceBound env before).2
  | .statement loop sourceStatement => (lowerStmt loop sourceStatement env before).2
  | .block loop bindings want sourceBlock => (lowerBlock loop bindings want sourceBlock env before).2

abbrev Child := Option (Fragment × LS)

def expressionChildren (env : LEnv) : List Expr → LS → List Child
  | [], _ => []
  | syntaxExpr :: rest, before =>
      some (.expression syntaxExpr,before) ::
        expressionChildren env rest (lowerExpr syntaxExpr env before).2

def argumentChildren (env : LEnv) : List Arg → LS → List Child
  | [], _ => []
  | argument :: rest, before =>
      some ((match argument with
        | .byVal syntaxExpr => .expression syntaxExpr
        | .byRef _ sourcePlace => .place sourcePlace),before) ::
        argumentChildren env rest (lowerArg argument env before).2

def statementChildren (env : LEnv) (loop : Option LoopCtx) : List Stmt → LS → List Child
  | [], _ => []
  | sourceStatement :: rest, before =>
      if before.cur.isSome then
        some (.statement loop sourceStatement,before) ::
          statementChildren env loop rest (lowerStmt loop sourceStatement env before).2
      else none :: statementChildren env loop rest before

def printChildren (env : LEnv) : List PrintArg → LS → List Child
  | [], _ => []
  | .text _ :: rest, before => none :: printChildren env rest before
  | .expr syntaxExpr :: rest, before =>
      some (.expression syntaxExpr,before) ::
        printChildren env rest (lowerExpr syntaxExpr env before).2

def branchChildren (env : LEnv) (before : LS) (condition : ValueId)
    (loop : Option LoopCtx) (want : Bool) (yes : Core.Block) (no : Option Core.Block) : List Child :=
  if before.cur.isSome then
    let split := fork condition env before
    let yesBefore := (setCur (some split.1.1) env split.2).2
    let yesAfter := (lowerBlock loop [] want yes env yesBefore).2
    let noBefore := (setCur (some split.1.2) env yesAfter).2
    [some (.block loop [] want yes,yesBefore),no.map fun body => (.block loop [] want body,noBefore)]
  else [none,none]

def shortCircuitChild (env : LEnv) (before : LS) (isAnd : Bool) (left : ValueId)
    (right : Expr) : Child :=
  if before.cur.isSome then
    let split := scFork isAnd left env before
    some (.expression right,(setCur (some split.1.1) env split.2).2)
  else none

def whileChildren (env : LEnv) (before : LS) (condition : Expr) (body : Core.Block) : List Child :=
  let header := newBlock [] env before
  let jumped := (emitTerm (.br header.1.1 []) env header.2).2
  let conditionBefore := (setCur (some header.1.1) env jumped).2
  let tested := lowerExpr condition env conditionBefore
  let bodyChild := if tested.2.cur.isSome then
    let split := fork tested.1 env tested.2
    let bodyBefore := (setCur (some split.1.1) env split.2).2
    some (.block (some ⟨tested.2.stack.length,split.1.2,.jump header.1.1⟩) [] false body,bodyBefore)
    else none
  [some (.expression condition,conditionBefore),bodyChild]

def rangeChild (env : LEnv) (before : LS) (varId : VarId) (low high : ValueId)
    (body : Core.Block) (origin : OriginId) : Child :=
  if before.cur.isSome then
    let type := (intTyOf low env before).1
    let header := newBlock [.data (.int type)] env before
    let counter := header.1.2.headD 0
    let jumped := (emitTerm (.br header.1.1 [low]) env header.2).2
    let headerBefore := (setCur (some header.1.1) env jumped).2
    let tested := emitDef (.cmp .lt type counter high) env headerBefore
    let split := fork tested.1 env tested.2
    let bodyBefore := (setCur (some split.1.1) env split.2).2
    some (.block (some ⟨tested.2.stack.length,split.1.2,.next header.1.1 type counter⟩)
      [(varId,counter,origin)] false body,bodyBefore)
  else none

def eachChild (env : LEnv) (before : LS) (varId : VarId) (index : Option VarId)
    (sourceView : View) (byRef : Bool) (body : Core.Block) (origin : OriginId) : Child :=
  let source := lowerEachSource sourceView env before
  let regrow := regrowOf source.1.1 env source.2
  let sampled := eachSampled regrow.1 source.1.2 env regrow.2
  let start := emitDef (.constInt .i64 0) env sampled.2
  if start.2.cur.isSome then
    let header := newBlock [.data (.int .i64)] env start.2
    let counter := header.1.2.headD 0
    let jumped := (emitTerm (.br header.1.1 [start.1]) env header.2).2
    let headerBefore := (setCur (some header.1.1) env jumped).2
    let length := eachLen regrow.1 source.1.1 sampled.1 env headerBefore
    let tested := emitDef (.cmp .lt .i64 counter length.1) env length.2
    let split := fork tested.1 env tested.2
    let elementBefore := (setCur (some split.1.1) env split.2).2
    let element := emitDef (.refElem source.1.2 counter) env elementBefore
    let value := eachElemValue varId byRef element.1 env element.2
    let bindings := (varId,value.1,origin) :: (index.toList.map fun i => (i,counter,origin))
    some (.block (some ⟨tested.2.stack.length,split.1.2,.next header.1.1 .i64 counter⟩)
      bindings false body,value.2)
  else none

def Fragment.children (fragment : Fragment) (env : LEnv) (before : LS) : List Child :=
  match fragment with
  | .expression syntaxExpr => match syntaxExpr with
    | .lit .. | .bool _ => []
    | .read sourcePlace | .ref _ sourcePlace | .pop sourcePlace _ => [some (.place sourcePlace,before)]
    | .slice _ sourceView low high _ =>
      let viewed := lowerView sourceView env before
      let loweredLow := lowerBound low env viewed.2
      [some (.view sourceView,before),some (.bound low,viewed.2),some (.bound high,loweredLow.2)]
    | .len sourceView => [some (.view sourceView,before)]
    | .un _ value _ | .not value | .conv _ _ value _ | .fill _ value =>
      [some (.expression value,before)]
    | .bin _ left right _ | .cmp _ left right =>
      [some (.expression left,before),some (.expression right,(lowerExpr left env before).2)]
    | .and left right =>
      let lowered := lowerExpr left env before
      [some (.expression left,before),shortCircuitChild env lowered.2 true lowered.1 right]
    | .or left right =>
      let lowered := lowerExpr left env before
      [some (.expression left,before),shortCircuitChild env lowered.2 false lowered.1 right]
    | .call _ arguments _ => argumentChildren env arguments before
    | .push sourcePlace value _ =>
      [some (.place sourcePlace,before),some (.expression value,(lowerPlace sourcePlace env before).2)]
    | .ifE condition yes no =>
      let tested := lowerExpr condition env before
      some (.expression condition,before) :: branchChildren env tested.2 tested.1 none true yes (some no)
    | .blockE sourceBlock => [some (.block none [] true sourceBlock,before)]
    | .arrLit _ expressions | .structLit _ expressions => expressionChildren env expressions before
  | .place sourcePlace => match sourcePlace with
    | .var _ | .global _ => []
    | .deref syntaxExpr => [some (.expression syntaxExpr,before)]
    | .field owner _ => [some (.place owner,before)]
    | .elem sourceView index _ =>
      [some (.view sourceView,before),some (.expression index,(lowerView sourceView env before).2)]
  | .view sourceView => match sourceView with
    | .of sourcePlace => [some (.place sourcePlace,before)]
    | .val syntaxExpr => [some (.expression syntaxExpr,before)]
  | .bound sourceBound => match sourceBound with
    | .omitted => []
    | .expr syntaxExpr | .fromEnd syntaxExpr => [some (.expression syntaxExpr,before)]
  | .statement loop sourceStatement => match sourceStatement with
    | .letS _ value _ | .rebind _ value _ | .expr value _ | .assertS value _ | .exit value _ =>
      [some (.expression value,before)]
    | .assign sourcePlace value _ | .popN sourcePlace value _ =>
      [some (.place sourcePlace,before),some (.expression value,(lowerPlace sourcePlace env before).2)]
    | .assignOp _ sourcePlace value _ =>
      let addressed := lowerPlace sourcePlace env before
      [some (.place sourcePlace,before),some (.expression value,(emitDef (.load addressed.1) env addressed.2).2)]
    | .assignWhole sourcePlace value origin =>
      let addressed := lowerPlace sourcePlace env before
      [some (.place sourcePlace,before),some (.expression value,(emitEffect (.clear addressed.1 (some origin)) env addressed.2).2)]
    | .append sourcePlace sourceView _ =>
      [some (.place sourcePlace,before),some (.view sourceView,(lowerPlace sourcePlace env before).2)]
    | .resize sourcePlace size fill _ =>
      let addressed := lowerPlace sourcePlace env before
      let counted := lowerExpr size env addressed.2
      [some (.place sourcePlace,before),some (.expression size,addressed.2),fill.map fun syntaxExpr => (.expression syntaxExpr,counted.2)]
    | .clear sourcePlace _ => [some (.place sourcePlace,before)]
    | .ifS condition yes no _ =>
      let tested := lowerExpr condition env before
      some (.expression condition,before) :: branchChildren env tested.2 tested.1 loop false yes no
    | .while condition body _ => whileChildren env before condition body
    | .forRange varId low high body origin =>
      let first := lowerExpr low env before
      let second := lowerExpr high env first.2
      [some (.expression low,before),some (.expression high,first.2),rangeChild env second.2 varId first.1 second.1 body origin]
    | .forEach varId index sourceView byRef body origin =>
      [some (.view sourceView,before),eachChild env before varId index sourceView byRef body origin]
    | .ret value _ => [value.map fun syntaxExpr => (.expression syntaxExpr,before)]
    | .brk _ | .cont _ | .abort .. => []
    | .print arguments _ => printChildren env arguments before
  | .block loop bindings want (.mk scope statements value) =>
    let entered := (emitEffect (.enter scope) env before).2
    let enteredScope :=  (pushScope scope env entered).2
    let initialized := (initSlots bindings env enteredScope).2
    let stated := (lowerStmts loop statements env initialized).2
    statementChildren env loop statements initialized ++ [value.map fun syntaxExpr => (.expression syntaxExpr,stated)]

def Fragment.child? (fragment : Fragment) (env : LEnv) (before : LS) (index : Nat) : Child :=
  (fragment.children env before)[index]?.join

def Fragment.at? (fragment : Fragment) (env : LEnv) (before : LS) : List Nat → Child
  | [] => some (fragment,before)
  | index :: path => do
      let (child,start) ← fragment.child? env before index
      child.at? env start path

def SourceLoweringAt (root : Fragment) (env : LEnv) (initial : LS) (path : List Nat)
    (fragment : Fragment) (before : LS) : Prop := root.at? env initial path = some (fragment,before)

theorem SourceLoweringAt.here (root : Fragment) (env : LEnv) (initial : LS) :
    SourceLoweringAt root env initial [] root initial := rfl

theorem SourceLoweringAt.child {root fragment child : Fragment} {env : LEnv} {initial before start : LS}
    {path : List Nat} {index : Nat}
    (parent : SourceLoweringAt root env initial path fragment before)
    (row : fragment.child? env before index = some (child,start)) :
    SourceLoweringAt root env initial (path ++ [index]) child start := by
  induction path generalizing root initial with
  | nil =>
    obtain ⟨rfl,rfl⟩ := Option.some.inj parent
    simpa [SourceLoweringAt,Fragment.at?,row]
  | cons first rest ih =>
    simp only [SourceLoweringAt,List.cons_append,Fragment.at?] at parent ⊢
    cases found : root.child? env initial first with
    | none => simp [found] at parent
    | some entry =>
      obtain ⟨next,middle⟩ := entry
      simp only [found,Option.bind_some] at parent ⊢
      exact ih parent

def ChildMatches : Child → Option DemandNode → Prop
  | none, _ => True
  | some (fragment,_), node => node = some fragment.node

@[simp] theorem ChildMatches.none (node : Option DemandNode) : ChildMatches none node := trivial

@[simp] theorem ChildMatches.some (fragment : Fragment) (before : LS) (node : Option DemandNode) :
    ChildMatches (some (fragment,before)) node ↔ node = some fragment.node := Iff.rfl

@[simp] theorem ChildMatches.option_expression (expression : Option Expr) (before : LS) :
    ChildMatches (expression.map fun e => (.expression e,before))
      (expression.map DemandNode.expression) := by
  cases expression <;> trivial

def ChildrenMatch : List Child → List (Option DemandNode) → Prop
  | [], [] => True
  | actual :: actuals, node :: nodes => ChildMatches actual node ∧ ChildrenMatch actuals nodes
  | _, _ => False

@[simp] theorem ChildrenMatch.append {left right : List Child} {nodes more : List (Option DemandNode)}
    (first : ChildrenMatch left nodes) (second : ChildrenMatch right more) :
    ChildrenMatch (left ++ right) (nodes ++ more) := by
  induction left generalizing nodes with
  | nil => cases nodes <;> simp_all [ChildrenMatch]
  | cons head tail ih =>
    cases nodes with
    | nil => simp [ChildrenMatch] at first
    | cons node nodes => exact ⟨first.1,ih first.2⟩

private theorem expressionChildren_sources (env : LEnv) (expressions : List Expr) (before : LS) :
    ChildrenMatch (expressionChildren env expressions before)
      (expressions.map (some ∘ DemandNode.expression)) := by
  induction expressions generalizing before with
  | nil => trivial
  | cons expression rest ih => exact ⟨rfl,ih _⟩

private theorem argumentChildren_sources (env : LEnv) (arguments : List Arg) (before : LS) :
    ChildrenMatch (argumentChildren env arguments before) (arguments.map fun
      | .byVal expression => some (.expression expression)
      | .byRef _ place => some (.place place)) := by
  induction arguments generalizing before with
  | nil => trivial
  | cons argument rest ih => cases argument <;> exact ⟨rfl,ih _⟩

private theorem statementChildren_sources (env : LEnv) (loop : Option LoopCtx)
    (statements : List Stmt) (before : LS) :
    ChildrenMatch (statementChildren env loop statements before)
      (statements.map (some ∘ DemandNode.statement)) := by
  induction statements generalizing before with
  | nil => trivial
  | cons statement rest ih =>
    simp only [statementChildren]
    split <;> exact ⟨by trivial,ih _⟩

private theorem printChildren_sources (env : LEnv) (arguments : List PrintArg) (before : LS) :
    ChildrenMatch (printChildren env arguments before) (arguments.map fun
      | .text _ => none
      | .expr expression => some (.expression expression)) := by
  induction arguments generalizing before with
  | nil => trivial
  | cons argument rest ih => cases argument <;> exact ⟨by trivial,ih _⟩

@[simp] theorem shortCircuitChild_sources (env : LEnv) (before : LS) (isAnd : Bool)
    (left : ValueId) (right : Expr) :
    ChildMatches (shortCircuitChild env before isAnd left right) (some (.expression right)) := by
  unfold shortCircuitChild
  split <;> trivial

@[simp] theorem branchChildren_sources (env : LEnv) (before : LS) (condition : ValueId)
    (loop : Option LoopCtx) (want : Bool) (yes : Core.Block) (no : Option Core.Block) :
    ChildrenMatch (branchChildren env before condition loop want yes no)
      [some (.block yes),no.map DemandNode.block] := by
  unfold branchChildren
  split <;> cases no <;> trivial

@[simp] theorem whileChildren_sources (env : LEnv) (before : LS) (condition : Expr) (body : Core.Block) :
    ChildrenMatch (whileChildren env before condition body) [some (.expression condition),some (.block body)] := by
  unfold whileChildren
  dsimp only
  constructor
  · rfl
  · unfold ChildrenMatch
    constructor
    · split <;> trivial
    · trivial

@[simp] theorem rangeChild_sources (env : LEnv) (before : LS) (variableId : VarId) (low high : ValueId)
    (body : Core.Block) (origin : OriginId) :
    ChildMatches (rangeChild env before variableId low high body origin) (some (.block body)) := by
  unfold rangeChild
  split <;> trivial

@[simp] theorem eachChild_sources (env : LEnv) (before : LS) (variableId : VarId) (index : Option VarId)
    (view : View) (byRef : Bool) (body : Core.Block) (origin : OriginId) :
    ChildMatches (eachChild env before variableId index view byRef body origin) (some (.block body)) := by
  unfold eachChild
  dsimp only
  split <;> trivial

theorem Fragment.children_sources (fragment : Fragment) (env : LEnv) (before : LS) :
    ChildrenMatch (fragment.children env before) fragment.node.children := by
  cases fragment with
  | expression expression =>
    cases expression <;>
      simp [Fragment.children,Fragment.node,DemandNode.children,ChildrenMatch]
    all_goals first
      | exact argumentChildren_sources _ _ _
      | exact expressionChildren_sources _ _ _
      | exact shortCircuitChild_sources _ _ _ _ _
      | exact branchChildren_sources _ _ _ _ _ _ (some _)
  | place place =>
    cases place <;> simp [Fragment.children,Fragment.node,DemandNode.children,ChildrenMatch]
  | view view =>
    cases view <;> simp [Fragment.children,Fragment.node,DemandNode.children,ChildrenMatch]
  | bound bound =>
    cases bound <;> simp [Fragment.children,Fragment.node,DemandNode.children,ChildrenMatch]
  | statement loop statement =>
    cases statement <;>
      simp [Fragment.children,Fragment.node,DemandNode.children,ChildrenMatch]
    all_goals first
      | exact printChildren_sources _ _ _
      | exact whileChildren_sources _ _ _ _
      | exact rangeChild_sources _ _ _ _ _ _ _
      | exact eachChild_sources _ _ _ _ _ _ _ _
      | exact branchChildren_sources _ _ _ _ _ _ _
      | exact ChildMatches.option_expression _ _
  | block loop bindings want block =>
    cases block with
    | mk scope statements value =>
      apply ChildrenMatch.append
      · exact statementChildren_sources _ _ _ _
      · cases value <;> trivial

theorem ChildrenMatch.row {actual : List Child} {nodes : List (Option DemandNode)}
    (aligned : ChildrenMatch actual nodes) {index : Nat} {fragment : Fragment} {before : LS}
    (row : actual[index]? = some (some (fragment,before))) :
    nodes[index]? = some (some fragment.node) := by
  induction actual generalizing nodes index with
  | nil => simp at row
  | cons head tail ih =>
    cases nodes with
    | nil => simp [ChildrenMatch] at aligned
    | cons node nodes =>
      cases index with
      | zero =>
        simp only [List.getElem?_cons_zero,Option.some.injEq] at row
        subst head
        exact congrArg some aligned.1
      | succ index => exact ih aligned.2 row

theorem Fragment.child_source {fragment child : Fragment} {env : LEnv} {before start : LS}
    {index : Nat} (row : fragment.child? env before index = some (child,start)) :
    fragment.node.child? index = some child.node := by
  have actual : (fragment.children env before)[index]? = some (some (child,start)) := by
    cases found : (fragment.children env before)[index]? <;> simp_all [Fragment.child?]
  exact (show fragment.node.children[index]?.join = some child.node from
    by rw [(fragment.children_sources env before).row actual]; rfl)

#print axioms SourceLoweringAt.child
#print axioms Fragment.child_source

end Goose.Lower.Validation.SourceReplacementWriterLedger
