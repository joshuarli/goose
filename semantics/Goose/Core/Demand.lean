import Std.Data.HashMap
import Goose.Core.Json
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

def Arg.sliceHolderVariables (access : AccessEnv) : Arg → List VarId
  | .byRef _ p =>
    match access.placeType? p with
    | some (.slice _ _) => p.variables
    | _ => []
  | .byVal _ => []

inductive AliasSource
  | variable (id : VarId)
  | operand (path : List Nat)
  | iteration (scope : Nat)
  deriving DecidableEq, Repr

/-- A reference or sampled run kept until a consuming evaluation completes. -/
structure RetainedAlias where
  ty : Ty
  roots : List RootRef
  source : AliasSource
  deriving DecidableEq, Repr

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
  deriving DecidableEq, Hashable, Repr

private structure DemandKey where
  path : List Nat
  phase : DemandPhase
  deriving DecidableEq, Repr

private instance : BEq DemandKey where
  beq a b := decide (a = b)

private instance : LawfulBEq DemandKey where
  rfl := by intro a; simp [BEq.beq]
  eq_of_beq := by intro a b h; exact of_decide_eq_true h

private instance : Hashable DemandKey where
  hash key := hash (key.path, key.phase)

private instance : LawfulHashable DemandKey where
  hash_eq a b h := by
    have hab := eq_of_beq h
    subst b
    rfl

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
  deriving DecidableEq, Repr

private def DemandPoint.key (point : DemandPoint) : DemandKey := ⟨point.path, point.phase⟩

/- The index retains the first point for each path and phase. `covers` ensures
  every source occurrence resolves to its full point, so key collisions with
  different demand facts are rejected while repeated equal facts are safe. -/
private structure DemandPathIndex (points : List DemandPoint) where
  entries : Std.HashMap DemandKey DemandPoint
  covers : ∀ {point}, point ∈ points → entries[point.key]? = some point
  lookupValid : ∀ {key point}, entries[key]? = some point → point ∈ points ∧ point.key = key

private def DemandPathIndex.empty : DemandPathIndex [] :=
  ⟨{}, by intro point h; simp at h, by intro key point h; simp at h⟩

private def DemandPathIndex.prepend (point : DemandPoint) {rest : List DemandPoint}
    (old : DemandPathIndex rest) : V (DemandPathIndex (point :: rest)) := do
  match hlookup : old.entries[point.key]? with
  | none =>
    let entries := old.entries.insert point.key point
    pure ⟨entries, by
      intro candidate hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · simp [entries, DemandPoint.key]
      · have hcover := old.covers hmem
        have hne : point.key ≠ candidate.key := by
          intro heq
          have : old.entries[point.key]? = some candidate := by
            change old.entries[candidate.key]? = some candidate at hcover
            change old.entries[point.key]? = some candidate
            rw [heq]
            exact hcover
          rw [hlookup] at this
          contradiction
        rw [Std.HashMap.getElem?_insert]
        have hbeq : (point.key == candidate.key) = false :=
          Bool.eq_false_iff.mpr (by simpa using hne)
        rw [hbeq]
        simpa using hcover
    , by
      intro key candidate hvalue
      by_cases heq : key = point.key
      · subst key
        have hinsert : entries[point.key]? = some point := by
          simp [entries, DemandPoint.key]
        rw [hinsert] at hvalue
        injection hvalue with hcandidate
        subst candidate
        exact ⟨List.mem_cons_self, rfl⟩
      · rw [Std.HashMap.getElem?_insert] at hvalue
        have hbeq : (point.key == key) = false :=
          Bool.eq_false_iff.mpr (by
            intro h
            exact heq (eq_of_beq h).symm)
        rw [hbeq] at hvalue
        obtain ⟨hmem, hkey⟩ := old.lookupValid hvalue
        exact ⟨List.mem_cons_of_mem _ hmem, hkey⟩
    ⟩
  | some previous =>
    if hsame : previous = point then
      pure ⟨old.entries, by
        intro candidate hmem
        simp only [List.mem_cons] at hmem
        rcases hmem with rfl | hmem
        · simpa [hsame] using hlookup
        · exact old.covers hmem
      , by
        intro key candidate hvalue
        obtain ⟨hmem, hkey⟩ := old.lookupValid hvalue
        exact ⟨List.mem_cons_of_mem _ hmem, hkey⟩
      ⟩
    else reject .shrink "demand plan has conflicting points at one path and phase"

private def DemandPathIndex.build : (points : List DemandPoint) → V (DemandPathIndex points)
  | [] => pure DemandPathIndex.empty
  | point :: rest => do
    let old ← DemandPathIndex.build rest
    DemandPathIndex.prepend point old

private def DemandPathIndex.verifyPoint {points : List DemandPoint}
    (index : DemandPathIndex points) (point : DemandPoint) : V (PLift (point ∈ points)) := do
  match hlookup : index.entries[point.key]? with
  | none => reject .shrink s!"demand approval has no point at path {point.path} phase {repr point.phase}"
  | some indexedPoint =>
    let ⟨hmem, hkey⟩ := index.lookupValid hlookup
    if hsame : indexedPoint = point then
      pure ⟨by simpa [hsame] using hmem⟩
    else reject .shrink s!"demand approval metadata differs at path {point.path} phase {repr point.phase}"

private theorem DemandPathIndex.unique {points : List DemandPoint}
    (index : DemandPathIndex points) :
    ∀ a b, a ∈ points → b ∈ points → a.key = b.key → a = b := by
  intro a b ha hb hkey
  have ha' := index.covers ha
  have hb' := index.covers hb
  rw [hkey] at ha'
  rw [ha'] at hb'
  cases hb'
  rfl

private theorem DemandPathIndex.uniquePathPhase {points : List DemandPoint}
    (index : DemandPathIndex points) :
    ∀ a b, a ∈ points → b ∈ points → a.path = b.path → a.phase = b.phase → a = b := by
  intro a b ha hb hpath hphase
  apply index.unique a b ha hb
  cases a
  cases b
  simp_all [DemandPoint.key]

/-- The first point at a syntax path and evaluation phase in a derived plan. -/
def DemandPoint.lookup? (plan : Array DemandPoint) (path : List Nat)
    (phase : DemandPhase) : Option DemandPoint :=
  plan.toList.find? fun point => point.path == path && point.phase == phase

private theorem DemandPoint.lookupList_of_mem_unique (points : List DemandPoint)
    (point : DemandPoint)
    (unique : ∀ a b, a ∈ points → b ∈ points → a.path = b.path → a.phase = b.phase → a = b)
    (mem : point ∈ points) :
    points.find? (fun candidate => candidate.path == point.path &&
      candidate.phase == point.phase) = some point := by
  revert point unique mem
  cases points with
  | nil =>
    intro point unique mem
    simp at mem
  | cons head tail =>
    intro point unique mem
    simp only [List.mem_cons] at mem
    by_cases hmatches : head.path == point.path && head.phase == point.phase
    · have hkeys : head.path = point.path ∧ head.phase = point.phase := by
        simpa only [Bool.and_eq_true, beq_iff_eq] using hmatches
      have heq : head = point := unique head point (by simp) (by simp [mem]) hkeys.1 hkeys.2
      subst head
      simp
    · have uniqueTail : ∀ a b, a ∈ tail → b ∈ tail →
          a.path = b.path → a.phase = b.phase → a = b := by
        intro a b ha hb hpath hphase
        exact unique a b (by simp [ha]) (by simp [hb]) hpath hphase
      rcases mem with rfl | mem
      · simp at hmatches
      · simp [hmatches, DemandPoint.lookupList_of_mem_unique tail point uniqueTail mem]

/-- The source syntax node covered by a demand focus. -/
inductive DemandNode
  | expression (node : Expr)
  | place (node : Place)
  | view (node : View)
  | bound (node : Bound)
  | statement (node : Stmt)
  | block (node : Block)

def DemandNode.variables : DemandNode → List VarId
  | .expression node => node.variables
  | .place node => node.variables
  | .view node => node.variables
  | .bound node => node.variables
  | .statement node => node.variables
  | .block node => node.variables

structure DemandFrame where
  active : List VarId
  future : List VarId
  retained : List RetainedAlias
  deriving DecidableEq, Repr

structure DemandOwner where
  ty : Option Ty
  roots : List RootRef
  deriving DecidableEq, Repr

structure DemandWholeCheck where
  forbidden : DemandOwner
  checkedRoots : List RootRef

structure DemandExpectedPoint where
  path : List Nat
  node : DemandNode
  phase : DemandPhase
  frame : DemandFrame
  shrinkOwners : List DemandOwner := []
  wholeChecks : List DemandWholeCheck := []

def DemandNode.directShrinkPlace? : DemandNode → Option Place
  | .expression (.pop p _) => some p
  | .statement s => match s with
    | .popN p _ _ | .resize p _ _ _ | .clear p _ | .assignWhole p _ _ => some p
    | _ => none
  | _ => none

def DemandNode.isDirectShrink (node : DemandNode) : Bool :=
  node.directShrinkPlace?.isSome

def DemandNode.callInfo? : DemandNode → Option (ContextId × List Arg)
  | .expression (.call context args _) => some (context, args)
  | _ => none

def DemandExpectedPoint.toPoint (expected : DemandExpectedPoint) : DemandPoint :=
  ⟨expected.path, expected.phase, expected.frame.active, expected.frame.future,
    expected.frame.retained⟩

private structure DemandExpectedIndex (expected : List DemandExpectedPoint) where
  entries : Std.HashMap DemandKey DemandExpectedPoint
  lookupValid : ∀ {key occurrence}, entries[key]? = some occurrence →
    occurrence ∈ expected ∧ occurrence.toPoint.key = key

private def DemandExpectedIndex.empty : DemandExpectedIndex [] :=
  ⟨{}, by intro key occurrence h; simp at h⟩

private def DemandExpectedIndex.prepend (occurrence : DemandExpectedPoint)
    {rest : List DemandExpectedPoint} (old : DemandExpectedIndex rest) :
    V (DemandExpectedIndex (occurrence :: rest)) := do
  let key := occurrence.toPoint.key
  match hlookup : old.entries[key]? with
  | none =>
    let entries := old.entries.insert key occurrence
    pure ⟨entries, by
      intro lookupKey candidate hvalue
      by_cases heq : lookupKey = key
      · subst lookupKey
        have hinsert : entries[key]? = some occurrence := by
          simp [entries]
        rw [hinsert] at hvalue
        injection hvalue with hcandidate
        subst candidate
        exact ⟨List.mem_cons_self, rfl⟩
      · rw [Std.HashMap.getElem?_insert] at hvalue
        have hbeq : (key == lookupKey) = false := Bool.eq_false_iff.mpr (by
          intro h
          exact heq (eq_of_beq h).symm)
        rw [hbeq] at hvalue
        obtain ⟨hmem, hkey⟩ := old.lookupValid hvalue
        exact ⟨List.mem_cons_of_mem _ hmem, hkey⟩⟩
  | some previous =>
    if hsame : previous.toPoint = occurrence.toPoint then
      pure ⟨old.entries, by
        intro lookupKey candidate hvalue
        obtain ⟨hmem, hkey⟩ := old.lookupValid hvalue
        exact ⟨List.mem_cons_of_mem _ hmem, hkey⟩⟩
    else reject .shrink "demand coverage has conflicting expected points at one path and phase"

private def DemandExpectedIndex.build :
    (expected : List DemandExpectedPoint) → V (DemandExpectedIndex expected)
  | [] => pure DemandExpectedIndex.empty
  | occurrence :: rest => do
    let old ← DemandExpectedIndex.build rest
    DemandExpectedIndex.prepend occurrence old

/-- Child positions use the same indices as the demand traversal. `none` keeps
an omitted optional child or a text-only print argument at its source index. -/
def DemandNode.children : DemandNode → List (Option DemandNode)
  | .expression e =>
    match e with
    | .lit .. | .bool _ => []
    | .read p | .ref _ p | .pop p _ => [some (.place p)]
    | .slice _ v lo hi _ => [some (.view v), some (.bound lo), some (.bound hi)]
    | .len v => [some (.view v)]
    | .un _ e _ | .not e | .conv _ _ e _ | .fill _ e => [some (.expression e)]
    | .bin _ a b _ | .cmp _ a b | .and a b | .or a b =>
      [some (.expression a), some (.expression b)]
    | .call _ args _ => args.map fun
      | .byVal e => some (.expression e)
      | .byRef _ p => some (.place p)
    | .push p e _ => [some (.place p), some (.expression e)]
    | .ifE c t f => [some (.expression c), some (.block t), some (.block f)]
    | .blockE b => [some (.block b)]
    | .arrLit _ es | .structLit _ es => es.map (some ∘ DemandNode.expression)
  | .place p =>
    match p with
    | .var _ | .global _ => []
    | .deref e => [some (.expression e)]
    | .elem v i _ => [some (.view v), some (.expression i)]
    | .field p _ => [some (.place p)]
  | .view v =>
    match v with
    | .of p => [some (.place p)]
    | .val e => [some (.expression e)]
  | .bound b =>
    match b with
    | .expr e | .fromEnd e => [some (.expression e)]
    | .omitted => []
  | .statement s =>
    match s with
    | .letS _ e _ | .rebind _ e _ | .expr e _ | .assertS e _ | .exit e _ =>
      [some (.expression e)]
    | .assign p e _ | .assignOp _ p e _ | .assignWhole p e _ =>
      [some (.place p), some (.expression e)]
    | .append p v _ => [some (.place p), some (.view v)]
    | .popN p e _ => [some (.place p), some (.expression e)]
    | .resize p size fill _ => [some (.place p), some (.expression size), fill.map (.expression)]
    | .clear p _ => [some (.place p)]
    | .ifS c t f _ => [some (.expression c), some (.block t), f.map (.block)]
    | .while c b _ => [some (.expression c), some (.block b)]
    | .forRange _ lo hi b _ => [some (.expression lo), some (.expression hi), some (.block b)]
    | .forEach _ _ v _ b _ => [some (.view v), some (.block b)]
    | .ret e _ => [e.map (.expression)]
    | .brk _ | .cont _ | .abort .. => []
    | .print args _ => args.map fun
      | .text _ => none
      | .expr e => some (.expression e)
  | .block (.mk _ statements value) =>
    statements.map (some ∘ DemandNode.statement) ++ [value.map (.expression)]

def DemandNode.child? (node : DemandNode) (index : Nat) : Option DemandNode :=
  ((node.children[index]?).join)

def DemandNode.visibleForChild (node : DemandNode) (visible : List VarId)
    (index : Nat) : List VarId :=
  match node with
  | .block (.mk _ statements _) =>
    (statements.take index).foldl (fun active statement =>
      match statement with
      | .letS x _ _ => if active.contains x then active else x :: active
      | _ => active) visible
  | .statement (.forRange x _ _ _ _) =>
    if index == 2 && !visible.contains x then x :: visible else visible
  | .statement (.forEach x idx _ _ _ _) =>
    if index == 1 then (x :: idx.toList).foldl
      (fun active binder => if active.contains binder then active else binder :: active) visible
    else visible
  | _ => visible

/-- Successful statement evaluation adds a `let` binder to lexical visibility. -/
def DemandNode.visibleAfter (node : DemandNode) (visible : List VarId) : List VarId :=
  match node with
  | .statement (.letS binder _ _) =>
    if visible.contains binder then visible else binder :: visible
  | _ => visible

def DemandNode.visibleAt? (node : DemandNode) (visible : List VarId) :
    List Nat → Option (DemandNode × List VarId)
  | [] => some (node, visible)
  | index :: path => do
    let child ← node.child? index
    child.visibleAt? (node.visibleForChild visible index) path
termination_by path => path.length

structure DemandChildExpectation where
  active : List VarId
  future : List VarId

/-- Future variables required after evaluating a direct child; `none` marks an absent child. -/
def DemandNode.childFuture (node : DemandNode) (access : AccessEnv) (parent : DemandPoint)
    (index : Nat) : Option (List VarId) :=
  let later (variables : List VarId) := variables ++ parent.future
  match node with
  | .expression e =>
    match e with
    | .slice _ _ lo hi _ =>
      if index == 0 then some (later (lo.variables ++ hi.variables))
      else if index == 1 then some (later hi.variables)
      else if index == 2 then some parent.future else none
    | .bin _ _ right _ | .cmp _ _ right | .and _ right | .or _ right =>
      if index == 0 then some (later right.variables)
      else if index == 1 then some parent.future else none
    | .call _ args _ =>
      if index < args.length then
        let holders := (args.take (index + 1)).flatMap (Arg.sliceHolderVariables access)
        some (later (holders ++ (args.drop (index + 1)).flatMap Arg.variables))
      else none
    | .push _ value _ =>
      if index == 0 then some (later value.variables)
      else if index == 1 then some parent.future else none
    | .ifE _condition yes no =>
      if index == 0 then some (later (yes.variables ++ no.variables))
      else if index == 1 || index == 2 then some parent.future else none
    | .arrLit _ expressions | .structLit _ expressions =>
      if index < expressions.length then
        some (later ((expressions.drop (index + 1)).flatMap Expr.variables))
      else none
    | .read _ | .ref _ _ | .pop _ _ | .len _ | .un _ _ _ | .not _ |
      .conv _ _ _ _ | .fill _ _ | .blockE _ =>
        if index < node.children.length then some parent.future else none
    | .lit .. | .bool _ => none
  | .place p =>
    match p with
    | .elem _ indexExpr _ =>
      if index == 0 then some (later indexExpr.variables)
      else if index == 1 then some parent.future else none
    | .deref _ | .field _ _ =>
      if index == 0 then some parent.future else none
    | .var _ | .global _ => none
  | .view v =>
    match v with
    | .of _ | .val _ => if index == 0 then some parent.future else none
  | .bound b =>
    match b with
    | .expr _ | .fromEnd _ => if index == 0 then some parent.future else none
    | .omitted => none
  | .statement s =>
    match s with
    | .assign _ value _ | .assignOp _ _ value _ | .assignWhole _ value _ =>
      if index == 0 then some (later value.variables)
      else if index == 1 then some parent.future else none
    | .append _ v _ =>
      if index == 0 then some (later v.variables)
      else if index == 1 then some parent.future else none
    | .popN _ count _ =>
      if index == 0 then some (later count.variables)
      else if index == 1 then some parent.future else none
    | .resize _ size fill _ =>
      let fillVars := fill.toList.flatMap Expr.variables
      if index == 0 then some (later (size.variables ++ fillVars))
      else if index == 1 then some (later fillVars)
      else if index == 2 && fill.isSome then some parent.future else none
    | .ifS _condition yes no _ =>
      let noVars := no.toList.flatMap Block.variables
      if index == 0 then some (later (yes.variables ++ noVars))
      else if index == 1 || (index == 2 && no.isSome) then some parent.future else none
    | .while condition body _ =>
      let backedge := parent.active.filter (condition.variables ++ body.variables).contains
      if index == 0 || index == 1 then some (later backedge) else none
    | .forRange _x _lo hi body _ =>
      let backedge := parent.active.filter body.variables.contains
      if index == 0 then some (later (hi.variables ++ body.variables))
      else if index == 1 then some (later body.variables)
      else if index == 2 then some (later backedge) else none
    | .forEach _ _ _v _ body _ =>
      let backedge := parent.active.filter body.variables.contains
      if index == 0 then some (later body.variables)
      else if index == 1 then some (later backedge) else none
    | .letS _ _ _ | .rebind _ _ _ | .expr _ _ | .assertS _ _ | .exit _ _ |
      .ret (some _) _ =>
      if index == 0 then some parent.future else none
    | .ret none _ => none
    | .clear _ _ => if index == 0 then some parent.future else none
    | .print args _ =>
      if index < args.length then
        some (later ((args.drop (index + 1)).flatMap PrintArg.variables))
      else none
    | .brk _ | .cont _ | .abort .. => none
  | .block (.mk _ statements value) =>
    if index < statements.length then
      let laterStatements := (statements.drop (index + 1)).flatMap Stmt.variables
      let valueVars := value.toList.flatMap Expr.variables
      some (later (laterStatements ++ valueVars))
    else if index == statements.length && value.isSome then some parent.future
    else none

private def callFutureRegressionArgs : List Arg :=
  [ .byRef .mutable (.var 2)
  , .byVal (.read (.var 3))
  , .byRef .mutable (.var 4) ]

private def callFutureRegressionNode : DemandNode :=
  .expression (.call 0 callFutureRegressionArgs 0)

private def callFutureRegressionAccess : AccessEnv :=
  let impl : Impl := {
    name := "call-future"
    params := #[]
    results := #[]
    vars := #[
      ⟨"unused0", .unit, .mutable, 0, 0⟩,
      ⟨"unused1", .unit, .mutable, 0, 0⟩,
      ⟨"slice", .slice .mutable .bool, .mutable, 0, 0⟩,
      ⟨"scalar", .int .i64, .mutable, 0, 0⟩,
      ⟨"reference", .ref .mutable (.int .i64), .mutable, 0, 0⟩]
    body := .mk 0 [] none
    summary := .unknown }
  let ctx : Context := ⟨0, "call-future", [], [], []⟩
  let mod : Module := {
    files := #[]
    types := #[]
    globals := #[]
    impls := #[impl]
    contexts := #[ctx]
    entry := 0
    origins := #[] }
  ⟨mod, impl, ctx⟩

#guard callFutureRegressionNode.childFuture callFutureRegressionAccess
  ⟨[], .expression, [], [9], []⟩ 0 == some [2, 3, 4, 9]
#guard callFutureRegressionNode.childFuture callFutureRegressionAccess
  ⟨[], .expression, [], [9], []⟩ 1 == some [2, 4, 9]
#guard callFutureRegressionNode.childFuture callFutureRegressionAccess
  ⟨[], .expression, [], [9], []⟩ 2 == some [2, 9]
#guard Arg.sliceHolderVariables callFutureRegressionAccess (.byRef .mutable (.var 2)) == [2]
#guard Arg.sliceHolderVariables callFutureRegressionAccess
  (.byRef .mutable (.deref (.read (.var 4)))) == []

/-- The expected child frame shape; list fields are consumed extensionally. -/
def DemandNode.childExpectation? (node : DemandNode) (access : AccessEnv) (parent : DemandPoint)
    (index : Nat) : Option DemandChildExpectation := do
  let _ ← node.child? index
  let future ← node.childFuture access parent index
  pure ⟨node.visibleForChild parent.active index, future⟩

def DemandPoint.sameFrameMembership (a b : DemandPoint) : Prop :=
  (∀ x, x ∈ a.active ↔ x ∈ b.active) ∧
    (∀ x, x ∈ a.future ↔ x ∈ b.future) ∧
    (∀ alias, alias ∈ a.retained ↔ alias ∈ b.retained)

/-- A child-path witness into one source syntax tree. -/
inductive DemandNodeAt : DemandNode → List Nat → DemandNode → Prop
  | here (node : DemandNode) : DemandNodeAt node [] node
  | child {parent child node index path}
      (hchild : parent.child? index = some child)
      (hpath : DemandNodeAt child path node) :
      DemandNodeAt parent (index :: path) node

theorem DemandNodeAt.snoc {root parent path} {child : DemandNode}
    (hsource : DemandNodeAt root path parent) (index : Nat)
    (hnext : parent.child? index = some child) :
    DemandNodeAt root (path ++ [index]) child := by
  induction hsource with
  | here node =>
    simpa using (DemandNodeAt.child hnext (DemandNodeAt.here child))
  | @child parent middle node firstIndex path hfirst hpath ih =>
    simpa [List.cons_append] using (DemandNodeAt.child hfirst (ih hnext))

private structure DemandWorkItem (root : DemandNode) where
  path : List Nat
  node : DemandNode
  frame : DemandFrame
  forbidden : List DemandOwner := []
  source : DemandNodeAt root path node

/-- Context plans start at implementation bodies; later plan entries start at
global initializers, matching `deriveModuleDemand`'s owner order. -/
def demandRoot? (m : Module) (owner : Nat) : Option DemandNode :=
  if owner < m.contexts.size then
    (m.contexts[owner]?).bind fun ctx =>
      (m.impls[ctx.impl]?).map fun impl => .block impl.body
  else
    (m.globals[owner - m.contexts.size]?).map fun global => .expression global.init

def demandInitialVisible? (m : Module) (owner : Nat) : Option (List VarId) :=
  if owner < m.contexts.size then
    (m.contexts[owner]?).bind fun ctx =>
      (m.impls[ctx.impl]?).map fun impl => impl.params.toList.map (·.var)
  else
    (m.globals[owner - m.contexts.size]?).map fun _ => []

def demandVisibleAt? (m : Module) (owner : Nat) (path : List Nat) : Option (List VarId) := do
  let root ← demandRoot? m owner
  let visible ← demandInitialVisible? m owner
  let (_, visible) ← root.visibleAt? visible path
  some visible

/-- The typing-visible bindings at one owner-relative source path. -/
def DemandVisibleAt (m : Module) (owner : Nat) (path : List Nat)
    (visible : List VarId) : Prop :=
  demandVisibleAt? m owner path = some visible

def DemandSourceAt (m : Module) (owner : Nat) (path : List Nat)
    (node : DemandNode) : Prop :=
  ∃ root, demandRoot? m owner = some root ∧ DemandNodeAt root path node

theorem DemandSourceAt.child {m owner path parent index child}
    (hsource : DemandSourceAt m owner path parent)
    (hchild : parent.child? index = some child) :
    DemandSourceAt m owner (path ++ [index]) child := by
  rcases hsource with ⟨root, hroot, hnode⟩
  exact ⟨root, hroot, hnode.snoc index hchild⟩

def DemandNode.phaseMatches (node : DemandNode) (phase : DemandPhase) : Bool :=
  match node with
  | .expression e =>
    phase == .expression || match e with
      | .call .. => phase == .call || phase == .mutation
      | .pop .. => phase == .mutation
      | _ => false
  | .place _ => phase == .place
  | .view _ => phase == .view
  | .bound _ => phase == .bound
  | .statement s =>
    phase == .statement || match s with
      | .popN .. | .resize .. | .clear .. | .assignWhole .. => phase == .mutation
      | _ => false
  | .block _ => phase == .block

def DemandNodeHasPhase (node : DemandNode) (phase : DemandPhase) : Prop :=
  node.phaseMatches phase = true

/-- The phase used for child traversal before a node's auxiliary checks. -/
def DemandNode.primaryPhase : DemandNode → DemandPhase
  | .expression _ => .expression
  | .place _ => .place
  | .view _ => .view
  | .bound _ => .bound
  | .statement _ => .statement
  | .block _ => .block

private structure DemandCursor (root : DemandNode) where
  path : List Nat
  node : DemandNode
  sourceProof : DemandNodeAt root path node

private def DemandCursor.child? {root} (cursor : DemandCursor root)
    (index : Nat) : Option (DemandCursor root) :=
  match hchild : cursor.node.child? index with
  | none => none
  | some child =>
    some ⟨cursor.path ++ [index], child, cursor.sourceProof.snoc index hchild⟩

private structure DemandTrace (root : DemandNode) where
  point : DemandPoint
  cursor : DemandCursor root
  pathMatches : point.path = cursor.path
  hasPhase : DemandNodeHasPhase cursor.node point.phase

private def DemandTrace.sourceAt (m : Module) (owner : Nat)
    (trace : DemandTrace root) : Prop :=
  demandRoot? m owner = some root ∧
    DemandNodeAt root trace.point.path trace.cursor.node

private theorem DemandTrace.sourceAt_of_root (m : Module) (owner : Nat)
    (trace : DemandTrace root) (hroot : demandRoot? m owner = some root) :
    trace.sourceAt m owner := by
  refine ⟨hroot, ?_⟩
  simpa [trace.pathMatches] using trace.cursor.sourceProof

def DemandPathPhaseUnique (plan : Array DemandPoint) : Prop :=
  ∀ a b, a ∈ plan.toList → b ∈ plan.toList → a.path = b.path → a.phase = b.phase → a = b

private structure DemandSetup where
  root : DemandNode
  access : AccessEnv
  initial : DemandFrame

/-- Lexical bindings present before an owner's root is traversed. -/
def demandInitialActive (m : Module) (owner : Nat) : List VarId :=
  if owner < m.contexts.size then
    match m.contexts[owner]? with
    | none => []
    | some ctx =>
      match m.impls[ctx.impl]? with
      | none => []
      | some impl => impl.params.toList.map (·.var)
  else []

private def demandSetup? (m : Module) (owner : Nat) : Option DemandSetup := do
  if owner < m.contexts.size then
    let ctx ← m.contexts[owner]?
    let impl ← m.impls[ctx.impl]?
    pure ⟨.block impl.body, ⟨m, impl, ctx⟩,
      ⟨demandInitialActive m owner, [], []⟩⟩
  else
    let global ← m.globals[owner - m.contexts.size]?
    pure ⟨.expression global.init, ⟨m, initImpl, initContext⟩, ⟨[], [], []⟩⟩

def demandAccess? (m : Module) (owner : Nat) : Option AccessEnv :=
  (demandSetup? m owner).map DemandSetup.access

structure DemandEnv (m : Module) (planOwner : Nat) (root : DemandNode) where
  access : AccessEnv
  accessMatches : demandAccess? m planOwner = some access
  cursor : DemandCursor root
  active : List VarId
  future : List VarId
  retained : List RetainedAlias
  forbidden : List DemandOwner := []

def DemandPoint.fromEnv {m : Module} {planOwner : Nat} {root}
    (env : DemandEnv m planOwner root) (path : List Nat)
    (phase : DemandPhase) : DemandPoint :=
  ⟨path, phase, env.active, env.future, env.retained⟩

@[simp] theorem DemandPoint.fromEnv_active {m : Module} {planOwner : Nat} {root}
    (env : DemandEnv m planOwner root) (path : List Nat)
    (phase : DemandPhase) : (DemandPoint.fromEnv env path phase).active = env.active := rfl

@[simp] theorem DemandPoint.fromEnv_future {m : Module} {planOwner : Nat} {root}
    (env : DemandEnv m planOwner root) (path : List Nat)
    (phase : DemandPhase) : (DemandPoint.fromEnv env path phase).future = env.future := rfl

@[simp] theorem DemandPoint.fromEnv_retained {m : Module} {planOwner : Nat} {root}
    (env : DemandEnv m planOwner root) (path : List Nat)
    (phase : DemandPhase) : (DemandPoint.fromEnv env path phase).retained = env.retained := rfl

def DemandPoint.ActiveMatches (point : DemandPoint) (visible : List VarId) : Prop :=
  ∀ x, x ∈ point.active ↔ x ∈ visible

theorem DemandPoint.activeMatches_fromEnv {m : Module} {planOwner : Nat} {root}
    (env : DemandEnv m planOwner root) (path : List Nat)
    (phase : DemandPhase) (visible : List VarId)
    (hactive : ∀ x, x ∈ env.active ↔ x ∈ visible) :
    (DemandPoint.fromEnv env path phase).ActiveMatches visible := by
  intro x
  exact hactive x

def DemandEnv.withFuture {m : Module} {planOwner : Nat} {root}
    (env : DemandEnv m planOwner root) (variables : List VarId) : DemandEnv m planOwner root :=
  { env with future := variables ++ env.future }

def DemandEnv.withActive {m : Module} {planOwner : Nat} {root}
    (env : DemandEnv m planOwner root) (active : List VarId) : DemandEnv m planOwner root :=
  { env with active }

theorem DemandPoint.activeMatches_withFuture {m : Module} {planOwner : Nat} {root}
    (env : DemandEnv m planOwner root) (path : List Nat)
    (phase : DemandPhase) (variables visible : List VarId)
    (hactive : ∀ x, x ∈ env.active ↔ x ∈ visible) :
    (DemandPoint.fromEnv (env.withFuture variables) path phase).ActiveMatches visible := by
  intro x
  change x ∈ env.active ↔ x ∈ visible
  exact hactive x

def DemandEnv.withAliases {m : Module} {planOwner : Nat} {root}
    (env : DemandEnv m planOwner root)
    (aliases : List RetainedAlias) : DemandEnv m planOwner root :=
  { env with retained := aliases ++ env.retained }

def DemandEnv.activeBackedge {m : Module} {planOwner : Nat} {root}
    (env : DemandEnv m planOwner root) (variables : List VarId) : List VarId :=
  variables.filter env.active.contains

@[simp] theorem DemandEnv.withFuture_future {m : Module} {planOwner : Nat} {root}
    (env : DemandEnv m planOwner root) (variables : List VarId) :
    (env.withFuture variables).future = variables ++ env.future := rfl

@[simp] theorem DemandEnv.withFuture_active {m : Module} {planOwner : Nat} {root}
    (env : DemandEnv m planOwner root) (variables : List VarId) :
    (env.withFuture variables).active = env.active := rfl

@[simp] theorem DemandEnv.withFuture_retained {m : Module} {planOwner : Nat} {root}
    (env : DemandEnv m planOwner root) (variables : List VarId) :
    (env.withFuture variables).retained = env.retained := rfl

@[simp] theorem DemandEnv.withActive_active {m : Module} {planOwner : Nat} {root}
    (env : DemandEnv m planOwner root) (active : List VarId) :
    (env.withActive active).active = active := rfl

@[simp] theorem DemandEnv.withActive_future {m : Module} {planOwner : Nat} {root}
    (env : DemandEnv m planOwner root) (active : List VarId) :
    (env.withActive active).future = env.future := rfl

@[simp] theorem DemandEnv.withActive_retained {m : Module} {planOwner : Nat} {root}
    (env : DemandEnv m planOwner root) (active : List VarId) :
    (env.withActive active).retained = env.retained := rfl

@[simp] theorem DemandEnv.withAliases_retained {m : Module} {planOwner : Nat} {root}
    (env : DemandEnv m planOwner root)
    (aliases : List RetainedAlias) :
    (env.withAliases aliases).retained = aliases ++ env.retained := rfl

@[simp] theorem DemandEnv.withAliases_future {m : Module} {planOwner : Nat} {root}
    (env : DemandEnv m planOwner root)
    (aliases : List RetainedAlias) :
    (env.withAliases aliases).future = env.future := rfl

theorem DemandEnv.withFuture_append_future {m : Module} {planOwner : Nat} {root}
    (env : DemandEnv m planOwner root)
    (first later : List VarId) :
    (env.withFuture (first ++ later)).future = first ++ later ++ env.future := by
  simp [List.append_assoc]

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

def DemandOwner.compatible (_owner : DemandOwner) (alias : RetainedAlias) : Bool :=
  alias.ty.interiorTarget?.isSome

def DemandOwner.conflicts (owner : DemandOwner) (alias : RetainedAlias) : Bool :=
  owner.invalidates && owner.compatible alias &&
    owner.roots.any (fun target => alias.roots.any (rootsMayOverlap target))

def DemandPointShrinkSafe (access : AccessEnv) (point : DemandPoint)
    (owner : DemandOwner) : Prop :=
  (∀ x, x ∈ point.future → x ∈ point.active → ∀ alias,
    access.aliasVariable x = .ok (some alias) → owner.conflicts alias = false) ∧
  (∀ alias, alias ∈ point.retained → owner.conflicts alias = false)

def DemandRootsDisjoint (forbiddenRoots checkedRoots : List RootRef) : Prop :=
  ∀ forbiddenRoot, forbiddenRoot ∈ forbiddenRoots → ∀ checkedRoot,
    checkedRoot ∈ checkedRoots → rootsMayOverlap forbiddenRoot checkedRoot = false

private structure DemandShrinkEvent (m : Module) (planOwner : Nat) (root : DemandNode) where
  trace : DemandTrace root
  mutationPhase : trace.point.phase = .mutation
  access : AccessEnv
  accessMatches : demandAccess? m planOwner = some access
  owner : DemandOwner
  safe : DemandPointShrinkSafe access trace.point owner

private structure DemandWholeRootsEvent (root : DemandNode) where
  trace : DemandTrace root
  forbidden : DemandOwner
  checkedRoots : List RootRef
  disjoint : DemandRootsDisjoint forbidden.roots checkedRoots

private structure DemandFoundShrinkOwner {root : DemandNode}
    {m : Module} {planOwner : Nat}
    (events : List (DemandShrinkEvent m planOwner root)) (occurrence : DemandExpectedPoint)
    (owner : DemandOwner) where
  event : DemandShrinkEvent m planOwner root
  member : event ∈ events
  pathMatches : event.trace.point.path = occurrence.path
  ownerMatches : event.owner = owner
  mutationPhase : event.trace.point.phase = .mutation

private def DemandShrinkEvent.findOwner {m : Module} {planOwner : Nat} {root}
    (occurrence : DemandExpectedPoint)
    (owner : DemandOwner) :
    (events : List (DemandShrinkEvent m planOwner root)) →
      V (DemandFoundShrinkOwner (m := m) (planOwner := planOwner) events occurrence owner)
  | [] => reject .shrink s!"demand plan has no shrink approval at {occurrence.path}"
  | event :: rest => do
    if hpath : event.trace.point.path = occurrence.path then
      if howner : event.owner = owner then
        pure ⟨event, by simp, hpath, howner, event.mutationPhase⟩
      else
        let found ← DemandShrinkEvent.findOwner occurrence owner rest
        pure ⟨found.event, by simp [found.member], found.pathMatches,
          found.ownerMatches, found.mutationPhase⟩
    else
      let found ← DemandShrinkEvent.findOwner occurrence owner rest
      pure ⟨found.event, by simp [found.member], found.pathMatches,
        found.ownerMatches, found.mutationPhase⟩
termination_by events => events.length

private def DemandShrinkEvent.verifyOwnersAt {root}
    {m : Module} {planOwner : Nat}
    (events : List (DemandShrinkEvent m planOwner root)) (occurrence : DemandExpectedPoint) :
    (owners : List DemandOwner) →
      V (PLift (∀ owner, owner ∈ owners →
        ∃ event, event ∈ events ∧ event.trace.point.path = occurrence.path ∧
          event.owner = owner ∧ event.trace.point.phase = .mutation))
  | [] => pure ⟨by intro owner howner; simp at howner⟩
  | owner :: rest => do
    let found ← DemandShrinkEvent.findOwner occurrence owner events
    let restCovered ← DemandShrinkEvent.verifyOwnersAt events occurrence rest
    pure ⟨by
      intro candidate hmember
      simp only [List.mem_cons] at hmember
      rcases hmember with heq | htail
      · cases heq
        exact ⟨found.event, found.member, found.pathMatches, found.ownerMatches,
          found.mutationPhase⟩
      · exact restCovered.down candidate htail⟩
termination_by owners => owners.length

private def DemandExpectedPoint.verifyShrinkRequests {root}
    {m : Module} {planOwner : Nat}
    (events : List (DemandShrinkEvent m planOwner root)) :
    (expected : List DemandExpectedPoint) →
      V (PLift (∀ occurrence, occurrence ∈ expected → occurrence.phase = .mutation → ∀ owner,
        owner ∈ occurrence.shrinkOwners →
          ∃ event, event ∈ events ∧ event.trace.point.path = occurrence.path ∧
            event.owner = owner ∧ event.trace.point.phase = .mutation))
  | [] => pure ⟨by intro occurrence hmember; simp at hmember⟩
  | occurrence :: rest => do
    let here ← DemandShrinkEvent.verifyOwnersAt events occurrence occurrence.shrinkOwners
    let later ← DemandExpectedPoint.verifyShrinkRequests events rest
    pure ⟨by
      intro candidate hmember hphase owner howner
      simp only [List.mem_cons] at hmember
      rcases hmember with heq | htail
      · cases heq
        exact here.down owner howner
      · exact later.down candidate htail hphase owner howner⟩
termination_by expected => expected.length

private structure DemandFoundWholeRequest {root : DemandNode}
    (events : List (DemandWholeRootsEvent root)) (occurrence : DemandExpectedPoint)
    (request : DemandWholeCheck) where
  event : DemandWholeRootsEvent root
  member : event ∈ events
  pathMatches : event.trace.point.path = occurrence.path
  phaseMatches : event.trace.point.phase = occurrence.phase
  forbiddenMatches : event.forbidden = request.forbidden
  rootsMatch : event.checkedRoots = request.checkedRoots

private def DemandWholeRootsEvent.findRequest {root} (occurrence : DemandExpectedPoint)
    (request : DemandWholeCheck) :
    (events : List (DemandWholeRootsEvent root)) →
      V (DemandFoundWholeRequest events occurrence request)
  | [] => reject .whole s!"demand plan has no whole-root check at {occurrence.path}"
  | event :: rest => do
    if hpath : event.trace.point.path = occurrence.path then
      if hphase : event.trace.point.phase = occurrence.phase then
        if hforbidden : event.forbidden = request.forbidden then
          if hroots : event.checkedRoots = request.checkedRoots then
            pure ⟨event, by simp, hpath, hphase, hforbidden, hroots⟩
          else
            let found ← DemandWholeRootsEvent.findRequest occurrence request rest
            pure ⟨found.event, by simp [found.member], found.pathMatches,
              found.phaseMatches, found.forbiddenMatches, found.rootsMatch⟩
        else
          let found ← DemandWholeRootsEvent.findRequest occurrence request rest
          pure ⟨found.event, by simp [found.member], found.pathMatches,
            found.phaseMatches, found.forbiddenMatches, found.rootsMatch⟩
      else
        let found ← DemandWholeRootsEvent.findRequest occurrence request rest
        pure ⟨found.event, by simp [found.member], found.pathMatches,
          found.phaseMatches, found.forbiddenMatches, found.rootsMatch⟩
    else
      let found ← DemandWholeRootsEvent.findRequest occurrence request rest
      pure ⟨found.event, by simp [found.member], found.pathMatches,
        found.phaseMatches, found.forbiddenMatches, found.rootsMatch⟩
termination_by events => events.length

private def DemandWholeRootsEvent.verifyRequestsAt {root}
    (events : List (DemandWholeRootsEvent root)) (occurrence : DemandExpectedPoint) :
    (requests : List DemandWholeCheck) →
      V (PLift (∀ request, request ∈ requests →
        ∃ event, event ∈ events ∧ event.trace.point.path = occurrence.path ∧
          event.trace.point.phase = occurrence.phase ∧ event.forbidden = request.forbidden ∧
            event.checkedRoots = request.checkedRoots))
  | [] => pure ⟨by intro request hrequest; simp at hrequest⟩
  | request :: rest => do
    let found ← DemandWholeRootsEvent.findRequest occurrence request events
    let restCovered ← DemandWholeRootsEvent.verifyRequestsAt events occurrence rest
    pure ⟨by
      intro candidate hmember
      simp only [List.mem_cons] at hmember
      rcases hmember with heq | htail
      · cases heq
        exact ⟨found.event, found.member, found.pathMatches, found.phaseMatches,
          found.forbiddenMatches, found.rootsMatch⟩
      · exact restCovered.down candidate htail⟩
termination_by requests => requests.length

private def DemandExpectedPoint.verifyWholeRequests {root}
    (events : List (DemandWholeRootsEvent root)) :
    (expected : List DemandExpectedPoint) →
      V (PLift (∀ occurrence, occurrence ∈ expected → ∀ request,
        request ∈ occurrence.wholeChecks →
          ∃ event, event ∈ events ∧ event.trace.point.path = occurrence.path ∧
            event.trace.point.phase = occurrence.phase ∧
              event.forbidden = request.forbidden ∧
                event.checkedRoots = request.checkedRoots))
  | [] => pure ⟨by intro occurrence hmember; simp at hmember⟩
  | occurrence :: rest => do
    let here ← DemandWholeRootsEvent.verifyRequestsAt events occurrence occurrence.wholeChecks
    let later ← DemandExpectedPoint.verifyWholeRequests events rest
    pure ⟨by
      intro candidate hmember request hrequest
      simp only [List.mem_cons] at hmember
      rcases hmember with heq | htail
      · cases heq
        exact here.down request hrequest
      · exact later.down candidate htail request hrequest⟩
termination_by expected => expected.length

private structure DemandState (m : Module) (planOwner : Nat) (root : DemandNode) where
  traces : Array (DemandTrace root)
  shrinkEvents : Array (DemandShrinkEvent m planOwner root) := #[]
  wholeRootsEvents : Array (DemandWholeRootsEvent root) := #[]

private def DemandPathIndex.verifyShrinkEvents {points : List DemandPoint}
    (index : DemandPathIndex points) (m : Module) (planOwner : Nat) (root : DemandNode) :
    (events : List (DemandShrinkEvent m planOwner root)) →
      V (PLift (∀ event, event ∈ events → event.trace.point ∈ points))
  | [] => pure ⟨by intro event hmem; simp at hmem⟩
  | event :: rest => do
    let hpoint ← index.verifyPoint event.trace.point
    let hrest ← index.verifyShrinkEvents m planOwner root rest
    pure ⟨by
      intro candidate hmem
      have hmem' := List.mem_cons.mp hmem
      rcases hmem' with hevent | htail
      · cases hevent
        exact hpoint.down
      · exact hrest.down candidate htail⟩
termination_by events => events.length

private def DemandPathIndex.verifyWholeRootsEvents {points : List DemandPoint}
    (index : DemandPathIndex points) (root : DemandNode) :
    (events : List (DemandWholeRootsEvent root)) →
      V (PLift (∀ event, event ∈ events → event.trace.point ∈ points))
  | [] => pure ⟨by intro event hmem; simp at hmem⟩
  | event :: rest => do
    let hpoint ← index.verifyPoint event.trace.point
    let hrest ← index.verifyWholeRootsEvents root rest
    pure ⟨by
      intro candidate hmem
      have hmem' := List.mem_cons.mp hmem
      rcases hmem' with hevent | htail
      · cases hevent
        exact hpoint.down
      · exact hrest.down candidate htail⟩
termination_by events => events.length

abbrev DemandCheck (m : Module) (planOwner : Nat) (root : DemandNode) :=
  StateT (DemandState m planOwner root) V

def demandReject {m : Module} {planOwner : Nat} {root}
    (rule : Rule) (message : String) : DemandCheck m planOwner root α :=
  throw ⟨rule, message⟩

def demandLift {m : Module} {planOwner : Nat} {root} (check : V α) : DemandCheck m planOwner root α :=
  fun state => do
  let value ← check
  pure (value, state)

private def recordShrinkEvent {m : Module} {planOwner : Nat} {root}
    (trace : DemandTrace root) (access : AccessEnv)
    (accessMatches : demandAccess? m planOwner = some access)
    (owner : DemandOwner) (mutationPhase : trace.point.phase = .mutation)
    (safe : DemandPointShrinkSafe access trace.point owner) :
    DemandCheck m planOwner root Unit :=
  let event : DemandShrinkEvent m planOwner root :=
    ⟨trace, mutationPhase, access, accessMatches, owner, safe⟩
  modify fun state => { state with shrinkEvents := state.shrinkEvents.push event }

private def recordWholeRootsEvent {m : Module} {planOwner : Nat} {root}
    (trace : DemandTrace root) (forbidden : DemandOwner)
    (checkedRoots : List RootRef) (disjoint : DemandRootsDisjoint forbidden.roots checkedRoots) :
    DemandCheck m planOwner root Unit :=
  modify fun state =>
    { state with wholeRootsEvents := state.wholeRootsEvents.push ⟨trace, forbidden, checkedRoots, disjoint⟩ }

def AccessEnv.aliasExpr (env : AccessEnv) (path : List Nat) (e : Expr) : V (List RetainedAlias) := do
  let some t := env.exprType? e | reject .type "retained expression has no checked type"
  if t.interiorTarget?.isSome then pure [⟨t, ← env.exprRoots e, .operand path⟩]
  else pure []

def AccessEnv.aliasPlace (env : AccessEnv) (path : List Nat) (p : Place) : V (List RetainedAlias) := do
  let some t := env.placeType? p | reject .type "retained place has no checked type"
  let rt := Ty.ref .mutable t
  if rt.interiorTarget?.isSome || t.ownerElem?.isSome then
    pure [⟨rt, ← env.placeRoots p, .operand path⟩]
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

private def AccessEnv.aliasesOfArgsFrom (env : AccessEnv) (path : List Nat)
    (index : Nat) : List Arg → V (List RetainedAlias)
  | [] => .ok []
  | arg :: rest =>
    match env.aliasArg (path ++ [index]) arg with
    | .error err => .error err
    | .ok aliases =>
      match env.aliasesOfArgsFrom path (index + 1) rest with
      | .error err => .error err
      | .ok later => .ok (aliases ++ later)

private theorem except_map_ok_extract {α β : Type} {f : α → β} {result : β}
    {value : V α} (h : f <$> value = .ok result) :
    ∃ item, value = .ok item ∧ f item = result := by
  cases value with
  | error err =>
    change Except.error err = .ok result at h
    cases h
  | ok item =>
    change Except.ok (f item) = .ok result at h
    cases h
    exact ⟨item, rfl, rfl⟩

private def AccessEnv.aliasesOfArgs (env : AccessEnv) (path : List Nat)
    (args : List Arg) : V (List RetainedAlias) :=
  env.aliasesOfArgsFrom path 0 args

private theorem AccessEnv.aliasesOfArgsFrom_index
    (env : AccessEnv) (path : List Nat) (start : Nat) (args : List Arg)
    {collected : List RetainedAlias} (hcollected : env.aliasesOfArgsFrom path start args = .ok collected)
    (index : Nat) (arg : Arg) (hindex : index < args.length)
    (harg : args[index]? = some arg) :
    ∃ aliases, env.aliasArg (path ++ [start + index]) arg = .ok aliases ∧
      ∀ alias, alias ∈ aliases → alias ∈ collected := by
  induction args generalizing start index collected with
  | nil => simp at hindex
  | cons first rest ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at harg
      subst arg
      cases hfirst : env.aliasArg (path ++ [start]) first with
      | error err => simp [AccessEnv.aliasesOfArgsFrom, hfirst] at hcollected
      | ok current =>
        cases hlater : env.aliasesOfArgsFrom path (start + 1) rest with
        | error err => simp [AccessEnv.aliasesOfArgsFrom, hfirst, hlater] at hcollected
        | ok later =>
          have hresult : current ++ later = collected := by
            simpa [AccessEnv.aliasesOfArgsFrom, hfirst, hlater] using hcollected
          refine ⟨current, ?_, ?_⟩
          · rfl
          · intro alias hmem
            rw [← hresult]
            exact List.mem_append_left _ hmem
    | succ index =>
      have hindex' : index < rest.length := by
        simp only [List.length_cons, Nat.succ_lt_succ_iff] at hindex
        exact hindex
      have harg' : rest[index]? = some arg := by simpa using harg
      cases hfirst : env.aliasArg (path ++ [start]) first with
      | error err => simp [AccessEnv.aliasesOfArgsFrom, hfirst] at hcollected
      | ok current =>
        cases hlater : env.aliasesOfArgsFrom path (start + 1) rest with
        | error err => simp [AccessEnv.aliasesOfArgsFrom, hfirst, hlater] at hcollected
        | ok later =>
          have hresult : current ++ later = collected := by
            simpa [AccessEnv.aliasesOfArgsFrom, hfirst, hlater] using hcollected
          obtain ⟨aliases, halias, hmem⟩ :=
            ih (start + 1) hlater index hindex' harg'
          have hpath : start + 1 + index = start + Nat.succ index := by omega
          refine ⟨aliases, ?_, ?_⟩
          · simpa only [hpath] using halias
          · intro alias hmemAlias
            rw [← hresult]
            exact List.mem_append_right _ (hmem alias hmemAlias)

private theorem AccessEnv.aliasesOfArgs_index
    (env : AccessEnv) (path : List Nat) (args : List Arg)
    {collected : List RetainedAlias} (hcollected : env.aliasesOfArgs path args = .ok collected)
    (index : Nat) (arg : Arg) (hindex : index < args.length)
    (harg : args[index]? = some arg) :
    ∃ aliases, env.aliasArg (path ++ [index]) arg = .ok aliases ∧
      ∀ alias, alias ∈ aliases → alias ∈ collected := by
  simpa [AccessEnv.aliasesOfArgs] using
    AccessEnv.aliasesOfArgsFrom_index env path 0 args hcollected index arg hindex harg

private def AccessEnv.aliasesOfExprs (env : AccessEnv) (path : List Nat)
    (expressions : List Expr) : V (List RetainedAlias) := do
  let mut aliases := []
  for (expression, index) in expressions.zipIdx do
    aliases := aliases ++ (← env.aliasExpr (path ++ [index]) expression)
  pure aliases

def DemandNode.retainedForChild (node : DemandNode) (access : AccessEnv)
    (path : List Nat) (index : Nat) : V (List RetainedAlias) := do
  let aliases ← match node with
    | .expression e =>
      match e with
      | .slice _ v _ _ _ =>
        if index == 1 || index == 2 then access.aliasView (path ++ [0]) v else pure []
      | .bin _ left _ _ | .cmp _ left _ | .and left _ | .or left _ =>
        if index == 1 then access.aliasExpr (path ++ [0]) left else pure []
      | .call _ args _ => access.aliasesOfArgs path (args.take index)
      | .push p _ _ =>
        if index == 1 then access.aliasPlace (path ++ [0]) p else pure []
      | .arrLit _ expressions | .structLit _ expressions =>
        access.aliasesOfExprs path (expressions.take index)
      | _ => pure []
    | .place (.elem v _ _) =>
      if index == 1 then access.aliasView (path ++ [0]) v else pure []
    | .statement s =>
      match s with
      | .assign p _ _ | .assignOp _ p _ _ | .assignWhole p _ _ |
        .append p _ _ | .popN p _ _ | .resize p _ _ _ =>
        if index == 1 || (index == 2 && (match s with | .resize .. => true | _ => false)) then
          access.aliasPlace (path ++ [0]) p
        else pure []
      | .forEach _ _ v _ _ _ =>
        if index != 1 then pure [] else
          match v with
          | .of p =>
            match access.placeType? p with
            | some ty =>
              if ty.ownerElem?.isSome then access.aliasPlace (path ++ [0]) p
              else access.aliasView (path ++ [0]) v
            | none => access.aliasView (path ++ [0]) v
          | .val _ => access.aliasView (path ++ [0]) v
      | _ => pure []
    | _ => pure []
  pure aliases

def DemandNode.childFrame (node : DemandNode) (access : AccessEnv)
    (path : List Nat) (frame : DemandFrame) (index : Nat) : V DemandFrame := do
  let parent : DemandPoint := ⟨path, .expression, frame.active, frame.future, frame.retained⟩
  let some expectation := node.childExpectation? access parent index
    | reject .block "demand traversal reached a missing child"
  let aliases ← node.retainedForChild access path index
  pure ⟨expectation.active, expectation.future, aliases ++ frame.retained⟩

theorem DemandNode.childFrame_newAlias {node : DemandNode} {access : AccessEnv}
    {path : List Nat} {frame : DemandFrame} {index : Nat} {result : DemandFrame}
    {aliases : List RetainedAlias} {alias : RetainedAlias}
    (hframe : node.childFrame access path frame index = .ok result)
    (haliases : node.retainedForChild access path index = .ok aliases)
    (hmem : alias ∈ aliases) : alias ∈ result.retained := by
  unfold DemandNode.childFrame at hframe
  let parent : DemandPoint := ⟨path, .expression, frame.active, frame.future, frame.retained⟩
  cases hchild : node.childExpectation? access parent index with
  | none => simp [parent, hchild, reject] at hframe
  | some expectation =>
    rw [haliases] at hframe
    simp [parent, hchild] at hframe
    cases hframe
    exact List.mem_append_left _ hmem

/-- Arguments evaluated before a call child keep their aliases live in that child's frame. -/
theorem DemandNode.call_child_retains_argument
    {access : AccessEnv} {path : List Nat} {frame childFrame : DemandFrame}
    {context origin index j : Nat} {args : List Arg} {arg : Arg}
    (hchild : (DemandNode.expression (.call context args origin)).childFrame
      access path frame index = .ok childFrame)
    (hji : j < index) (harg : args[j]? = some arg)
    {aliases : List RetainedAlias} {alias : RetainedAlias}
    (haliases : access.aliasArg (path ++ [j]) arg = .ok aliases)
    (hmem : alias ∈ aliases) : alias ∈ childFrame.retained := by
  unfold DemandNode.childFrame at hchild
  let parent : DemandPoint := ⟨path, .expression, frame.active, frame.future, frame.retained⟩
  cases hexpect : (DemandNode.expression (.call context args origin)).childExpectation?
      access parent index with
  | none => simp [parent, hexpect, reject] at hchild
  | some expectation =>
    have hmapped :
        (fun collected => DemandFrame.mk expectation.active expectation.future
          (collected ++ frame.retained)) <$>
            (DemandNode.expression (.call context args origin)).retainedForChild
              access path index = .ok childFrame := by
      simpa [parent, hexpect] using hchild
    obtain ⟨collected, hcollectedRetained, hresult⟩ := except_map_ok_extract hmapped
    have hcollected : access.aliasesOfArgs path (args.take index) = .ok collected := by
      simpa [DemandNode.retainedForChild] using hcollectedRetained
    have hchildRetained : childFrame.retained = collected ++ frame.retained := by
      have hfields := congrArg DemandFrame.retained hresult
      simpa using hfields.symm
    have hargPrefix : (args.take index)[j]? = some arg := by
      simpa [hji] using harg
    have hargBounds : j < args.length := (List.getElem?_eq_some_iff.mp harg).1
    have htake : j < (args.take index).length := by
      simpa [List.length_take] using (Nat.lt_min.mpr ⟨hji, hargBounds⟩)
    obtain ⟨indexedAliases, hindexed, hmemCollected⟩ :=
      AccessEnv.aliasesOfArgs_index access path (args.take index) hcollected j arg htake hargPrefix
    have hindexedEq : indexedAliases = aliases := by
      have heq := hindexed.symm.trans haliases
      injection heq
    have hmemArg : alias ∈ indexedAliases := by simpa [hindexedEq] using hmem
    have hmemPrefix : alias ∈ collected := hmemCollected alias hmemArg
    rw [hchildRetained]
    exact List.mem_append_left _ hmemPrefix

private def addVisibleBinder (active : List VarId) (binder : VarId) : List VarId :=
  if active.contains binder then active else binder :: active

private theorem addVisibleBinder_mem_congr {active active' : List VarId}
    (hactive : ∀ x, x ∈ active ↔ x ∈ active') (binder : VarId) :
    ∀ x, x ∈ addVisibleBinder active binder ↔ x ∈ addVisibleBinder active' binder := by
  have hcontains : active.contains binder = active'.contains binder := by
    apply Bool.eq_iff_iff.mpr
    simpa only [List.contains_iff_mem] using hactive binder
  have hmem : binder ∈ active ↔ binder ∈ active' := hactive binder
  by_cases hb : binder ∈ active
  · have hb' := hmem.mp hb
    intro x
    simp [addVisibleBinder, hb, hb', hactive]
  · have hb' : binder ∉ active' := fun h => hb (hmem.mpr h)
    intro x
    simp [addVisibleBinder, hb, hb', hactive]

private theorem visibleAfterBinders_mem_congr {active active' : List VarId}
    (hactive : ∀ x, x ∈ active ↔ x ∈ active') :
    ∀ (binders : List VarId) (x : VarId),
      x ∈ binders.foldl addVisibleBinder active ↔
        x ∈ binders.foldl addVisibleBinder active' := by
  intro binders
  induction binders generalizing active active' with
  | nil => exact hactive
  | cons binder rest ih =>
    intro x
    simp only [List.foldl_cons]
    exact ih (addVisibleBinder_mem_congr hactive binder) x

private def visibleAfterStatement (active : List VarId) : Stmt → List VarId
  | .letS binder _ _ => addVisibleBinder active binder
  | _ => active

private theorem visibleAfterStatements_mem_congr {active active' : List VarId}
    (hactive : ∀ x, x ∈ active ↔ x ∈ active') :
    ∀ (statements : List Stmt) (x : VarId),
      x ∈ statements.foldl visibleAfterStatement active ↔
        x ∈ statements.foldl visibleAfterStatement active' := by
  intro statements
  induction statements generalizing active active' with
  | nil => exact hactive
  | cons statement rest ih =>
    intro x
    simp only [List.foldl_cons]
    apply ih
    intro y
    cases statement
    case letS binder expr origin => exact addVisibleBinder_mem_congr hactive binder y
    all_goals exact hactive y

theorem DemandNode.visibleForChild_mem_congr (node : DemandNode) (index : Nat)
    {active active' : List VarId}
    (hactive : ∀ x, x ∈ active ↔ x ∈ active') :
    ∀ x, x ∈ node.visibleForChild active index ↔ x ∈ node.visibleForChild active' index := by
  cases node with
  | expression _ | place _ | view _ | bound _ => intro x; exact hactive x
  | statement statement =>
    cases statement with
    | forRange binder lo hi body origin =>
      intro x
      have hcontains : active.contains binder = active'.contains binder := by
        apply Bool.eq_iff_iff.mpr
        simpa only [List.contains_iff_mem] using hactive binder
      simp only [DemandNode.visibleForChild]
      rw [hcontains]
      by_cases hcondition : index = 2 ∧ binder ∉ active'
      · simp [hcondition, hactive]
      · simp [hcondition, hactive]
    | forEach binder indexOpt view byRef body origin =>
      intro x
      simp only [DemandNode.visibleForChild]
      split
      · exact visibleAfterBinders_mem_congr hactive (binder :: indexOpt.toList) x
      · exact hactive x
    | _ => intro x; exact hactive x
  | block block =>
    cases block with
    | mk scope statements value =>
      intro x
      change x ∈ (statements.take index).foldl visibleAfterStatement active ↔
        x ∈ (statements.take index).foldl visibleAfterStatement active'
      exact visibleAfterStatements_mem_congr hactive (statements.take index) x

theorem DemandNode.childFrame_active {node : DemandNode} {access : AccessEnv}
    {path : List Nat} {frame : DemandFrame} {index : Nat} {result : DemandFrame}
    (h : node.childFrame access path frame index = .ok result) :
    result.active = node.visibleForChild frame.active index := by
  unfold DemandNode.childFrame at h
  let parent : DemandPoint := ⟨path, .expression, frame.active, frame.future, frame.retained⟩
  cases hchild : node.childExpectation? access parent index with
  | none => simp [parent, hchild, reject] at h
  | some expectation =>
    have hexpectActive : expectation.active = node.visibleForChild frame.active index := by
      unfold DemandNode.childExpectation? at hchild
      cases hnodeChild : node.child? index with
      | none => simp [hnodeChild] at hchild
      | some child =>
        cases hfuture : node.childFuture access parent index with
        | none => simp [hnodeChild, hfuture] at hchild
        | some future =>
          simp [hnodeChild, hfuture] at hchild
          cases hchild
          rfl
    cases hretained : node.retainedForChild access path index with
    | error err =>
      simp [parent, hchild, hretained] at h
      cases h
    | ok retained =>
      simp [parent, hchild, hretained] at h
      cases h
      exact hexpectActive

theorem DemandNode.childFrame_future {node : DemandNode} {access : AccessEnv}
    {path : List Nat} {frame : DemandFrame} {index : Nat} {result : DemandFrame}
    {expectation : DemandChildExpectation}
    (h : node.childFrame access path frame index = .ok result)
    (hchild : node.childExpectation? access
      ⟨path, .expression, frame.active, frame.future, frame.retained⟩ index = some expectation) :
    result.future = expectation.future := by
  let parent : DemandPoint := ⟨path, .expression, frame.active, frame.future, frame.retained⟩
  cases hretained : node.retainedForChild access path index with
  | error err =>
    simp [DemandNode.childFrame, hchild, hretained] at h
    change Except.map (fun aliases =>
      DemandFrame.mk expectation.active expectation.future (aliases ++ frame.retained))
      (.error err) = .ok result at h
    cases h
  | ok aliases =>
    simp [DemandNode.childFrame, hchild, hretained] at h
    change Except.map (fun aliases =>
      DemandFrame.mk expectation.active expectation.future (aliases ++ frame.retained))
      (.ok aliases) = .ok result at h
    cases h
    rfl

def DemandNode.phaseFrame (node : DemandNode) (access : AccessEnv)
    (path : List Nat) (frame : DemandFrame) (phase : DemandPhase) : V DemandFrame := do
  match node with
  | .expression (.call _ args _) =>
    if phase == .call || phase == .mutation then
      let aliases ← access.aliasesOfArgs path args
      pure { frame with retained := aliases ++ frame.retained }
    else pure frame
  | _ => pure frame

theorem DemandNode.phaseFrame_active {node : DemandNode} {access : AccessEnv}
    {path : List Nat} {frame : DemandFrame} {phase : DemandPhase} {result : DemandFrame}
    (h : node.phaseFrame access path frame phase = .ok result) : result.active = frame.active := by
  cases node with
  | expression expression =>
    cases expression with
    | call context args origin =>
      unfold DemandNode.phaseFrame at h
      by_cases hphase : phase == .call || phase == .mutation
      · simp only [hphase, ↓reduceIte] at h
        cases haliases : AccessEnv.aliasesOfArgs access path args with
        | error err =>
          simp [haliases] at h
          cases h
        | ok aliases =>
          simp [haliases] at h
          cases h
          rfl
      · simp [hphase] at h
        cases h
        rfl
    | _ => simp [DemandNode.phaseFrame] at h; cases h; rfl
  | _ => simp [DemandNode.phaseFrame] at h; cases h; rfl

theorem DemandNode.phaseFrame_future {node : DemandNode} {access : AccessEnv}
    {path : List Nat} {frame : DemandFrame} {phase : DemandPhase} {result : DemandFrame}
    (h : node.phaseFrame access path frame phase = .ok result) : result.future = frame.future := by
  cases node with
  | expression expression =>
    cases expression with
    | call context args origin =>
      unfold DemandNode.phaseFrame at h
      by_cases hphase : phase == .call || phase == .mutation
      · simp only [hphase, ↓reduceIte] at h
        cases haliases : AccessEnv.aliasesOfArgs access path args with
        | error err =>
          simp [haliases] at h
          cases h
        | ok aliases =>
          simp [haliases] at h
          cases h
          rfl
      · simp [hphase] at h
        cases h
        rfl
    | _ => simp [DemandNode.phaseFrame] at h; cases h; rfl
  | _ => simp [DemandNode.phaseFrame] at h; cases h; rfl

/-- Successful call entry validates every argument alias at its original operand path. -/
theorem DemandNode.call_phase_alias_argument
    {access : AccessEnv} {path : List Nat} {frame result : DemandFrame}
    {context origin index : Nat} {args : List Arg} {arg : Arg}
    (hphase : (DemandNode.expression (.call context args origin)).phaseFrame
      access path frame .call = .ok result)
    (hindex : index < args.length) (harg : args[index]? = some arg) :
    ∃ aliases, access.aliasArg (path ++ [index]) arg = .ok aliases := by
  have hmapped :
      (fun aliases => { frame with retained := aliases ++ frame.retained }) <$>
        access.aliasesOfArgs path args = .ok result := by
    simpa [DemandNode.phaseFrame] using hphase
  obtain ⟨collected, hcollected, _⟩ := except_map_ok_extract hmapped
  obtain ⟨aliases, haliases, _⟩ :=
    AccessEnv.aliasesOfArgs_index access path args hcollected index arg hindex harg
  exact ⟨aliases, haliases⟩

/-- A by-reference call argument's retained aliases are present at mutation
phase, where the call may update the argument's backing storage. -/
theorem DemandNode.call_mutation_retains_argument
    {access : AccessEnv} {path : List Nat} {frame result : DemandFrame}
    {context origin index : Nat} {args : List Arg} {arg : Arg}
    (hphase : (DemandNode.expression (.call context args origin)).phaseFrame
      access path frame .mutation = .ok result)
    (hindex : index < args.length) (harg : args[index]? = some arg) :
    ∃ aliases, access.aliasArg (path ++ [index]) arg = .ok aliases ∧
      ∀ alias, alias ∈ aliases → alias ∈ result.retained := by
  have hmapped :
      (fun aliases => { frame with retained := aliases ++ frame.retained }) <$>
        access.aliasesOfArgs path args = .ok result := by
    simpa [DemandNode.phaseFrame] using hphase
  obtain ⟨collected, hcollected, hresult⟩ := except_map_ok_extract hmapped
  obtain ⟨aliases, haliases, hmem⟩ :=
    AccessEnv.aliasesOfArgs_index access path args hcollected index arg hindex harg
  refine ⟨aliases, haliases, ?_⟩
  intro alias halias
  have hcollected := hmem alias halias
  change alias ∈ result.retained
  rw [← hresult]
  exact List.mem_append_left _ hcollected

theorem DemandNode.childFrame_retains {node : DemandNode} {access : AccessEnv}
    {path : List Nat} {frame : DemandFrame} {index : Nat} {result : DemandFrame}
    (h : node.childFrame access path frame index = .ok result) {alias : RetainedAlias}
    (hmem : alias ∈ frame.retained) : alias ∈ result.retained := by
  unfold DemandNode.childFrame at h
  let parent : DemandPoint := ⟨path, .expression, frame.active, frame.future, frame.retained⟩
  cases hchild : node.childExpectation? access parent index with
  | none => simp [parent, hchild, reject] at h
  | some expectation =>
    cases hretained : node.retainedForChild access path index with
    | error err =>
      simp [parent, hchild, hretained] at h
      cases h
    | ok aliases =>
      simp [parent, hchild, hretained] at h
      cases h
      exact List.mem_append_right _ hmem

theorem DemandNode.phaseFrame_retains {node : DemandNode} {access : AccessEnv}
    {path : List Nat} {frame : DemandFrame} {phase : DemandPhase} {result : DemandFrame}
    (h : node.phaseFrame access path frame phase = .ok result) {alias : RetainedAlias}
    (hmem : alias ∈ frame.retained) : alias ∈ result.retained := by
  cases node with
  | expression expression =>
    cases expression with
    | call context args origin =>
      unfold DemandNode.phaseFrame at h
      by_cases hphase : phase == .call || phase == .mutation
      · simp only [hphase, ↓reduceIte] at h
        cases haliases : AccessEnv.aliasesOfArgs access path args with
        | error err =>
          simp [haliases] at h
          cases h
        | ok aliases =>
          simp [haliases] at h
          cases h
          exact List.mem_append_right _ hmem
      · simp [hphase] at h
        cases h
        exact hmem
    | _ => simp [DemandNode.phaseFrame] at h; cases h; exact hmem
  | _ => simp [DemandNode.phaseFrame] at h; cases h; exact hmem

def DemandEnv.child {m : Module} {planOwner : Nat} {root}
    (env : DemandEnv m planOwner root) (index : Nat) :
    V (DemandEnv m planOwner root) := do
  let some cursor := env.cursor.child? index
    | reject .block "demand traversal reached a missing source child"
  let frame ← env.cursor.node.childFrame env.access env.cursor.path
    ⟨env.active, env.future, env.retained⟩ index
  let env := { env with cursor := cursor, active := frame.active }
  pure { env with future := frame.future, retained := frame.retained }

def recordDemand {m : Module} {planOwner : Nat} {root}
    (env : DemandEnv m planOwner root)
    (phase : DemandPhase) : DemandCheck m planOwner root (DemandTrace root) := do
  if hphase : env.cursor.node.phaseMatches phase = true then
    let frame ← demandLift (env.cursor.node.phaseFrame env.access env.cursor.path
      ⟨env.active, env.future, env.retained⟩ phase)
    let point : DemandPoint := ⟨env.cursor.path, phase, frame.active, frame.future, frame.retained⟩
    let trace : DemandTrace root := ⟨point, env.cursor, rfl, hphase⟩
    modify fun state => { state with traces := state.traces.push trace }
    pure trace
  else
    demandReject .block "demand traversal reached a different source node"

/-- A checked context and implementation lookup fixes the owner's body root. -/
theorem demandRoot?_context {m : Module} {c : ContextId} {ctx : Context}
    {impl : Impl} (hctx : m.contexts[c]? = some ctx)
    (himpl : m.impls[ctx.impl]? = some impl) :
    demandRoot? m c = some (.block impl.body) := by
  have hc : c < m.contexts.size := (Array.getElem?_eq_some_iff.mp hctx).1
  have hctxValue : m.contexts[c] = ctx := (Array.getElem?_eq_some_iff.mp hctx).2
  simp [demandRoot?, hc, hctxValue, himpl]

/-- A checked context lookup fixes the access environment used by its demand walk. -/
theorem demandAccess?_context {m : Module} {c : ContextId} {ctx : Context}
    {impl : Impl} (hctx : m.contexts[c]? = some ctx)
    (himpl : m.impls[ctx.impl]? = some impl) :
    demandAccess? m c = some ⟨m, impl, ctx⟩ := by
  have hc : c < m.contexts.size := (Array.getElem?_eq_some_iff.mp hctx).1
  have hctxValue : m.contexts[c] = ctx := (Array.getElem?_eq_some_iff.mp hctx).2
  simp [demandAccess?, demandSetup?, hc, hctxValue, himpl]

private theorem demandSetup_initial {m owner setup}
    (hsetup : demandSetup? m owner = some setup) :
    setup.initial = ⟨demandInitialActive m owner, [], []⟩ := by
  by_cases howner : owner < m.contexts.size
  · unfold demandSetup? at hsetup
    simp only [ite_eq_left howner] at hsetup
    cases hctx : m.contexts[owner]? with
    | none => simp [hctx] at hsetup
    | some ctx =>
      cases himpl : m.impls[ctx.impl]? with
      | none => simp [hctx, himpl] at hsetup
      | some impl =>
        simp [hctx, himpl] at hsetup
        cases hsetup
        simp [demandInitialActive, howner]
  · unfold demandSetup? at hsetup
    simp only [ite_eq_right howner] at hsetup
    cases hglobal : m.globals[owner - m.contexts.size]? with
    | none => simp [hglobal] at hsetup
    | some global =>
      simp [hglobal] at hsetup
      cases hsetup
      simp [demandInitialActive, howner]

private def demandSetupWitness (m : Module) (owner : Nat) :
    V (Σ setup, PLift (demandSetup? m owner = some setup)) := do
  match hsetup : demandSetup? m owner with
  | none => reject .block "demand coverage has no owner access environment"
  | some setup => pure ⟨setup, ⟨hsetup⟩⟩

private def DemandPhase.all : List DemandPhase :=
  [.expression, .place, .view, .bound, .statement, .block, .mutation, .call]

private theorem DemandPhase.mem_all (phase : DemandPhase) : phase ∈ DemandPhase.all := by
  cases phase <;> simp [DemandPhase.all]

def AccessEnv.owner (env : AccessEnv) (p : Place) : V DemandOwner := do
  let some t := env.placeType? p | reject .type "shrink owner has no checked type"
  pure ⟨some t, ← env.placeRoots p⟩

def AccessEnv.rootType? (env : AccessEnv) : RootRef → Option Ty
  | .local x => (env.impl.vars[x]?).map (·.ty)
  | .global g => (env.mod.globals[g]?).map (·.ty)
  | .param i => do
    let p ← env.impl.params[i]?
    let v ← env.impl.vars[p.var]?
    match v.ty with
    | .ref _ t => some t
    | _ => none

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

def AccessEnv.callShrinkOwners (env : AccessEnv) (context : ContextId)
    (args : List Arg) : V (List DemandOwner) := do
  let some ctx := env.mod.contexts[context]? | reject .call "call has no context"
  let some callee := env.mod.impls[ctx.impl]? | reject .call "call has no implementation"
  let actual ← env.argsRoots args
  match callee.summary with
  | .unknown => pure (env.unknownOwners actual)
  | .known summary => env.targetOwners callee ctx actual summary.shrinks

def AccessEnv.callEffectOwners (env : AccessEnv) (context : ContextId)
    (args : List Arg) : V (List DemandOwner) := do
  let some ctx := env.mod.contexts[context]? | reject .call "call has no context"
  let some callee := env.mod.impls[ctx.impl]? | reject .call "call has no implementation"
  let actual ← env.argsRoots args
  match callee.summary with
  | .unknown => pure (env.unknownOwners actual)
  | .known summary =>
    env.targetOwners callee ctx actual
      (summary.reads ++ summary.writes ++ summary.grows ++ summary.shrinks ++ summary.rebinds)

private def DemandNode.expectedShrinkOwners (access : AccessEnv) (node : DemandNode)
    (phase : DemandPhase) : V (List DemandOwner) :=
  match phase with
  | .mutation =>
    match node.directShrinkPlace? with
    | some p => (fun owner => [owner]) <$> access.owner p
    | none => match node with
      | .expression (.call context args _) => access.callShrinkOwners context args
      | _ => pure []
  | _ => pure []

private def DemandNode.expectedWholeChecks (access : AccessEnv)
    (forbidden : List DemandOwner) (node : DemandNode) (phase : DemandPhase) :
    V (List DemandWholeCheck) := do
  let wholeChecks ← match phase, node with
    | .place, .place p =>
      let roots ← access.placeRoots p
      pure (forbidden.map fun owner => ⟨owner, roots⟩)
    | .expression, .expression e =>
      match e with
      | .read _ =>
        let roots ← access.exprRoots e
        pure (forbidden.map fun owner => ⟨owner, roots⟩)
      | _ => pure []
    | .mutation, .expression (.call context args _) =>
      if forbidden.isEmpty then pure []
      else
        let effects ← access.callEffectOwners context args
        pure (forbidden.flatMap fun owner => effects.map fun effect =>
          ⟨owner, effect.roots⟩)
    | _, _ => pure []
  pure wholeChecks

private structure DemandExpectedEvidence (root : DemandNode) (access : AccessEnv) where
  expected : DemandExpectedPoint
  item : DemandWorkItem root
  phaseSource : DemandNodeHasPhase item.node expected.phase
  expectedPath : expected.path = item.path
  expectedNode : expected.node = item.node
  phaseFrame : item.node.phaseFrame access item.path item.frame expected.phase =
    .ok expected.frame
  shrinkRequests : DemandNode.expectedShrinkOwners access item.node expected.phase =
    .ok expected.shrinkOwners
  wholeRequests : DemandNode.expectedWholeChecks access item.forbidden item.node expected.phase =
    .ok expected.wholeChecks

private structure DemandExpectedPhaseResult (root : DemandNode) (access : AccessEnv)
    (item : DemandWorkItem root) (phase : DemandPhase) where
  entry : Option (DemandExpectedEvidence root access)
  covers : DemandNodeHasPhase item.node phase →
    ∃ evidence, entry = some evidence ∧ evidence.item.path = item.path ∧
      evidence.item.node = item.node ∧ evidence.item.frame = item.frame ∧
      evidence.expected.phase = phase
  sameItem : ∀ evidence, evidence ∈ entry.toList → evidence.item = item

private structure DemandExpectedPhasesResult (root : DemandNode) (access : AccessEnv)
    (item : DemandWorkItem root) (phases : List DemandPhase) where
  entries : List (DemandExpectedEvidence root access)
  covers : ∀ phase, phase ∈ phases → DemandNodeHasPhase item.node phase →
    ∃ evidence, evidence ∈ entries ∧ evidence.item.path = item.path ∧
      evidence.item.node = item.node ∧ evidence.item.frame = item.frame ∧
      evidence.expected.phase = phase
  sameItem : ∀ evidence, evidence ∈ entries → evidence.item = item

private structure DemandChildWorkResult (root : DemandNode) (access : AccessEnv)
    (parent : DemandWorkItem root) (limit : Nat) where
  items : List (DemandWorkItem root)
  contains : ∀ index child, index < limit → parent.node.child? index = some child →
    ∃ frame, parent.node.childFrame access parent.path parent.frame index = .ok frame ∧
      ∃ item, item ∈ items ∧ item.path = parent.path ++ [index] ∧
        item.node = child ∧ item.frame = frame

private structure DemandExpectedWalkResult (root : DemandNode) (access : AccessEnv)
    (work : List (DemandWorkItem root)) where
  entries : List (DemandExpectedEvidence root access)
  covers : ∀ item, item ∈ work → ∀ phase, DemandNodeHasPhase item.node phase →
    ∃ entry, entry ∈ entries ∧ entry.item.path = item.path ∧
      entry.item.node = item.node ∧ entry.item.frame = item.frame ∧
      entry.expected.phase = phase
  phaseCoverage : ∀ entry, entry ∈ entries → ∀ phase, DemandNodeHasPhase entry.item.node phase →
    ∃ targetEntry, targetEntry ∈ entries ∧
      targetEntry.item.path = entry.item.path ∧
      targetEntry.item.node = entry.item.node ∧
      targetEntry.item.frame = entry.item.frame ∧
      targetEntry.expected.phase = phase
  children : ∀ entry, entry ∈ entries →
    entry.expected.phase = entry.item.node.primaryPhase →
    ∀ index child, entry.item.node.child? index = some child →
    ∀ childPhase, DemandNodeHasPhase child childPhase →
      ∃ childEntry, childEntry ∈ entries ∧
        childEntry.item.path = entry.item.path ++ [index] ∧
        childEntry.item.node = child ∧
        childEntry.expected.phase = childPhase ∧
        ∃ childFrame, entry.item.node.childFrame access entry.item.path
            entry.item.frame index = .ok childFrame ∧
          childEntry.item.frame = childFrame ∧
          ∃ phaseFrame, child.phaseFrame access (entry.item.path ++ [index])
              childFrame childPhase = .ok phaseFrame ∧
            childEntry.expected.frame = phaseFrame

private def DemandNode.expectedPhase (access : AccessEnv)
    (item : DemandWorkItem root) (phase : DemandPhase) :
    V (DemandExpectedPhaseResult root access item phase) := do
  if hphase : item.node.phaseMatches phase = true then
    match hframe : item.node.phaseFrame access item.path item.frame phase with
    | .error error => throw error
    | .ok frame => do
      match hshrink : DemandNode.expectedShrinkOwners access item.node phase with
      | .error error => throw error
      | .ok shrinkOwners =>
        match hwhole : DemandNode.expectedWholeChecks access item.forbidden item.node phase with
        | .error error => throw error
        | .ok wholeChecks => do
          let evidence : DemandExpectedEvidence root access :=
            ⟨⟨item.path, item.node, phase, frame, shrinkOwners, wholeChecks⟩,
              item, hphase, rfl, rfl, hframe, hshrink, hwhole⟩
          pure ⟨some evidence, by
            intro _
            exact ⟨evidence, rfl, rfl, rfl, rfl, rfl⟩, by
            intro candidate hmem
            simp at hmem
            subst candidate
            rfl⟩
  else
    pure ⟨none, by
      intro hvalid
      simp [DemandNodeHasPhase, hphase] at hvalid, by
      intro candidate hmem
      simp at hmem⟩

private def DemandNode.expectedPhases (access : AccessEnv)
    (item : DemandWorkItem root) : (phases : List DemandPhase) →
      V (DemandExpectedPhasesResult root access item phases)
  | [] => pure ⟨[], by intro phase hmem; simp at hmem, by intro evidence hmem; simp at hmem⟩
  | phase :: rest => do
    let head ← DemandNode.expectedPhase access item phase
    let tail ← DemandNode.expectedPhases access item rest
    pure ⟨head.entry.toList ++ tail.entries, by
      intro candidate hmem hvalid
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · obtain ⟨evidence, hentry, hpath, hnode, hframe, hphase⟩ := head.covers hvalid
        exact ⟨evidence, List.mem_append_left _ (by simp [hentry]),
          hpath, hnode, hframe, hphase⟩
      · obtain ⟨evidence, hentry, hpath, hnode, hframe, hphase⟩ :=
          tail.covers candidate hmem hvalid
        exact ⟨evidence, List.mem_append_right _ hentry, hpath, hnode, hframe, hphase⟩,
      by
        intro evidence hmem
        simp only [List.mem_append] at hmem
        rcases hmem with hhead | htail
        · cases hopt : head.entry with
          | none => simp [hopt] at hhead
          | some headEntry =>
            simp [hopt] at hhead
            exact head.sameItem evidence (by simpa [hopt] using hhead)
        · exact tail.sameItem evidence htail⟩

private def DemandNode.expectedChildrenRev (access : AccessEnv)
    (parent : DemandWorkItem root) : (limit : Nat) →
      V (DemandChildWorkResult root access parent limit)
  | 0 => pure ⟨[], by
      intro index child hindex hchild
      omega⟩
  | limit + 1 => do
    let prefixResult ← DemandNode.expectedChildrenRev access parent limit
    match hchild : parent.node.child? limit with
    | none =>
      pure ⟨prefixResult.items, by
        intro index child hindex hnext
        by_cases heq : index = limit
        · subst index
          simp [hchild] at hnext
        · exact prefixResult.contains index child (by omega) hnext⟩
    | some child => do
      match hframe : parent.node.childFrame access parent.path parent.frame limit with
      | .error error => throw error
      | .ok frame => do
        let childForbidden ← match parent.node with
          | .statement (.assignWhole p _ _) =>
            if limit == 1 then
              let owner ← access.owner p
              pure (owner :: parent.forbidden)
            else pure parent.forbidden
          | _ => pure parent.forbidden
        let childItem : DemandWorkItem root :=
          ⟨parent.path ++ [limit], child, frame, childForbidden,
            parent.source.snoc limit (by simpa [DemandNode.child?] using hchild)⟩
        pure ⟨childItem :: prefixResult.items, by
          intro index candidate hindex hnext
          by_cases heq : index = limit
          · subst index
            have hnode : child = candidate := Option.some.inj (hchild.symm.trans hnext)
            subst candidate
            refine ⟨frame, ?_, childItem, ?_, rfl, rfl, rfl⟩
            · exact hframe
            · simp [childItem]
          · obtain ⟨oldFrame, holdFrame, oldItem, holdItem, holdPath, holdNode, holdItemFrame⟩ :=
              prefixResult.contains index candidate (by omega) hnext
            exact ⟨oldFrame, holdFrame, oldItem, List.mem_cons_of_mem _ holdItem,
              holdPath, holdNode, holdItemFrame⟩⟩
termination_by limit => limit

private def DemandNode.expectedChildren (access : AccessEnv)
    (parent : DemandWorkItem root) (limit : Nat) :
      V (DemandChildWorkResult root access parent limit) := do
  let result ← DemandNode.expectedChildrenRev access parent limit
  pure ⟨result.items.reverse, by
    intro index child hindex hchild
    obtain ⟨frame, hframe, item, hitem, hpath, hnode, hitemFrame⟩ :=
      result.contains index child hindex hchild
    exact ⟨frame, hframe, item, List.mem_reverse.mpr hitem,
      hpath, hnode, hitemFrame⟩⟩

private def DemandNode.expectedWork (access : AccessEnv) (root : DemandNode) : Nat →
    (work : List (DemandWorkItem root)) → V (DemandExpectedWalkResult root access work)
  | 0, [] => pure ⟨[], by intro item hmem; simp at hmem,
    by intro entry hmem; simp at hmem,
    by intro entry hmem; simp at hmem⟩
  | 0, _ :: _ => reject .shrink "demand coverage walk exceeded the decoded syntax node limit"
  | _ + 1, [] => pure ⟨[], by intro item hmem; simp at hmem,
    by intro entry hmem; simp at hmem,
    by intro entry hmem; simp at hmem⟩
  | fuel + 1, item :: rest => do
    let here ← DemandNode.expectedPhases access item DemandPhase.all
    let children ← DemandNode.expectedChildren access item item.node.children.length
    let tail ← DemandNode.expectedWork access root fuel (children.items ++ rest)
    pure ⟨here.entries ++ tail.entries, by
      intro candidate hmem phase hvalid
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · obtain ⟨entry, hentry, hpath, hnode, hframe, hphase⟩ :=
          here.covers phase (DemandPhase.mem_all phase) hvalid
        exact ⟨entry, List.mem_append_left _ hentry, hpath, hnode, hframe, hphase⟩
      · obtain ⟨entry, hentry, hpath, hnode, hframe, hphase⟩ :=
          tail.covers candidate (List.mem_append_right _ hmem) phase hvalid
        exact ⟨entry, List.mem_append_right _ hentry, hpath, hnode, hframe, hphase⟩,
      by
        intro entry hmem phase hvalid
        simp only [List.mem_append] at hmem
        rcases hmem with hhere | htail
        · have hitem := here.sameItem entry hhere
          have hvalidItem : DemandNodeHasPhase item.node phase := by
            simpa [hitem] using hvalid
          obtain ⟨targetEntry, htargetEntry, hpath, hnode, hframe, hphase⟩ :=
            here.covers phase (DemandPhase.mem_all phase) hvalidItem
          exact ⟨targetEntry, List.mem_append_left _ htargetEntry,
            hpath.trans (by rw [hitem]), hnode.trans (by rw [hitem]),
            hframe.trans (by rw [hitem]), hphase⟩
        · obtain ⟨targetEntry, htargetEntry, hpath, hnode, hframe, hphase⟩ :=
            tail.phaseCoverage entry htail phase hvalid
          exact ⟨targetEntry, List.mem_append_right _ htargetEntry,
            hpath, hnode, hframe, hphase⟩,
      by
        intro entry hmem hprimary index child hchild childPhase hchildPhase
        simp only [List.mem_append] at hmem
        rcases hmem with hhere | htail
        · have hentryItem := here.sameItem entry hhere
          have hchild' : item.node.child? index = some child := by
            rw [← hentryItem]
            exact hchild
          have hindex : index < item.node.children.length := by
            have hget : (item.node.children[index]?).join = some child := by
              simpa [DemandNode.child?] using hchild'
            have houter : item.node.children[index]? = some (some child) := by
              cases hopt : item.node.children[index]? with
              | none => simp [hopt] at hget
              | some child? =>
                cases child? with
                | none => simp [hopt] at hget
                | some actual =>
                  simp [hopt] at hget
                  have hactual : actual = child := hget
                  subst actual
                  rfl
            exact Classical.choose (List.getElem?_eq_some_iff.mp houter)
          obtain ⟨childFrame, hchildFrame, childItem, hchildItem,
            hchildPath, hchildNode, hitemFrame⟩ :=
              children.contains index child hindex hchild'
          have hchildItemPhase : DemandNodeHasPhase childItem.node childPhase := by
            simpa [hchildNode] using hchildPhase
          obtain ⟨childEntry, hchildEntry, hentryPath, hentryNode, hentryFrame,
            hentryPhase⟩ := tail.covers childItem
              (List.mem_append_left _ hchildItem) childPhase hchildItemPhase
          have hparentPath : entry.item.path = item.path := by rw [hentryItem]
          have hparentNode : entry.item.node = item.node := by rw [hentryItem]
          have hparentFrame : entry.item.frame = item.frame := by rw [hentryItem]
          refine ⟨childEntry, List.mem_append_right _ hchildEntry, ?_, ?_, hentryPhase,
            childFrame, ?_, ?_, childEntry.expected.frame, ?_, rfl⟩
          · calc
              childEntry.item.path = childItem.path := hentryPath
              _ = item.path ++ [index] := hchildPath
              _ = entry.item.path ++ [index] := by rw [hparentPath]
          · calc
              childEntry.item.node = childItem.node := hentryNode
              _ = child := hchildNode
          · simpa [hparentPath, hparentNode, hparentFrame] using hchildFrame
          · calc
              childEntry.item.frame = childItem.frame := hentryFrame
              _ = childFrame := hitemFrame
          · simpa only [hentryNode, hentryPath, hentryFrame, hentryPhase,
              hchildNode, hchildPath, hitemFrame, hparentNode, hparentPath, hparentFrame]
              using childEntry.phaseFrame
        · obtain ⟨childEntry, hchildEntry, hpath, hnode, hphase, childFrame,
            hchildFrame, hentryFrame, phaseFrame, hphaseFrame, hexpectedFrame⟩ :=
              tail.children entry htail hprimary index child hchild childPhase hchildPhase
          exact ⟨childEntry, List.mem_append_right _ hchildEntry, hpath, hnode,
            hphase, childFrame, hchildFrame, hentryFrame, phaseFrame, hphaseFrame,
            hexpectedFrame⟩⟩
termination_by fuel => fuel

private theorem demandSetup_root {m owner setup}
    (hsetup : demandSetup? m owner = some setup) :
    demandRoot? m owner = some setup.root := by
  by_cases howner : owner < m.contexts.size
  · unfold demandSetup? at hsetup
    simp only [ite_eq_left howner] at hsetup
    cases hctx : m.contexts[owner]? with
    | none => simp [hctx] at hsetup
    | some ctx =>
      cases himpl : m.impls[ctx.impl]? with
      | none => simp [hctx, himpl] at hsetup
      | some impl =>
        simp [hctx, himpl] at hsetup
        cases hsetup
        simp [demandRoot?, howner]
        refine ⟨impl, ?_, rfl⟩
        have ⟨_, hctxValue⟩ := Array.getElem?_eq_some_iff.mp hctx
        have hctxImpl : m.contexts[owner].impl = ctx.impl := congrArg Context.impl hctxValue
        rw [hctxImpl]
        exact himpl
  · unfold demandSetup? at hsetup
    simp only [ite_eq_right howner] at hsetup
    cases hglobal : m.globals[owner - m.contexts.size]? with
    | none => simp [hglobal] at hsetup
    | some global =>
      simp [hglobal] at hsetup
      cases hsetup
      simp [demandRoot?, howner, hglobal]

def DemandNode.expectedPoints (m : Module) (owner : Nat) :
    V (List DemandExpectedPoint) := do
  let some setup := demandSetup? m owner
    | reject .block "demand coverage has no owner root"
  let result ← DemandNode.expectedWork setup.access setup.root
    (Decode.maxNodesPerFunction + 1)
    [⟨[], setup.root, setup.initial, [], DemandNodeAt.here setup.root⟩]
  pure (result.entries.map fun entry => entry.expected)

def DemandExpectedAt (m : Module) (owner : Nat)
    (expected : DemandExpectedPoint) : Prop :=
  ∃ points, DemandNode.expectedPoints m owner = .ok points ∧ expected ∈ points

/-- A specific source node and phase occurs in the owner's replayed coverage walk. -/
def DemandExpectedSourceAt (m : Module) (owner : Nat) (path : List Nat)
    (node : DemandNode) (phase : DemandPhase) (expected : DemandExpectedPoint) : Prop :=
  ∃ points, DemandNode.expectedPoints m owner = .ok points ∧ expected ∈ points ∧
    expected.path = path ∧ expected.node = node ∧ expected.phase = phase

private theorem expectedPoints_result {m owner points}
    (hwalk : DemandNode.expectedPoints m owner = .ok points)
    : ∃ setup result, demandSetup? m owner = some setup ∧
      DemandNode.expectedWork setup.access setup.root (Decode.maxNodesPerFunction + 1)
        [⟨[], setup.root, setup.initial, [], DemandNodeAt.here setup.root⟩] = .ok result ∧
      (result.entries.map fun entry => entry.expected) = points := by
  unfold DemandNode.expectedPoints at hwalk
  cases hsetup : demandSetup? m owner with
  | none =>
    simp [hsetup] at hwalk
    cases hwalk
  | some setup =>
    cases hresult : DemandNode.expectedWork setup.access setup.root
        (Decode.maxNodesPerFunction + 1)
        [⟨[], setup.root, setup.initial, [], DemandNodeAt.here setup.root⟩] with
    | error error =>
      simp [hsetup, hresult] at hwalk
      cases hwalk
    | ok result =>
      simp [hsetup, hresult] at hwalk
      have hmap : (result.entries.map fun entry => entry.expected) = points := by
        injection hwalk
      exact ⟨setup, result, rfl, hresult, hmap⟩

private theorem expectedPoints_evidence {m owner points expected}
    (hwalk : DemandNode.expectedPoints m owner = .ok points)
    (hmem : expected ∈ points) :
    DemandSourceAt m owner expected.path expected.node ∧
      DemandNodeHasPhase expected.node expected.phase := by
  obtain ⟨setup, result, hsetup, hresult, hmap⟩ := expectedPoints_result hwalk
  have hmemMap : expected ∈ result.entries.map fun entry => entry.expected := by
    rw [hmap]
    exact hmem
  rcases List.mem_map.mp hmemMap with ⟨entry, hentry, heq⟩
  subst expected
  have hroot := demandSetup_root hsetup
  refine ⟨?_, ?_⟩
  · exact ⟨setup.root, hroot, by
      rw [entry.expectedPath, entry.expectedNode]
      exact entry.item.source⟩
  · simpa [entry.expectedNode] using entry.phaseSource

private theorem DemandNode.phaseFrame_primary (node : DemandNode) (access : AccessEnv)
    (path : List Nat) (frame : DemandFrame) :
    node.phaseFrame access path frame node.primaryPhase = .ok frame := by
  cases node with
  | expression expression => cases expression <;> rfl
  | place place => rfl
  | view view => rfl
  | bound bound => rfl
  | statement statement => rfl
  | block block => rfl

/-- The root expected point keeps the exact initial demand frame for its owner. -/
theorem DemandNode.expectedPoints_root_withFrame {m owner points root}
    (hwalk : DemandNode.expectedPoints m owner = .ok points)
    (hroot : demandRoot? m owner = some root) :
    ∃ expected, expected ∈ points ∧
      DemandExpectedSourceAt m owner [] root root.primaryPhase expected ∧
      expected.frame = ⟨demandInitialActive m owner, [], []⟩ := by
  obtain ⟨setup, result, hsetup, hresult, hmap⟩ := expectedPoints_result hwalk
  have hsetupRoot := demandSetup_root hsetup
  have hrootEq : setup.root = root := Option.some.inj (hsetupRoot.symm.trans hroot)
  have hinitial := demandSetup_initial hsetup
  have hprimary : DemandNodeHasPhase setup.root setup.root.primaryPhase := by
    cases setup.root <;> simp [DemandNodeHasPhase, DemandNode.phaseMatches,
      DemandNode.primaryPhase]
  let initial : DemandWorkItem setup.root :=
    ⟨[], setup.root, setup.initial, [], DemandNodeAt.here setup.root⟩
  obtain ⟨entry, hentry, hpath, hnode, hitemFrame, hphase⟩ :=
    result.covers initial (by simp [initial]) setup.root.primaryPhase hprimary
  have hmemMap : entry.expected ∈ result.entries.map fun item => item.expected :=
    List.mem_map.mpr ⟨entry, hentry, rfl⟩
  have hmem : entry.expected ∈ points := by
    rw [← hmap]
    exact hmemMap
  have hentryPath : entry.expected.path = [] := by
    rw [entry.expectedPath, hpath]
  have hentryNode : entry.expected.node = root := by
    calc
      entry.expected.node = entry.item.node := entry.expectedNode
      _ = initial.node := hnode
      _ = setup.root := rfl
      _ = root := hrootEq
  have hentryPhase : entry.expected.phase = root.primaryPhase := by
    calc
      entry.expected.phase = setup.root.primaryPhase := hphase
      _ = root.primaryPhase := congrArg DemandNode.primaryPhase hrootEq
  have hframePhase := entry.phaseFrame
  rw [← entry.expectedNode, ← entry.expectedPath] at hframePhase
  rw [hentryNode, hentryPath, hentryPhase, DemandNode.phaseFrame_primary] at hframePhase
  have hentryExpectedFrame : entry.expected.frame = entry.item.frame :=
    (Except.ok.inj hframePhase).symm
  have hentryFrame : entry.expected.frame = setup.initial := by
    calc
      entry.expected.frame = entry.item.frame := hentryExpectedFrame
      _ = initial.frame := hitemFrame
      _ = setup.initial := rfl
  refine ⟨entry.expected, hmem, ?_, ?_⟩
  · exact ⟨points, hwalk, hmem, hentryPath, hentryNode, hentryPhase⟩
  · rw [hentryFrame, hinitial]

/-- A successful expected walk contains its source root at the primary phase. -/
theorem DemandNode.expectedPoints_root {m owner points root}
    (hwalk : DemandNode.expectedPoints m owner = .ok points)
    (hroot : demandRoot? m owner = some root) :
    ∃ expected, expected ∈ points ∧
      DemandExpectedSourceAt m owner [] root root.primaryPhase expected := by
  obtain ⟨expected, hmem, hsource, _⟩ :=
    DemandNode.expectedPoints_root_withFrame hwalk hroot
  exact ⟨expected, hmem, hsource⟩

private theorem expectedPoints_child {m owner points path parentNode parentExpected
    index childNode childPhase}
    (hwalk : DemandNode.expectedPoints m owner = .ok points)
    (hparentMem : parentExpected ∈ points)
    (hparentPath : parentExpected.path = path)
    (hparentNode : parentExpected.node = parentNode)
    (hparentPrimary : parentExpected.phase = parentNode.primaryPhase)
    (hchild : parentNode.child? index = some childNode)
    (hchildPhase : DemandNodeHasPhase childNode childPhase) :
    ∃ setup childExpected childFrame phaseFrame,
      demandSetup? m owner = some setup ∧
      DemandExpectedSourceAt m owner (path ++ [index]) childNode childPhase childExpected ∧
      parentNode.childFrame setup.access path parentExpected.frame index = .ok childFrame ∧
      childNode.phaseFrame setup.access (path ++ [index]) childFrame childPhase = .ok phaseFrame ∧
      childExpected.frame = phaseFrame := by
  obtain ⟨setup, result, hsetup, hresult, hmap⟩ := expectedPoints_result hwalk
  have hparentMap : parentExpected ∈ result.entries.map fun entry => entry.expected := by
    rw [hmap]
    exact hparentMem
  rcases List.mem_map.mp hparentMap with ⟨parentEntry, hparentEntry, hparentEq⟩
  have hitemPath : parentEntry.item.path = path := by
    calc
      parentEntry.item.path = parentEntry.expected.path := parentEntry.expectedPath.symm
      _ = parentExpected.path := congrArg DemandExpectedPoint.path hparentEq
      _ = path := hparentPath
  have hitemNode : parentEntry.item.node = parentNode := by
    calc
      parentEntry.item.node = parentEntry.expected.node := parentEntry.expectedNode.symm
      _ = parentExpected.node := congrArg DemandExpectedPoint.node hparentEq
      _ = parentNode := hparentNode
  have hentryPrimary : parentEntry.expected.phase = parentEntry.item.node.primaryPhase := by
    calc
      parentEntry.expected.phase = parentExpected.phase := congrArg DemandExpectedPoint.phase hparentEq
      _ = parentNode.primaryPhase := hparentPrimary
      _ = parentEntry.item.node.primaryPhase := by rw [hitemNode]
  have hitemFrame : parentEntry.item.frame = parentExpected.frame := by
    have hprimaryFrame := DemandNode.phaseFrame_primary parentEntry.item.node setup.access
      parentEntry.item.path parentEntry.item.frame
    have hphaseFrame := parentEntry.phaseFrame
    rw [hentryPrimary, hprimaryFrame] at hphaseFrame
    exact (Except.ok.inj hphaseFrame).trans
      (congrArg DemandExpectedPoint.frame hparentEq)
  have hentryChild : parentEntry.item.node.child? index = some childNode := by
    rw [hitemNode]
    exact hchild
  obtain ⟨childEntry, hchildEntry, hchildPath, hchildNode, hchildExpectedPhase,
      childFrame, hchildFrame, hchildItemFrame, phaseFrame, hphaseFrame, hchildFrameEq⟩ :=
    result.children parentEntry hparentEntry hentryPrimary index childNode hentryChild
      childPhase hchildPhase
  have hchildMem : childEntry.expected ∈ points := by
    rw [← hmap]
    exact List.mem_map.mpr ⟨childEntry, hchildEntry, rfl⟩
  have hchildExpectedPath : childEntry.expected.path = path ++ [index] := by
    calc
      childEntry.expected.path = childEntry.item.path := childEntry.expectedPath
      _ = parentEntry.item.path ++ [index] := hchildPath
      _ = path ++ [index] := by rw [hitemPath]
  have hchildExpectedNode : childEntry.expected.node = childNode := by
    calc
      childEntry.expected.node = childEntry.item.node := childEntry.expectedNode
      _ = childNode := hchildNode
  have hchildSource : DemandExpectedSourceAt m owner (path ++ [index]) childNode
      childPhase childEntry.expected :=
    ⟨points, hwalk, hchildMem, hchildExpectedPath, hchildExpectedNode,
      hchildExpectedPhase⟩
  refine ⟨setup, childEntry.expected, childFrame, phaseFrame, hsetup, hchildSource,
    ?_, ?_, hchildFrameEq⟩
  · simpa [hitemPath, hitemNode, hitemFrame] using hchildFrame
  · simpa [hitemPath] using hphaseFrame

structure DemandExpectedChildFrame (m : Module) (owner : Nat) (path : List Nat)
    (parentNode : DemandNode) (parentPhase : DemandPhase)
    (parentExpected : DemandExpectedPoint) (index : Nat) (childNode : DemandNode)
    (childPhase : DemandPhase) (access : AccessEnv) where
  points : List DemandExpectedPoint
  walk : DemandNode.expectedPoints m owner = .ok points
  parentMember : parentExpected ∈ points
  childExpected : DemandExpectedPoint
  childSource : DemandExpectedSourceAt m owner (path ++ [index]) childNode childPhase childExpected
  childMember : childExpected ∈ points
  childFrame : DemandFrame
  childFrameEq : parentNode.childFrame access path parentExpected.frame index = .ok childFrame
  phaseFrame : DemandFrame
  phaseFrameEq : childNode.phaseFrame access (path ++ [index]) childFrame childPhase = .ok phaseFrame
  expectedFrameEq : childExpected.frame = phaseFrame

structure DemandExpectedPhaseFrame (m : Module) (owner : Nat) (path : List Nat)
    (node : DemandNode) (parentPhase : DemandPhase) (parentExpected : DemandExpectedPoint)
    (targetPhase : DemandPhase) (access : AccessEnv) where
  points : List DemandExpectedPoint
  walk : DemandNode.expectedPoints m owner = .ok points
  parentMember : parentExpected ∈ points
  targetExpected : DemandExpectedPoint
  targetSource : DemandExpectedSourceAt m owner path node targetPhase targetExpected
  targetMember : targetExpected ∈ points
  phaseFrame : DemandFrame
  phaseFrameEq : node.phaseFrame access path parentExpected.frame targetPhase = .ok phaseFrame
  expectedFrameEq : targetExpected.frame = phaseFrame

private structure DemandExpectedCoverage (points : List DemandPoint)
    (expected : List DemandExpectedPoint) where
  token : Unit
  covers : ∀ occurrence, occurrence ∈ expected →
    ∃ point, point ∈ points ∧ point.path = occurrence.path ∧
      point.phase = occurrence.phase ∧
      DemandPoint.sameFrameMembership point occurrence.toPoint

private structure DemandObservedCoverage (points : List DemandPoint)
    (expected : List DemandExpectedPoint) where
  token : Unit
  covers : ∀ point, point ∈ points →
    ∃ occurrence, occurrence ∈ expected ∧ occurrence.path = point.path ∧
      occurrence.phase = point.phase ∧
      DemandPoint.sameFrameMembership point occurrence.toPoint

private def DemandExpectedPoint.verifyObserved {expected : List DemandExpectedPoint}
    (index : DemandExpectedIndex expected) :
    (points : List DemandPoint) → V (DemandObservedCoverage points expected)
  | [] => pure ⟨(), by intro point h; simp at h⟩
  | point :: rest =>
    match hlookup : index.entries[point.key]? with
    | none => reject .shrink s!"demand plan has an unexpected point at {point.path} phase {repr point.phase}"
    | some occurrence => do
      let ⟨hoccurrence, hkey⟩ := index.lookupValid hlookup
      have hpath : occurrence.path = point.path := by
        have h := congrArg DemandKey.path hkey
        simpa [DemandPoint.key, DemandExpectedPoint.toPoint] using h
      have hphase : occurrence.phase = point.phase := by
        have h := congrArg DemandKey.phase hkey
        simpa [DemandPoint.key, DemandExpectedPoint.toPoint] using h
      if hframe : point.active = occurrence.frame.active ∧
          point.future = occurrence.frame.future ∧
          point.retained = occurrence.frame.retained then
        let hrest ← DemandExpectedPoint.verifyObserved index rest
        have hsame : DemandPoint.sameFrameMembership point occurrence.toPoint := by
          simp [DemandPoint.sameFrameMembership, DemandExpectedPoint.toPoint,
            hframe.1, hframe.2.1, hframe.2.2]
        pure ⟨(), by
          intro candidate hmem
          simp only [List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · exact ⟨occurrence, hoccurrence, hpath, hphase, hsame⟩
          · exact hrest.covers candidate hmem⟩
      else reject .shrink s!"demand metadata differs at path {point.path} phase {repr point.phase}"
termination_by points => points.length

private def DemandPathIndex.verifyExpected {points : List DemandPoint}
    (index : DemandPathIndex points) : (expected : List DemandExpectedPoint) →
      V (DemandExpectedCoverage points expected)
  | [] => pure ⟨(), by intro occurrence h; simp at h⟩
  | occurrence :: rest => do
    let key : DemandKey := ⟨occurrence.path, occurrence.phase⟩
    match hlookup : index.entries[key]? with
    | none => reject .shrink s!"demand coverage is missing path {occurrence.path} phase {repr occurrence.phase}"
    | some point => do
      let hrest ← index.verifyExpected rest
      let ⟨hpoint, hkey⟩ := index.lookupValid hlookup
      have hpath : point.path = occurrence.path := by
        have := congrArg DemandKey.path hkey
        simpa [DemandPoint.key, key] using this
      have hphase : point.phase = occurrence.phase := by
        have := congrArg DemandKey.phase hkey
        simpa [DemandPoint.key, key] using this
      if hframe : point.active = occurrence.frame.active ∧
          point.future = occurrence.frame.future ∧
          point.retained = occurrence.frame.retained then
        have hsame : DemandPoint.sameFrameMembership point occurrence.toPoint := by
          simp [DemandPoint.sameFrameMembership, DemandExpectedPoint.toPoint,
            hframe.1, hframe.2.1, hframe.2.2]
        pure ⟨(), by
          intro candidate hmem
          simp only [List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · exact ⟨point, hpoint, hpath, hphase, hsame⟩
          · exact hrest.covers candidate hmem⟩
      else reject .shrink s!"demand metadata differs at path {occurrence.path} phase {repr occurrence.phase}"

theorem DemandExpectedSourceAt.sourceFacts {m owner path node phase expected}
    (sourceAt : DemandExpectedSourceAt m owner path node phase expected) :
    DemandSourceAt m owner path node ∧ DemandNodeHasPhase node phase := by
  rcases sourceAt with ⟨points, hwalk, hmem, hpath, hnode, hphase⟩
  obtain ⟨hsource, hhasPhase⟩ := expectedPoints_evidence hwalk hmem
  exact ⟨by simpa [hpath, hnode] using hsource, by simpa [hnode, hphase] using hhasPhase⟩

/-- A direct mutation request names the canonical owner checked during replay. -/
theorem DemandExpectedSourceAt.directShrinkOwner
    {m owner path node phase expected place access shrinkOwner}
    (sourceAt : DemandExpectedSourceAt m owner path node phase expected)
    (mutation : phase = .mutation)
    (directPlace : node.directShrinkPlace? = some place)
    (accessMatches : demandAccess? m owner = some access)
    (ownerResult : access.owner place = .ok shrinkOwner) :
    shrinkOwner ∈ expected.shrinkOwners := by
  rcases sourceAt with ⟨points, hwalk, hmem, hpath, hnode, hphase⟩
  obtain ⟨setup, result, hsetup, hresult, hmap⟩ := expectedPoints_result hwalk
  have hsourceMap : expected ∈ result.entries.map fun entry => entry.expected := by
    rw [hmap]
    exact hmem
  rcases List.mem_map.mp hsourceMap with ⟨entry, hentry, hentryExpected⟩
  have hentryPath : entry.item.path = path := by
    calc
      entry.item.path = entry.expected.path := entry.expectedPath.symm
      _ = expected.path := congrArg DemandExpectedPoint.path hentryExpected
      _ = path := hpath
  have hentryNode : entry.item.node = node := by
    calc
      entry.item.node = entry.expected.node := entry.expectedNode.symm
      _ = expected.node := congrArg DemandExpectedPoint.node hentryExpected
      _ = node := hnode
  have hphaseExpected : expected.phase = .mutation := hphase.trans mutation
  have hsetupAccess : setup.access = access := by
    simpa [demandAccess?, hsetup] using accessMatches
  have hshrinkRequests : DemandNode.expectedShrinkOwners access node .mutation =
      .ok expected.shrinkOwners := by
    simpa [hsetupAccess, hentryNode, hphaseExpected, hentryExpected] using entry.shrinkRequests
  have hownerList : [shrinkOwner] = expected.shrinkOwners := by
    have hownerResult := hshrinkRequests
    simp only [DemandNode.expectedShrinkOwners, directPlace, ownerResult] at hownerResult
    change (Except.ok [shrinkOwner] : V (List DemandOwner)) =
      Except.ok expected.shrinkOwners at hownerResult
    exact Except.ok.inj hownerResult
  rw [← hownerList]
  simp

/-- A call mutation occurrence reuses the checked access query for its
arguments and for the owners requested by the callee summary. -/
theorem DemandExpectedSourceAt.callShrinkOwners
    {m owner path node phase expected context args origin access}
    (sourceAt : DemandExpectedSourceAt m owner path node phase expected)
    (mutation : phase = .mutation)
    (callNode : node = .expression (.call context args origin))
    (accessMatches : demandAccess? m owner = some access) :
    ∃ actual, access.argsRoots args = .ok actual ∧
      access.callShrinkOwners context args = .ok expected.shrinkOwners := by
  rcases sourceAt with ⟨points, hwalk, hmem, hpath, hnode, hphase⟩
  obtain ⟨setup, result, hsetup, hresult, hmap⟩ := expectedPoints_result hwalk
  have hsourceMap : expected ∈ result.entries.map fun entry => entry.expected := by
    rw [hmap]
    exact hmem
  rcases List.mem_map.mp hsourceMap with ⟨entry, hentry, hentryExpected⟩
  have hentryPath : entry.item.path = path := by
    calc
      entry.item.path = entry.expected.path := entry.expectedPath.symm
      _ = expected.path := congrArg DemandExpectedPoint.path hentryExpected
      _ = path := hpath
  have hentryNode : entry.item.node = node := by
    calc
      entry.item.node = entry.expected.node := entry.expectedNode.symm
      _ = expected.node := congrArg DemandExpectedPoint.node hentryExpected
      _ = node := hnode
  have hphaseExpected : expected.phase = .mutation := hphase.trans mutation
  have hsetupAccess : setup.access = access := by
    simpa [demandAccess?, hsetup] using accessMatches
  have hshrinkRequests : access.callShrinkOwners context args =
      .ok expected.shrinkOwners := by
    simpa [hsetupAccess, hentryNode, hphaseExpected, hentryExpected, callNode,
      DemandNode.expectedShrinkOwners, DemandNode.directShrinkPlace?] using entry.shrinkRequests
  have hargs : ∃ actual, access.argsRoots args = .ok actual := by
    unfold AccessEnv.callShrinkOwners at hshrinkRequests
    cases hctx : access.mod.contexts[context]? with
    | none => simp [hctx, reject] at hshrinkRequests
    | some ctx =>
      simp only [hctx] at hshrinkRequests
      cases himpl : access.mod.impls[ctx.impl]? with
      | none => simp [himpl, reject] at hshrinkRequests
      | some callee =>
        simp only [himpl] at hshrinkRequests
        cases hactual : access.argsRoots args with
        | error error =>
          rw [hactual] at hshrinkRequests
          cases hshrinkRequests
        | ok actual => exact ⟨actual, rfl⟩
  exact ⟨hargs.choose, hargs.choose_spec, hshrinkRequests⟩

/-- A primary source point and each valid immediate child occur in the same
coverage walk. -/
theorem DemandExpectedSourceAt.child
    {m owner path parentNode parentPhase parentExpected index childNode childPhase}
    (parentSource : DemandExpectedSourceAt m owner path parentNode parentPhase parentExpected)
    (primary : parentPhase = parentNode.primaryPhase)
    (hchild : parentNode.child? index = some childNode)
    (hchildPhase : DemandNodeHasPhase childNode childPhase) :
    ∃ childExpected points,
      DemandExpectedSourceAt m owner (path ++ [index]) childNode childPhase childExpected ∧
      DemandNode.expectedPoints m owner = .ok points ∧
      parentExpected ∈ points ∧ childExpected ∈ points := by
  rcases parentSource with ⟨points, hwalk, hparentMem, hparentPath, hparentNode, hparentPhase⟩
  have hparentPrimary : parentExpected.phase = parentNode.primaryPhase := by
    rw [hparentPhase]
    exact primary
  obtain ⟨setup, childExpected, childFrame, phaseFrame, hsetup, hchildSource,
      hchildFrame, hphaseFrame, hchildFrameEq⟩ :=
    expectedPoints_child hwalk hparentMem hparentPath hparentNode hparentPrimary
      hchild hchildPhase
  have hchildSource' := hchildSource
  rcases hchildSource' with ⟨childPoints, hchildWalk, hchildMem, _, _, _⟩
  have hpoints : points = childPoints := by
    rw [hwalk] at hchildWalk
    injection hchildWalk
  have hchildMemParent : childExpected ∈ points := by
    rw [hpoints]
    exact hchildMem
  exact ⟨childExpected, points, hchildSource, hwalk, hparentMem, hchildMemParent⟩

/-- A source child stays in the parent's coverage walk, with the exact frames
used by demand traversal. The access environment must be the owner's checked one. -/
theorem DemandExpectedSourceAt.childFrame
    {m owner path parentNode parentPhase parentExpected index childNode childPhase access}
    (parentSource : DemandExpectedSourceAt m owner path parentNode parentPhase parentExpected)
    (primary : parentPhase = parentNode.primaryPhase)
    (hchild : parentNode.child? index = some childNode)
    (hchildPhase : DemandNodeHasPhase childNode childPhase)
    (accessMatches : demandAccess? m owner = some access) :
    Nonempty (DemandExpectedChildFrame m owner path parentNode parentPhase parentExpected index
      childNode childPhase access) := by
  rcases parentSource with ⟨points, hwalk, hparentMem, hparentPath, hparentNode, hparentPhase⟩
  have hparentPrimary : parentExpected.phase = parentNode.primaryPhase := by
    rw [hparentPhase]
    exact primary
  obtain ⟨setup, childExpected, childFrame, phaseFrame, hsetup, hchildSource,
      hchildFrame, hphaseFrame, hchildFrameEq⟩ :=
    expectedPoints_child hwalk hparentMem hparentPath hparentNode hparentPrimary
      hchild hchildPhase
  have hsetupAccess : setup.access = access := by
    simpa [demandAccess?, hsetup] using accessMatches
  have hchildFrame' : parentNode.childFrame access path parentExpected.frame index =
      .ok childFrame := by
    rw [← hsetupAccess]
    exact hchildFrame
  have hphaseFrame' : childNode.phaseFrame access (path ++ [index]) childFrame childPhase =
      .ok phaseFrame := by
    rw [← hsetupAccess]
    exact hphaseFrame
  rcases hchildSource with ⟨childPoints, hchildWalk, hchildMem, hchildPath, hchildNode,
    hchildSourcePhase⟩
  have hpoints : points = childPoints := by
    rw [hwalk] at hchildWalk
    injection hchildWalk
  have hchildMember : childExpected ∈ points := by
    rw [hpoints]
    exact hchildMem
  exact ⟨⟨points, hwalk, hparentMem, childExpected,
    ⟨points, hwalk, hchildMember, hchildPath, hchildNode, hchildSourcePhase⟩,
    hchildMember, childFrame, hchildFrame', phaseFrame, hphaseFrame', hchildFrameEq⟩⟩

/-- A primary point and each valid phase of that same node share one expected walk. -/
theorem DemandExpectedSourceAt.phaseFrame
    {m owner path node parentPhase parentExpected targetPhase access}
    (parentSource : DemandExpectedSourceAt m owner path node parentPhase parentExpected)
    (primary : parentPhase = node.primaryPhase)
    (targetHasPhase : DemandNodeHasPhase node targetPhase)
    (accessMatches : demandAccess? m owner = some access) :
    Nonempty (DemandExpectedPhaseFrame m owner path node parentPhase parentExpected
      targetPhase access) := by
  rcases parentSource with ⟨points, hwalk, hparentMem, hparentPath, hparentNode, hparentPhase⟩
  have hparentPrimary : parentExpected.phase = node.primaryPhase := by
    rw [hparentPhase]
    exact primary
  obtain ⟨setup, result, hsetup, hresult, hmap⟩ := expectedPoints_result hwalk
  have hparentMap : parentExpected ∈ result.entries.map fun entry => entry.expected := by
    rw [hmap]
    exact hparentMem
  rcases List.mem_map.mp hparentMap with ⟨parentEntry, hparentEntry, hparentEq⟩
  have hitemPath : parentEntry.item.path = path := by
    calc
      parentEntry.item.path = parentEntry.expected.path := parentEntry.expectedPath.symm
      _ = parentExpected.path := congrArg DemandExpectedPoint.path hparentEq
      _ = path := hparentPath
  have hitemNode : parentEntry.item.node = node := by
    calc
      parentEntry.item.node = parentEntry.expected.node := parentEntry.expectedNode.symm
      _ = parentExpected.node := congrArg DemandExpectedPoint.node hparentEq
      _ = node := hparentNode
  have hentryPrimary : parentEntry.expected.phase = parentEntry.item.node.primaryPhase := by
    calc
      parentEntry.expected.phase = parentExpected.phase := congrArg DemandExpectedPoint.phase hparentEq
      _ = node.primaryPhase := hparentPrimary
      _ = parentEntry.item.node.primaryPhase := by rw [hitemNode]
  have hitemFrame : parentEntry.item.frame = parentExpected.frame := by
    have hprimaryFrame := DemandNode.phaseFrame_primary parentEntry.item.node setup.access
      parentEntry.item.path parentEntry.item.frame
    have hphaseFrame := parentEntry.phaseFrame
    rw [hentryPrimary, hprimaryFrame] at hphaseFrame
    exact (Except.ok.inj hphaseFrame).trans
      (congrArg DemandExpectedPoint.frame hparentEq)
  have htargetHasPhase : DemandNodeHasPhase parentEntry.item.node targetPhase := by
    simpa [hitemNode] using targetHasPhase
  obtain ⟨targetEntry, htargetEntry, htargetItemPath, htargetItemNode,
      htargetItemFrame, htargetPhase⟩ :=
    result.phaseCoverage parentEntry hparentEntry targetPhase htargetHasPhase
  have htargetPath : targetEntry.item.path = path := by
    calc
      targetEntry.item.path = parentEntry.item.path := htargetItemPath
      _ = path := hitemPath
  have htargetNode : targetEntry.item.node = node := by
    calc
      targetEntry.item.node = parentEntry.item.node := htargetItemNode
      _ = node := hitemNode
  have htargetFrame : targetEntry.item.frame = parentExpected.frame :=
    htargetItemFrame.trans hitemFrame
  have htargetMember : targetEntry.expected ∈ points := by
    rw [← hmap]
    exact List.mem_map.mpr ⟨targetEntry, htargetEntry, rfl⟩
  have htargetExpectedPath : targetEntry.expected.path = path := by
    calc
      targetEntry.expected.path = targetEntry.item.path := targetEntry.expectedPath
      _ = path := htargetPath
  have htargetExpectedNode : targetEntry.expected.node = node := by
    calc
      targetEntry.expected.node = targetEntry.item.node := targetEntry.expectedNode
      _ = node := htargetNode
  have hsetupAccess : setup.access = access := by
    simpa [demandAccess?, hsetup] using accessMatches
  have hphaseFrame : node.phaseFrame access path parentExpected.frame targetPhase =
      .ok targetEntry.expected.frame := by
    rw [← hsetupAccess, ← htargetNode, ← htargetPath, ← htargetFrame, ← htargetPhase]
    exact targetEntry.phaseFrame
  have htargetSource : DemandExpectedSourceAt m owner path node targetPhase
      targetEntry.expected :=
    ⟨points, hwalk, htargetMember, htargetExpectedPath, htargetExpectedNode,
      htargetPhase⟩
  exact ⟨⟨points, hwalk, hparentMem, targetEntry.expected, htargetSource,
    htargetMember, targetEntry.expected.frame, hphaseFrame, rfl⟩⟩

def PlansWellFormed (m : Module) (plans : Array (Array DemandPoint)) : Prop :=
  plans.size = (if m.profile == .pilot then 0 else m.contexts.size + m.globals.size) ∧
    ∀ owner plan, plans[owner]? = some plan →
      DemandPathPhaseUnique plan ∧
        (∀ point, point ∈ plan.toList →
          ∃ node, DemandSourceAt m owner point.path node ∧ DemandNodeHasPhase node point.phase) ∧
        (∀ expected, DemandExpectedAt m owner expected →
          ∃ point, point ∈ plan.toList ∧ point.path = expected.path ∧
            point.phase = expected.phase ∧
            DemandPoint.sameFrameMembership point expected.toPoint) ∧
        (∀ point, point ∈ plan.toList →
          ∃ expected, DemandExpectedAt m owner expected ∧ point.path = expected.path ∧
            point.phase = expected.phase ∧
            DemandPoint.sameFrameMembership point expected.toPoint)

/-- A focus pairs a unique checked point lookup with the syntax node at its owner path. -/
structure DemandFocus (m : Module) (plan : Array DemandPoint)
    (owner : Nat) (path : List Nat) (phase : DemandPhase) (node : DemandNode) where
  point : DemandPoint
  lookup : DemandPoint.lookup? plan path phase = some point
  pathPhaseUnique : DemandPathPhaseUnique plan
  sourceAt : DemandSourceAt m owner path node
  hasPhase : DemandNodeHasPhase node phase

structure DemandExpectedFocus (m : Module) (plan : Array DemandPoint)
    (owner : Nat) (path : List Nat) (phase : DemandPhase) (node : DemandNode)
    (expected : DemandExpectedPoint) where
  focus : DemandFocus m plan owner path phase node
  pointMem : focus.point ∈ plan.toList
  frameMatches : DemandPoint.sameFrameMembership focus.point expected.toPoint

/-- Expected source coverage constructs a focus with its unique plan lookup. -/
noncomputable def DemandFocus.ofExpected {m plans owner plan path phase node expected}
    (wellFormed : PlansWellFormed m plans)
    (ownerPlan : plans[owner]? = some plan)
    (expectedAt : DemandExpectedAt m owner expected)
    (expectedPath : expected.path = path)
    (expectedPhase : expected.phase = phase)
    (sourceAt : DemandSourceAt m owner path node)
    (hasPhase : DemandNodeHasPhase node phase) :
    DemandExpectedFocus m plan owner path phase node expected := by
  have ownerWellFormed := wellFormed.2 owner plan ownerPlan
  have expectedCoverage := ownerWellFormed.2.2.1 expected expectedAt
  let point : DemandPoint := Classical.choose expectedCoverage
  have pointSpec := Classical.choose_spec expectedCoverage
  obtain ⟨pointMem, pointPath, pointPhase, frameMatches⟩ := pointSpec
  have pointAtPath : point.path = path := pointPath.trans expectedPath
  have pointAtPhase : point.phase = phase := pointPhase.trans expectedPhase
  have lookup := DemandPoint.lookupList_of_mem_unique plan.toList point
    (by
      intro a b ha hb hpath hphase
      exact ownerWellFormed.1 a b ha hb hpath hphase)
    pointMem
  have focusLookup : DemandPoint.lookup? plan path phase = some point := by
    simpa [DemandPoint.lookup?, pointAtPath, pointAtPhase] using lookup
  exact ⟨⟨point, focusLookup, ownerWellFormed.1, sourceAt, hasPhase⟩,
    pointMem, frameMatches⟩

noncomputable def DemandFocus.ofExpectedSource {m plans owner plan path phase node expected}
    (wellFormed : PlansWellFormed m plans)
    (ownerPlan : plans[owner]? = some plan)
    (expectedSource : DemandExpectedSourceAt m owner path node phase expected)
    (sourceAt : DemandSourceAt m owner path node)
    (hasPhase : DemandNodeHasPhase node phase) :
    DemandExpectedFocus m plan owner path phase node expected := by
  let points : List DemandExpectedPoint := Classical.choose expectedSource
  have sourceSpec := Classical.choose_spec expectedSource
  rcases sourceSpec with ⟨hwalk, hmem, expectedPath, _, expectedPhase⟩
  exact DemandFocus.ofExpected wellFormed ownerPlan ⟨points, hwalk, hmem⟩
    expectedPath expectedPhase sourceAt hasPhase

def DemandFocus.child {m plan owner path phase node}
    (parent : DemandFocus m plan owner path phase node) (index : Nat)
    (childNode : DemandNode) (childPhase : DemandPhase)
    (hchild : node.child? index = some childNode)
    (hphase : DemandNodeHasPhase childNode childPhase)
    (point : DemandPoint)
    (hlookup : DemandPoint.lookup? plan (path ++ [index]) childPhase = some point) :
    DemandFocus m plan owner (path ++ [index]) childPhase childNode :=
  ⟨point, hlookup, parent.pathPhaseUnique,
    parent.sourceAt.child hchild, hphase⟩

private def checkDemandFuture (access : AccessEnv) (point : DemandPoint)
    (owner : DemandOwner) : (variables : List VarId) →
      V (PLift (∀ x, x ∈ variables → x ∈ point.active → ∀ alias,
        access.aliasVariable x = .ok (some alias) → owner.conflicts alias = false))
  | [] => pure ⟨by intro x hmem; cases hmem⟩
  | x :: rest => do
    let headSafe : PLift (∀ alias, x ∈ point.active →
        access.aliasVariable x = .ok (some alias) → owner.conflicts alias = false) ←
      if hactive : point.active.contains x then
        match halias : access.aliasVariable x with
        | .error err => throw err
        | .ok none => pure ⟨by
            intro alias _ hlookup
            rw [halias] at hlookup
            cases hlookup⟩
        | .ok (some alias) =>
          if hconflict : owner.conflicts alias then
            reject .shrink s!"shrink conflicts with demanded variable {x}"
          else
            have hsafe : owner.conflicts alias = false := by
              cases hvalue : owner.conflicts alias with
              | false => rfl
              | true => exact False.elim (hconflict (by simpa [hvalue]))
            pure ⟨by
              intro candidate _ hlookup
              rw [halias] at hlookup
              injection hlookup with heq
              cases heq
              exact hsafe⟩
      else
        pure ⟨by
          intro alias hmem _
          have hcontains : point.active.contains x = true := by
            exact (List.contains_iff_mem).2 hmem
          exact False.elim (hactive hcontains)⟩
    let restSafe ← checkDemandFuture access point owner rest
    pure ⟨by
      intro candidate hmem hactive alias hlookup
      simp only [List.mem_cons] at hmem
      rcases hmem with hhead | htail
      · subst candidate
        exact headSafe.down alias hactive hlookup
      · exact restSafe.down candidate htail hactive alias hlookup⟩
termination_by variables => variables.length

private def checkDemandRetained (owner : DemandOwner) :
    (aliases : List RetainedAlias) → V (PLift (∀ alias, alias ∈ aliases → owner.conflicts alias = false))
  | [] => pure ⟨by intro alias hmem; cases hmem⟩
  | alias :: rest => do
    if hconflict : owner.conflicts alias then
      reject .shrink s!"shrink conflicts with retained {repr alias.source}"
    else
      have hsafe : owner.conflicts alias = false := by
        cases hvalue : owner.conflicts alias with
        | false => rfl
        | true => exact False.elim (hconflict (by simpa [hvalue]))
      let restSafe ← checkDemandRetained owner rest
      pure ⟨by
        intro candidate hmem
        simp only [List.mem_cons] at hmem
        rcases hmem with heq | htail
        · cases heq
          exact hsafe
        · exact restSafe.down candidate htail⟩
termination_by aliases => aliases.length

def checkShrinkOwner {m : Module} {planOwner : Nat} {root}
    (env : DemandEnv m planOwner root) (trace : DemandTrace root)
    (owner : DemandOwner) : DemandCheck m planOwner root Unit := do
  if hmutation : trace.point.phase = .mutation then
    let futureSafe ← demandLift (checkDemandFuture env.access trace.point owner trace.point.future)
    let retainedSafe ← demandLift (checkDemandRetained owner trace.point.retained)
    let safe : DemandPointShrinkSafe env.access trace.point owner :=
      ⟨futureSafe.down, retainedSafe.down⟩
    recordShrinkEvent trace env.access env.accessMatches owner hmutation safe
  else
    demandReject .block "shrink approval is not attached to a mutation point"

def checkShrinkPoint {m : Module} {planOwner : Nat} {root}
    (env : DemandEnv m planOwner root) (_path : List Nat)
    (owner : DemandOwner) : DemandCheck m planOwner root Unit := do
  let trace ← recordDemand env .mutation
  checkShrinkOwner env trace owner

private def checkRootsAgainst (forbiddenRoot : RootRef) :
    (checkedRoots : List RootRef) →
      V (PLift (∀ checkedRoot, checkedRoot ∈ checkedRoots →
        rootsMayOverlap forbiddenRoot checkedRoot = false))
  | [] => pure ⟨by intro checkedRoot hmem; cases hmem⟩
  | checkedRoot :: rest => do
    if hoverlap : rootsMayOverlap forbiddenRoot checkedRoot then
      reject .whole "whole replacement depends on the cleared owner"
    else
      have hdisjoint : rootsMayOverlap forbiddenRoot checkedRoot = false := by
        cases hvalue : rootsMayOverlap forbiddenRoot checkedRoot with
        | false => rfl
        | true => exact False.elim (hoverlap (by simpa [hvalue]))
      let restDisjoint ← checkRootsAgainst forbiddenRoot rest
      pure ⟨by
        intro candidate hmem
        simp only [List.mem_cons] at hmem
        rcases hmem with heq | htail
        · cases heq
          exact hdisjoint
        · exact restDisjoint.down candidate htail⟩
termination_by checkedRoots => checkedRoots.length

private def checkRootsDisjoint : (forbiddenRoots : List RootRef) →
    (checkedRoots : List RootRef) → V (PLift (DemandRootsDisjoint forbiddenRoots checkedRoots))
  | [], _ => pure ⟨by intro forbiddenRoot hmem; simp at hmem⟩
  | forbiddenRoot :: rest, checkedRoots => do
    let headDisjoint ← checkRootsAgainst forbiddenRoot checkedRoots
    let restDisjoint ← checkRootsDisjoint rest checkedRoots
    pure ⟨by
      intro candidate hmem checkedRoot hchecked
      have hmem' := List.mem_cons.mp hmem
      rcases hmem' with heq | htail
      · subst candidate
        exact headDisjoint.down checkedRoot hchecked
      · exact restDisjoint.down candidate htail checkedRoot hchecked⟩
termination_by forbiddenRoots => forbiddenRoots.length

def checkWholeRoots {m : Module} {planOwner : Nat} {root}
    (env : DemandEnv m planOwner root) (trace : DemandTrace root)
    (roots : List RootRef) : DemandCheck m planOwner root Unit := do
  for owner in env.forbidden do
    let disjoint ← demandLift (checkRootsDisjoint owner.roots roots)
    recordWholeRootsEvent trace owner roots disjoint.down

def checkCallDemand {m : Module} {planOwner : Nat} {root}
    (env : DemandEnv m planOwner root) (_path : List Nat)
    (context : ContextId) (args : List Arg) (aliases : List RetainedAlias) :
    DemandCheck m planOwner root Unit := do
  let _ ← recordDemand env .call
  let mutationTrace ← recordDemand env .mutation
  let callEnv := env.withAliases aliases
  let owners ← demandLift (env.access.callShrinkOwners context args)
  for owner in owners do
    checkShrinkOwner callEnv mutationTrace owner
  unless callEnv.forbidden.isEmpty do
    let effects ← demandLift (env.access.callEffectOwners context args)
    for owner in effects do checkWholeRoots callEnv mutationTrace owner.roots

mutual
def demandPlace {m : Module} {planOwner : Nat} {root}
    (env : DemandEnv m planOwner root) (path : List Nat) (p : Place) :
    DemandCheck m planOwner root Unit := do
  let trace ← recordDemand env .place
  checkWholeRoots env trace (← demandLift (env.access.placeRoots p))
  match p with
  | .var _ | .global _ => pure ()
  | .deref e => demandExpr (← demandLift (env.child 0)) (path ++ [0]) e
  | .field owner _ => demandPlace (← demandLift (env.child 0)) (path ++ [0]) owner
  | .elem v i _ =>
    demandView (← demandLift (env.child 0)) (path ++ [0]) v
    demandExpr (← demandLift (env.child 1)) (path ++ [1]) i
termination_by sizeOf p

def demandView {m : Module} {planOwner : Nat} {root}
    (env : DemandEnv m planOwner root) (path : List Nat) (v : View) :
    DemandCheck m planOwner root Unit := do
  let _ ← recordDemand env .view
  match v with
  | .of p => demandPlace (← demandLift (env.child 0)) (path ++ [0]) p
  | .val e => demandExpr (← demandLift (env.child 0)) (path ++ [0]) e
termination_by sizeOf v

def demandBound {m : Module} {planOwner : Nat} {root}
    (env : DemandEnv m planOwner root) (path : List Nat) (b : Bound) :
    DemandCheck m planOwner root Unit := do
  let _ ← recordDemand env .bound
  match b with
  | .omitted => pure ()
  | .expr e | .fromEnd e => demandExpr (← demandLift (env.child 0)) (path ++ [0]) e
termination_by sizeOf b

def demandExpr {m : Module} {planOwner : Nat} {root}
    (env : DemandEnv m planOwner root) (path : List Nat) (e : Expr) :
    DemandCheck m planOwner root Unit := do
  let trace ← recordDemand env .expression
  match e with
  | .lit .. | .bool _ => pure ()
  | .read p =>
    demandPlace (← demandLift (env.child 0)) (path ++ [0]) p
    checkWholeRoots env trace (← demandLift (env.access.exprRoots e))
  | .ref _ p => demandPlace (← demandLift (env.child 0)) (path ++ [0]) p
  | .len v => demandView (← demandLift (env.child 0)) (path ++ [0]) v
  | .slice _ v lo hi _ =>
    demandView (← demandLift (env.child 0)) (path ++ [0]) v
    demandBound (← demandLift (env.child 1)) (path ++ [1]) lo
    demandBound (← demandLift (env.child 2)) (path ++ [2]) hi
  | .un _ a _ | .not a | .conv _ _ a _ | .fill _ a =>
    demandExpr (← demandLift (env.child 0)) (path ++ [0]) a
  | .bin _ a b _ | .cmp _ a b | .and a b | .or a b =>
    demandExpr (← demandLift (env.child 0)) (path ++ [0]) a
    demandExpr (← demandLift (env.child 1)) (path ++ [1]) b
  | .call c args _ =>
    let aliases ← demandArgs env path 0 args
    checkCallDemand env path c args aliases
  | .push p a _ =>
    demandPlace (← demandLift (env.child 0)) (path ++ [0]) p
    demandExpr (← demandLift (env.child 1)) (path ++ [1]) a
  | .pop p org =>
    demandPlace (← demandLift (env.child 0)) (path ++ [0]) p
    checkShrinkPoint env path (← demandLift (env.access.owner p))
  | .ifE c t f =>
    demandExpr (← demandLift (env.child 0)) (path ++ [0]) c
    demandBlock (← demandLift (env.child 1)) (path ++ [1]) t
    demandBlock (← demandLift (env.child 2)) (path ++ [2]) f
  | .blockE b => demandBlock (← demandLift (env.child 0)) (path ++ [0]) b
  | .arrLit _ es | .structLit _ es => demandExprs env path 0 es
termination_by sizeOf e

def demandExprs {m : Module} {planOwner : Nat} {root}
    (env : DemandEnv m planOwner root) (path : List Nat) (index : Nat)
    (es : List Expr) : DemandCheck m planOwner root Unit :=
  match es with
  | [] => pure ()
  | e :: rest => do
    demandExpr (← demandLift (env.child index)) (path ++ [index]) e
    demandExprs env path (index + 1) rest
termination_by sizeOf es

def demandArgs {m : Module} {planOwner : Nat} {root}
    (env : DemandEnv m planOwner root) (path : List Nat) (index : Nat)
    (args : List Arg) : DemandCheck m planOwner root (List RetainedAlias) :=
  match args with
  | [] => pure []
  | arg :: rest => do
    match arg with
    | .byVal e => demandExpr (← demandLift (env.child index)) (path ++ [index]) e
    | .byRef _ p => demandPlace (← demandLift (env.child index)) (path ++ [index]) p
    let aliases ← demandLift (env.access.aliasArg (path ++ [index]) arg)
    let later ← demandArgs env path (index + 1) rest
    pure (aliases ++ later)
termination_by sizeOf args

def demandPrintArgs {m : Module} {planOwner : Nat} {root}
    (env : DemandEnv m planOwner root) (path : List Nat) (index : Nat)
    (args : List PrintArg) : DemandCheck m planOwner root Unit :=
  match args with
  | [] => pure ()
  | arg :: rest => do
    match arg with
    | .text _ => pure ()
    | .expr e =>
      demandExpr (← demandLift (env.child index)) (path ++ [index]) e
    demandPrintArgs env path (index + 1) rest
termination_by sizeOf args

def demandStmt {m : Module} {planOwner : Nat} {root}
    (env : DemandEnv m planOwner root) (path : List Nat)
    (stmt : Stmt) : DemandCheck m planOwner root (DemandEnv m planOwner root) := do
  let _ ← recordDemand env .statement
  match stmt with
  | .letS x e _ =>
    demandExpr (← demandLift (env.child 0)) (path ++ [0]) e
    pure { env with active := x :: env.active }
  | .rebind _ e _ | .expr e _ | .assertS e _ | .exit e _ =>
    demandExpr (← demandLift (env.child 0)) (path ++ [0]) e
    pure env
  | .assign p e _ | .assignOp _ p e _ =>
    demandPlace (← demandLift (env.child 0)) (path ++ [0]) p
    demandExpr (← demandLift (env.child 1)) (path ++ [1]) e
    pure env
  | .append p v _ =>
    demandPlace (← demandLift (env.child 0)) (path ++ [0]) p
    demandView (← demandLift (env.child 1)) (path ++ [1]) v
    pure env
  | .popN p count org =>
    demandPlace (← demandLift (env.child 0)) (path ++ [0]) p
    demandExpr (← demandLift (env.child 1)) (path ++ [1]) count
    checkShrinkPoint env path (← demandLift (env.access.owner p))
    pure env
  | .resize p size fill org =>
    demandPlace (← demandLift (env.child 0)) (path ++ [0]) p
    demandExpr (← demandLift (env.child 1)) (path ++ [1]) size
    match fill with
    | none => pure ()
    | some e => demandExpr (← demandLift (env.child 2)) (path ++ [2]) e
    checkShrinkPoint env path (← demandLift (env.access.owner p))
    pure env
  | .clear p org =>
    demandPlace (← demandLift (env.child 0)) (path ++ [0]) p
    checkShrinkPoint env path (← demandLift (env.access.owner p))
    pure env
  | .assignWhole p e org =>
    demandPlace (← demandLift (env.child 0)) (path ++ [0]) p
    let owner ← demandLift (env.access.owner p)
    checkShrinkPoint env path owner
    demandExpr { (← demandLift (env.child 1)) with forbidden := owner :: env.forbidden } (path ++ [1]) e
    pure env
  | .ifS c t f _ =>
    demandExpr (← demandLift (env.child 0)) (path ++ [0]) c
    demandBlock (← demandLift (env.child 1)) (path ++ [1]) t
    match f with | none => pure () | some b => demandBlock (← demandLift (env.child 2)) (path ++ [2]) b
    pure env
  | .while c b _ =>
    demandExpr (← demandLift (env.child 0)) (path ++ [0]) c
    demandBlock (← demandLift (env.child 1)) (path ++ [1]) b
    pure env
  | .forRange x lo hi b _ =>
    demandExpr (← demandLift (env.child 0)) (path ++ [0]) lo
    demandExpr (← demandLift (env.child 1)) (path ++ [1]) hi
    demandBlock (← demandLift (env.child 2)) (path ++ [2]) b
    pure env
  | .forEach x idx v byRef b _ =>
    demandView (← demandLift (env.child 0)) (path ++ [0]) v
    let _ := byRef
    demandBlock (← demandLift (env.child 1)) (path ++ [1]) b
    pure env
  | .ret value _ =>
    match value with | none => pure () | some e => demandExpr (← demandLift (env.child 0)) (path ++ [0]) e
    pure env
  | .brk _ | .cont _ | .abort .. => pure env
  | .print args _ =>
    demandPrintArgs env path 0 args
    pure env
termination_by sizeOf stmt

def demandStmts {m : Module} {planOwner : Nat} {root}
    (env : DemandEnv m planOwner root) (path : List Nat) (index : Nat)
    (ss : List Stmt) : DemandCheck m planOwner root Unit :=
  match ss with
  | [] => pure ()
  | stmt :: rest => do
    let _ ← demandStmt (← demandLift (env.child index)) (path ++ [index]) stmt
    demandStmts env path (index + 1) rest
termination_by sizeOf ss

def demandBlock {m : Module} {planOwner : Nat} {root}
    (env : DemandEnv m planOwner root) (path : List Nat) (b : Block) :
    DemandCheck m planOwner root Unit := do
  let _ ← recordDemand env .block
  match b with
  | .mk _ ss value =>
    let _ ← demandStmts env path 0 ss
    match value with
    | none => pure ()
    | some e => do
      let valueEnv ← demandLift (env.child ss.length)
      demandExpr valueEnv (path ++ [ss.length]) e
termination_by sizeOf b
end

private structure IndexedDemandPlan (m : Module) (owner : Nat) where
  root : DemandNode
  ownerRoot : demandRoot? m owner = some root
  access : AccessEnv
  accessMatches : demandAccess? m owner = some access
  points : Array DemandPoint
  trace : Array (DemandTrace root)
  tracePoints : trace.map DemandTrace.point = points
  index : DemandPathIndex points.toList
  shrinkEvents : Array (DemandShrinkEvent m owner root)
  shrinkTraceCovered : ∀ event, event ∈ shrinkEvents.toList →
    event.trace.point ∈ points.toList
  wholeRootsEvents : Array (DemandWholeRootsEvent root)
  wholeRootsTraceCovered : ∀ event, event ∈ wholeRootsEvents.toList →
    event.trace.point ∈ points.toList
  expected : List DemandExpectedPoint
  expectedWalk : DemandNode.expectedPoints m owner = .ok expected
  shrinkCoverage : ∀ occurrence, occurrence ∈ expected → occurrence.phase = .mutation → ∀ owner,
    owner ∈ occurrence.shrinkOwners →
      ∃ event, event ∈ shrinkEvents.toList ∧ event.trace.point.path = occurrence.path ∧
        event.owner = owner ∧ event.trace.point.phase = .mutation ∧
          DemandPoint.sameFrameMembership event.trace.point occurrence.toPoint
  wholeRootsCoverage : ∀ occurrence, occurrence ∈ expected → ∀ request,
    request ∈ occurrence.wholeChecks →
      ∃ event, event ∈ wholeRootsEvents.toList ∧
        event.trace.point.path = occurrence.path ∧
        event.trace.point.phase = occurrence.phase ∧
        event.forbidden = request.forbidden ∧ event.checkedRoots = request.checkedRoots ∧
          DemandPoint.sameFrameMembership event.trace.point occurrence.toPoint
  expectedCoverage : ∀ occurrence, occurrence ∈ expected →
    ∃ point, point ∈ points.toList ∧ point.path = occurrence.path ∧
      point.phase = occurrence.phase ∧
      DemandPoint.sameFrameMembership point occurrence.toPoint
  expectedObservedCoverage : ∀ point, point ∈ points.toList →
    ∃ occurrence, occurrence ∈ expected ∧ occurrence.path = point.path ∧
      occurrence.phase = point.phase ∧
      DemandPoint.sameFrameMembership point occurrence.toPoint
  sourceAndPhase : ∀ point, point ∈ points.toList →
    ∃ node, DemandSourceAt m owner point.path node ∧ DemandNodeHasPhase node point.phase

structure DemandShrinkApproval (m : Module) (owner : Nat) (plan : Array DemandPoint) where
  point : DemandPoint
  access : AccessEnv
  accessMatches : demandAccess? m owner = some access
  shrinkOwner : DemandOwner
  node : DemandNode
  pointMem : point ∈ plan.toList
  pathPhaseUnique : DemandPathPhaseUnique plan
  lookup : DemandPoint.lookup? plan point.path .mutation = some point
  sourceAt : DemandSourceAt m owner point.path node
  hasPhase : DemandNodeHasPhase node .mutation
  safe : DemandPointShrinkSafe access point shrinkOwner

structure DemandWholeRootsApproval (m : Module) (owner : Nat)
    (plan : Array DemandPoint) where
  point : DemandPoint
  forbiddenOwner : DemandOwner
  checkedRoots : List RootRef
  node : DemandNode
  pointMem : point ∈ plan.toList
  pathPhaseUnique : DemandPathPhaseUnique plan
  lookup : DemandPoint.lookup? plan point.path point.phase = some point
  sourceAt : DemandSourceAt m owner point.path node
  hasPhase : DemandNodeHasPhase node point.phase
  disjoint : DemandRootsDisjoint forbiddenOwner.roots checkedRoots

structure DemandPlanApprovals (m : Module) (owner : Nat) (plan : Array DemandPoint)
    (expected : List DemandExpectedPoint) where
  access : AccessEnv
  accessMatches : demandAccess? m owner = some access
  shrink : List (DemandShrinkApproval m owner plan)
  wholeRoots : List (DemandWholeRootsApproval m owner plan)
  directShrinkAt : ∀ occurrence, occurrence ∈ expected →
    occurrence.phase = .mutation → occurrence.node.isDirectShrink = true →
    ∀ shrinkOwner, shrinkOwner ∈ occurrence.shrinkOwners →
    ∃ approval : DemandShrinkApproval m owner plan,
      approval.access = access ∧ approval.point.path = occurrence.path ∧
        approval.shrinkOwner = shrinkOwner ∧
        approval.point.phase = .mutation ∧
          DemandPoint.sameFrameMembership approval.point occurrence.toPoint
  callShrinkAt : ∀ occurrence, occurrence ∈ expected →
    ∀ context args, occurrence.node.callInfo? = some (context, args) →
    occurrence.phase = .mutation → ∀ shrinkOwner,
      shrinkOwner ∈ occurrence.shrinkOwners →
      ∃ approval : DemandShrinkApproval m owner plan,
        approval.access = access ∧ approval.point.path = occurrence.path ∧
          approval.shrinkOwner = shrinkOwner ∧
          approval.point.phase = .mutation ∧
            DemandPoint.sameFrameMembership approval.point occurrence.toPoint
  wholeRootsAt : ∀ occurrence, occurrence ∈ expected → ∀ request,
    request ∈ occurrence.wholeChecks →
      ∃ approval : DemandWholeRootsApproval m owner plan,
        approval.point.path = occurrence.path ∧
        approval.point.phase = occurrence.phase ∧
        approval.forbiddenOwner = request.forbidden ∧
        approval.checkedRoots = request.checkedRoots ∧
        DemandPoint.sameFrameMembership approval.point occurrence.toPoint

private def DemandShrinkApproval.ofEvent {m owner} (indexed : IndexedDemandPlan m owner)
    (event : DemandShrinkEvent m owner indexed.root)
    (eventMem : event ∈ indexed.shrinkEvents.toList) :
    DemandShrinkApproval m owner indexed.points := by
  let point := event.trace.point
  have pointMem := indexed.shrinkTraceCovered event eventMem
  have pathPhaseUnique := indexed.index.uniquePathPhase
  have lookup : DemandPoint.lookup? indexed.points point.path .mutation = some point := by
    have hlookup := DemandPoint.lookupList_of_mem_unique indexed.points.toList point
      (by
        intro a b ha hb hpath hphase
        exact pathPhaseUnique a b ha hb hpath hphase)
      pointMem
    simpa [DemandPoint.lookup?, point, event.mutationPhase] using hlookup
  have sourceAt : DemandSourceAt m owner point.path event.trace.cursor.node := by
    refine ⟨indexed.root, indexed.ownerRoot, ?_⟩
    simpa [event.trace.pathMatches, point] using event.trace.cursor.sourceProof
  exact ⟨point, event.access, event.accessMatches, event.owner,
    event.trace.cursor.node, pointMem,
    pathPhaseUnique, lookup, sourceAt,
    by simpa [event.mutationPhase] using event.trace.hasPhase, event.safe⟩

private def DemandWholeRootsApproval.ofEvent {m owner}
    (indexed : IndexedDemandPlan m owner)
    (event : DemandWholeRootsEvent indexed.root)
    (eventMem : event ∈ indexed.wholeRootsEvents.toList) :
    DemandWholeRootsApproval m owner indexed.points := by
  let point := event.trace.point
  have pointMem := indexed.wholeRootsTraceCovered event eventMem
  have pathPhaseUnique := indexed.index.uniquePathPhase
  have lookup : DemandPoint.lookup? indexed.points point.path point.phase = some point := by
    have hlookup := DemandPoint.lookupList_of_mem_unique indexed.points.toList point
      (by
        intro a b ha hb hpath hphase
        exact pathPhaseUnique a b ha hb hpath hphase)
      pointMem
    simpa [DemandPoint.lookup?, point] using hlookup
  have sourceAt : DemandSourceAt m owner point.path event.trace.cursor.node := by
    refine ⟨indexed.root, indexed.ownerRoot, ?_⟩
    simpa [event.trace.pathMatches, point] using event.trace.cursor.sourceProof
  exact ⟨point, event.forbidden, event.checkedRoots, event.trace.cursor.node, pointMem,
    pathPhaseUnique, lookup, sourceAt, event.trace.hasPhase, event.disjoint⟩

private def IndexedDemandPlan.approvals {m owner} (indexed : IndexedDemandPlan m owner) :
    DemandPlanApprovals m owner indexed.points indexed.expected :=
  ⟨indexed.access, indexed.accessMatches,
    indexed.shrinkEvents.toList.attach.map fun event =>
      DemandShrinkApproval.ofEvent indexed event.val event.property,
    indexed.wholeRootsEvents.toList.attach.map fun event =>
      DemandWholeRootsApproval.ofEvent indexed event.val event.property,
    by
      intro occurrence hoccurrence hphase hdirect shrinkOwner howner
      obtain ⟨event, hmem, hpath, heventOwner, hmut, hframe⟩ :=
        indexed.shrinkCoverage occurrence hoccurrence hphase shrinkOwner howner
      let approval := DemandShrinkApproval.ofEvent indexed event hmem
      refine ⟨approval, ?_, ?_, ?_, ?_, ?_⟩
      · have heq := approval.accessMatches.symm.trans indexed.accessMatches
        exact Option.some.inj heq
      · change event.trace.point.path = occurrence.path
        exact hpath
      · change event.owner = shrinkOwner
        exact heventOwner
      · exact hmut
      · change DemandPoint.sameFrameMembership event.trace.point occurrence.toPoint
        exact hframe,
    by
      intro occurrence hoccurrence context args hcall hphase shrinkOwner howner
      obtain ⟨event, hevent, hpath, heventOwner, hmut, hframe⟩ :=
        indexed.shrinkCoverage occurrence hoccurrence hphase shrinkOwner howner
      let approval := DemandShrinkApproval.ofEvent indexed event hevent
      refine ⟨approval, ?_, ?_, ?_, ?_, ?_⟩
      · have heq := approval.accessMatches.symm.trans indexed.accessMatches
        exact Option.some.inj heq
      · change event.trace.point.path = occurrence.path
        exact hpath
      · change event.owner = shrinkOwner
        exact heventOwner
      · exact hmut
      · change DemandPoint.sameFrameMembership event.trace.point occurrence.toPoint
        exact hframe,
    by
      intro occurrence hoccurrence request hrequest
      obtain ⟨event, hevent, hpath, hphase, hforbidden, hroots, hframe⟩ :=
        indexed.wholeRootsCoverage occurrence hoccurrence request hrequest
      refine ⟨DemandWholeRootsApproval.ofEvent indexed event hevent, ?_, ?_, ?_, ?_, ?_⟩
      · change event.trace.point.path = occurrence.path
        exact hpath
      · change event.trace.point.phase = occurrence.phase
        exact hphase
      · change event.forbidden = request.forbidden
        exact hforbidden
      · change event.checkedRoots = request.checkedRoots
        exact hroots
      · change DemandPoint.sameFrameMembership event.trace.point occurrence.toPoint
        exact hframe⟩

private def mkIndexedDemandPlan (m : Module) (owner : Nat) (root : DemandNode)
    (ownerRoot : demandRoot? m owner = some root)
    (state : DemandState m owner root) :
    V (IndexedDemandPlan m owner) := do
  let trace := state.traces
  let points := trace.map DemandTrace.point
  let index ← DemandPathIndex.build points.toList
  let shrinkTraceCovered ← index.verifyShrinkEvents m owner root state.shrinkEvents.toList
  let wholeRootsTraceCovered ← index.verifyWholeRootsEvents root state.wholeRootsEvents.toList
  match hExpected : DemandNode.expectedPoints m owner with
  | .error err => throw err
  | .ok expected => do
    let expectedCoverage ← index.verifyExpected expected
    let expectedIndex ← DemandExpectedIndex.build expected
    let expectedObservedCoverage ← DemandExpectedPoint.verifyObserved expectedIndex points.toList
    let shrinkRequests ← DemandExpectedPoint.verifyShrinkRequests
      state.shrinkEvents.toList expected
    let wholeRootsRequests ← DemandExpectedPoint.verifyWholeRequests
      state.wholeRootsEvents.toList expected
    let ⟨setup, hsetup⟩ ← demandSetupWitness m owner
    have accessMatches : demandAccess? m owner = some setup.access := by
      simp [demandAccess?, hsetup.down]
    let sourceAndPhase : ∀ point, point ∈ points.toList →
        ∃ node, DemandSourceAt m owner point.path node ∧ DemandNodeHasPhase node point.phase := by
      intro point hpoint
      have hpoints : (trace.map DemandTrace.point).toList = points.toList := by simp [points]
      have hmem : point ∈ (trace.map DemandTrace.point).toList := by
        rw [hpoints]
        exact hpoint
      rw [Array.toList_map] at hmem
      rcases List.mem_map.mp hmem with ⟨entry, hentry, heq⟩
      subst point
      refine ⟨entry.cursor.node, ?_, entry.hasPhase⟩
      refine ⟨root, ownerRoot, ?_⟩
      simpa [entry.pathMatches] using entry.cursor.sourceProof
    have frameOfPoint : ∀ occurrence, occurrence ∈ expected → ∀ point,
        point ∈ points.toList → point.path = occurrence.path →
          point.phase = occurrence.phase →
          DemandPoint.sameFrameMembership point occurrence.toPoint := by
      intro occurrence hoccurrence point hpoint hpath hphase
      obtain ⟨expectedPoint, hexpectedPoint, hexpectedPath, hexpectedPhase, hframe⟩ :=
        expectedCoverage.covers occurrence hoccurrence
      have heq : point = expectedPoint := index.uniquePathPhase point expectedPoint
        hpoint hexpectedPoint (hpath.trans hexpectedPath.symm)
          (hphase.trans hexpectedPhase.symm)
      cases heq
      exact hframe
    have shrinkCoverage : ∀ occurrence, occurrence ∈ expected →
        occurrence.phase = .mutation → ∀ shrinkOwner,
          shrinkOwner ∈ occurrence.shrinkOwners →
            ∃ event, event ∈ state.shrinkEvents.toList ∧
              event.trace.point.path = occurrence.path ∧ event.owner = shrinkOwner ∧
                event.trace.point.phase = .mutation ∧
                  DemandPoint.sameFrameMembership event.trace.point occurrence.toPoint := by
      intro occurrence hoccurrence hphase shrinkOwner howner
      obtain ⟨event, hevent, hpath, howner', hmutation⟩ :=
        shrinkRequests.down occurrence hoccurrence hphase shrinkOwner howner
      have hpoint := shrinkTraceCovered.down event hevent
      have hframe := frameOfPoint occurrence hoccurrence event.trace.point hpoint hpath
        (hmutation.trans hphase.symm)
      exact ⟨event, hevent, hpath, howner', hmutation, hframe⟩
    have wholeRootsCoverage : ∀ occurrence, occurrence ∈ expected → ∀ request,
        request ∈ occurrence.wholeChecks →
          ∃ event, event ∈ state.wholeRootsEvents.toList ∧
            event.trace.point.path = occurrence.path ∧
            event.trace.point.phase = occurrence.phase ∧
            event.forbidden = request.forbidden ∧
            event.checkedRoots = request.checkedRoots ∧
            DemandPoint.sameFrameMembership event.trace.point occurrence.toPoint := by
      intro occurrence hoccurrence request hrequest
      obtain ⟨event, hevent, hpath, hphase, hforbidden, hroots⟩ :=
        wholeRootsRequests.down occurrence hoccurrence request hrequest
      have hpoint := wholeRootsTraceCovered.down event hevent
      have hframe := frameOfPoint occurrence hoccurrence event.trace.point hpoint hpath hphase
      exact ⟨event, hevent, hpath, hphase, hforbidden, hroots, hframe⟩
    pure ⟨root, ownerRoot, setup.access, accessMatches, points, trace, rfl, index,
      state.shrinkEvents, shrinkTraceCovered.down,
      state.wholeRootsEvents, wholeRootsTraceCovered.down, expected, hExpected,
      shrinkCoverage, wholeRootsCoverage,
      expectedCoverage.covers, expectedObservedCoverage.covers,
      sourceAndPhase⟩

private def deriveContextDemand (m : Module) (owner : Nat) (howner : owner < m.contexts.size) :
    V (IndexedDemandPlan m owner) := do
  let ctx := m.contexts[owner]
  have hctx : m.contexts[owner]? = some ctx := by simp [ctx, howner]
  match himpl : m.impls[ctx.impl]? with
  | none => reject .call "demand context has no implementation"
  | some impl =>
    let root := DemandNode.block impl.body
    have hroot : demandRoot? m owner = some root := by
      simp [demandRoot?, howner, ctx, himpl, root]
    let cursor : DemandCursor root := ⟨[], root, .here root⟩
    let access : AccessEnv := ⟨m, impl, ctx⟩
    have accessMatches : demandAccess? m owner = some access :=
      demandAccess?_context hctx himpl
    let env : DemandEnv m owner root :=
      ⟨access, accessMatches, cursor, impl.params.toList.map (·.var), [], [], []⟩
    let (_, state) ← (demandBlock env [] impl.body).run { traces := #[] }
    mkIndexedDemandPlan m owner root hroot state

private def deriveGlobalDemand (m : Module) (owner : Nat)
    (hstart : m.contexts.size ≤ owner) (howner : owner < m.contexts.size + m.globals.size) :
    V (IndexedDemandPlan m owner) := do
  let globalIndex := owner - m.contexts.size
  let hglobalIndex : globalIndex < m.globals.size := by omega
  let global := m.globals[globalIndex]
  have hglobal : m.globals[globalIndex]? = some global := by simp [hglobalIndex, global]
  let root := DemandNode.expression global.init
  have hroot : demandRoot? m owner = some root := by
    simp [demandRoot?, hstart, hglobal, globalIndex, global, root]
  let cursor : DemandCursor root := ⟨[], root, .here root⟩
  let access : AccessEnv := ⟨m, initImpl, initContext⟩
  have accessMatches : demandAccess? m owner = some access := by
    simp [demandAccess?, demandSetup?, Nat.not_lt_of_ge hstart,
      show owner - m.contexts.size = globalIndex by rfl, hglobal, access]
  let env : DemandEnv m owner root := ⟨access, accessMatches, cursor, [], [], [], []⟩
  let (_, state) ← (demandExpr env [] global.init).run { traces := #[] }
  mkIndexedDemandPlan m owner root hroot state

private structure OwnedDemandRange (m : Module) (owner fuel : Nat) where
  plans : List (Σ planOwner, IndexedDemandPlan m planOwner)
  length_eq : plans.length = fuel
  ownerAt : ∀ (index : Nat) (plan : Σ planOwner, IndexedDemandPlan m planOwner),
    plans[index]? = some plan → plan.1 = owner + index

private structure IndexedDemandPlans (m : Module) where
  entries : Array (Σ owner, IndexedDemandPlan m owner)
  size_eq : entries.size = (if m.profile == .pilot then 0 else m.contexts.size + m.globals.size)
  ownerAt : ∀ (owner : Nat) (plan : Σ planOwner, IndexedDemandPlan m planOwner),
    entries[owner]? = some plan → plan.1 = owner

private def deriveOwnerRange (m : Module) (owner : Nat) : (fuel : Nat) →
    owner + fuel = m.contexts.size + m.globals.size → V (OwnedDemandRange m owner fuel)
  | 0, _ => pure ⟨[], rfl, by intro index plan hplan; simp at hplan⟩
  | fuel + 1, htotal => do
    have howner : owner < m.contexts.size + m.globals.size := by omega
    let plan ← if hcontext : owner < m.contexts.size then
      deriveContextDemand m owner hcontext
    else
      deriveGlobalDemand m owner (by omega) howner
    let rest ← deriveOwnerRange m (owner + 1) fuel (by omega)
    let plans := ⟨owner, plan⟩ :: rest.plans
    have hlen : plans.length = fuel + 1 := by simp [plans, rest.length_eq]
    have hownerAt : ∀ (index : Nat) (entry : Σ planOwner, IndexedDemandPlan m planOwner),
        plans[index]? = some entry → entry.1 = owner + index := by
      intro index entry hentry
      cases index with
      | zero =>
        have heq : (⟨owner, plan⟩ : Σ planOwner, IndexedDemandPlan m planOwner) = entry := by
          simpa [plans] using hentry
        cases heq
        rfl
      | succ index =>
        have htail : rest.plans[index]? = some entry := by simpa [plans] using hentry
        have htailOwner := rest.ownerAt index entry htail
        omega
    pure ⟨plans, hlen, hownerAt⟩
termination_by fuel => fuel

/-- Derive checked per-point demand and an index for each context and initializer. -/
private def deriveModuleDemandIndexed (m : Module) :
    V (IndexedDemandPlans m) := do
  if hpilot : m.profile == .pilot then
    return ⟨#[], by simp [hpilot], by intro owner plan hplan; simp at hplan⟩
  else
    let plans ← deriveOwnerRange m 0 (m.contexts.size + m.globals.size) (by omega)
    let entries := plans.plans.toArray
    have hsize : entries.size = m.contexts.size + m.globals.size := by
      simp [entries, plans.length_eq]
    have hownerAt : ∀ (owner : Nat) (plan : Σ planOwner, IndexedDemandPlan m planOwner),
        entries[owner]? = some plan → plan.1 = owner := by
      intro owner plan hplan
      have hlist : plans.plans[owner]? = some plan := by simpa [entries] using hplan
      have := plans.ownerAt owner plan hlist
      simpa using this
    pure ⟨entries, by simp [hpilot, hsize], hownerAt⟩

/-- Derive checked per-point demand for each invocation context and initializer. -/
def deriveModuleDemand (m : Module) : V (Array (Array DemandPoint)) := do
  let plans ← deriveModuleDemandIndexed m
  pure (plans.entries.map fun plan => plan.2.points)

/-- Extract checked shrink and whole-root decisions from the exact successful plan. -/
theorem deriveModuleDemand_ok_approvals (m : Module)
    (plans : Array (Array DemandPoint))
    (hderive : deriveModuleDemand m = .ok plans) :
    ∃ approvals : ∀ owner plan, plans[owner]? = some plan →
        Nonempty (Σ expected, PLift (DemandNode.expectedPoints m owner = .ok expected) ×
          DemandPlanApprovals m owner plan expected), True := by
  cases hindexed : deriveModuleDemandIndexed m with
  | error err =>
    simp [deriveModuleDemand, hindexed] at hderive
    cases hderive
  | ok indexed =>
    simp only [deriveModuleDemand, hindexed] at hderive
    have hplans : indexed.entries.map (fun entry => entry.2.points) = plans := by
      change Except.map (fun plans => plans.entries.map (fun entry => entry.2.points))
        (.ok indexed) = .ok plans at hderive
      injection hderive with hplans
    refine ⟨?_, True.intro⟩
    intro owner plan hownerPlan
    have hselected : (indexed.entries.map (fun entry => entry.2.points))[owner]? = some plan := by
      rw [hplans]
      exact hownerPlan
    have hselected' : (indexed.entries[owner]?).map (fun entry => entry.2.points) = some plan := by
      simpa only [Array.getElem?_map] using hselected
    cases hentry : indexed.entries[owner]? with
    | none => simp [hentry] at hselected'
    | some entry =>
      have hpoints : entry.2.points = plan := by
        simpa [hentry] using hselected'
      have hentryOwner : entry.1 = owner := indexed.ownerAt owner entry hentry
      cases hentryOwner
      cases hpoints
      exact ⟨⟨entry.2.expected, ⟨entry.2.expectedWalk⟩, entry.2.approvals⟩⟩

def checkModuleDemand (m : Module) : V Unit := do
  let _ ← deriveModuleDemand m
  pure ()

/-- Successful demand checking is backed by a concrete derived plan. -/
theorem deriveModuleDemand_ok_of_checkModuleDemand (m : Module)
    (h : checkModuleDemand m = .ok ()) :
    ∃ plans, deriveModuleDemand m = .ok plans := by
  change (fun _ => ()) <$> deriveModuleDemand m = .ok () at h
  cases hd : deriveModuleDemand m with
  | error e =>
    simp [hd] at h
    cases h
  | ok plans => exact ⟨plans, rfl⟩

/-- Successful checking yields plans aligned with their owner roots and traces. -/
theorem deriveModuleDemand_ok_wellFormed (m : Module)
    (h : checkModuleDemand m = .ok ()) :
    ∃ plans, deriveModuleDemand m = .ok plans ∧ PlansWellFormed m plans := by
  unfold checkModuleDemand at h
  cases hd : deriveModuleDemandIndexed m with
  | error err =>
    simp [deriveModuleDemand, hd] at h
    cases h
  | ok indexed =>
    let plans := indexed.entries.map fun plan => plan.2.points
    refine ⟨plans, ?_, ?_⟩
    · simp only [deriveModuleDemand, hd]
      rfl
    · constructor
      · simpa [plans] using indexed.size_eq
      · intro owner plan hplan
        have hsource : ∃ source, indexed.entries[owner]? = some source ∧ source.2.points = plan := by
          cases hentry : indexed.entries[owner]? with
          | none => simp [plans, hentry] at hplan
          | some source =>
            simp [plans, hentry] at hplan
            exact ⟨source, rfl, hplan⟩
        obtain ⟨source, hentry, hpoints⟩ := hsource
        have howner : source.1 = owner := indexed.ownerAt owner source hentry
        cases howner
        subst plan
        constructor
        · intro a b ha hb hpath hphase
          exact source.2.index.uniquePathPhase a b ha hb hpath hphase
        · constructor
          · intro point hpoint
            exact source.2.sourceAndPhase point hpoint
          · constructor
            · intro expected hexpected
              rcases hexpected with ⟨expectedPoints, hwalk, hmem⟩
              rw [source.2.expectedWalk] at hwalk
              cases hwalk
              exact source.2.expectedCoverage expected hmem
            · intro point hpoint
              obtain ⟨expected, hmem, hpath, hphase, hsame⟩ :=
                source.2.expectedObservedCoverage point hpoint
              refine ⟨expected, ⟨source.2.expected, source.2.expectedWalk, hmem⟩,
                ?_, ?_, hsame⟩
              · exact hpath.symm
              · exact hphase.symm

theorem deriveModuleDemand_unique_of_checkModuleDemand (m : Module)
    (h : checkModuleDemand m = .ok ()) :
    ∃ (plans : Array (Array DemandPoint)), deriveModuleDemand m = .ok plans ∧
      ∀ (owner : Nat) (plan : Array DemandPoint),
        plans[owner]? = some plan → DemandPathPhaseUnique plan := by
  unfold checkModuleDemand at h
  cases hd : deriveModuleDemandIndexed m with
  | error e =>
    simp [deriveModuleDemand, hd] at h
    cases h
  | ok indexed =>
    let plans := indexed.entries.map fun plan => plan.2.points
    refine ⟨plans, ?_, ?_⟩
    · simp only [deriveModuleDemand, hd]
      rfl
    · intro owner plan hplan
      cases hi : indexed.entries[owner]? with
      | none => simp [plans, hi] at hplan
      | some source =>
        simp [plans, hi] at hplan
        subst plan
        intro a b ha hb hpath hphase
        exact source.2.index.uniquePathPhase a b ha hb hpath hphase

end Goose.Core
