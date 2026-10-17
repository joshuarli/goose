import Goose.Lower.Validation.SourceCanonicalRootFloorsWriteScopes

set_option Elab.async false
set_option maxHeartbeats 2000000

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core

def sourceChildRootWrites (env : PEnv) (children : List (Option DemandNode)) : List SourceRootWrite :=
  children.flatMap fun
    | some node => sourceNodeRootWrites env node
    | none => []

private theorem sourceChildRootWrites_scopes (env : PEnv) (scopes : List Nat)
    (children : List (Option DemandNode)) :
    sourceChildRootWrites { env with scopes := scopes } children = sourceChildRootWrites env children := by
  unfold sourceChildRootWrites
  apply congrArg (fun action : Option DemandNode → List SourceRootWrite => children.flatMap action)
  funext child
  cases child with
  | none => rfl
  | some node => exact sourceNodeRootWrites_scopes env scopes node

def sourceNodeOwnRootWrites (env : PEnv) : DemandNode → List SourceRootWrite
  | .expression (.ifE _ yes no) => [(sourceBlockScope yes,
      unionRoots (collectSourceBlockRoots env yes #[]).1 (collectSourceBlockRoots env no #[]).1)]
  | _ => []

private theorem sourceArgumentRootWrites_children (env : PEnv) (arguments : List Arg) :
    sourceArgumentRootWrites env arguments = sourceChildRootWrites env (arguments.map fun
      | .byVal expression => some (.expression expression)
      | .byRef _ place => some (.place place)) := by
  induction arguments with
  | nil => rfl
  | cons head rest ih =>
    simp only [sourceChildRootWrites, sourceNodeRootWrites] at ih
    cases head <;> rw [sourceArgumentRootWrites.eq_def] <;>
      simp only [List.map_cons, sourceChildRootWrites, List.flatMap_cons,
        sourceNodeRootWrites, ← ih]

private theorem sourceExprListRootWrites_children (env : PEnv) (expressions : List Expr) :
    sourceExprListRootWrites env expressions =
      sourceChildRootWrites env (expressions.map (some ∘ DemandNode.expression)) := by
  induction expressions with
  | nil => rfl
  | cons expression rest ih =>
    simp only [sourceChildRootWrites, sourceNodeRootWrites] at ih
    rw [sourceExprListRootWrites.eq_def]
    simp only [List.map_cons, sourceChildRootWrites, List.flatMap_cons,
      Function.comp_apply, sourceNodeRootWrites, ← ih]

private theorem sourceStmtListRootWrites_children (env : PEnv) (statements : List Stmt) :
    sourceStmtListRootWrites env statements =
      sourceChildRootWrites env (statements.map (some ∘ DemandNode.statement)) := by
  induction statements with
  | nil => rfl
  | cons statement rest ih =>
    simp only [sourceChildRootWrites, sourceNodeRootWrites] at ih
    rw [sourceStmtListRootWrites.eq_def]
    simp only [List.map_cons, sourceChildRootWrites, List.flatMap_cons,
      Function.comp_apply, sourceNodeRootWrites, ← ih]

private theorem sourcePrintRootWrites_children (env : PEnv) (arguments : List PrintArg) :
    sourcePrintRootWrites env arguments = sourceChildRootWrites env (arguments.map fun
      | .text _ => none
      | .expr expression => some (.expression expression)) := by
  induction arguments with
  | nil => rfl
  | cons head rest ih =>
    simp only [sourceChildRootWrites, sourceNodeRootWrites] at ih
    cases head <;> rw [sourcePrintRootWrites.eq_def] <;>
      simp only [List.map_cons, sourceChildRootWrites, List.flatMap_cons,
        sourceNodeRootWrites, List.nil_append, ← ih]

local macro "source_node_writes_finish " equation:Lean.Parser.Tactic.rwRule : tactic =>
  `(tactic| (
    simp only [sourceNodeRootWrites, DemandNode.children, sourceNodeOwnRootWrites]
    rw [$equation]
    all_goals try simp only [sourceArgumentRootWrites_children, sourceExprListRootWrites_children,
      sourceStmtListRootWrites_children, sourcePrintRootWrites_children]
    all_goals try simp only [sourceChildRootWrites_scopes]
    all_goals try simp only [sourceChildRootWrites, List.flatMap_cons, List.flatMap_nil, List.flatMap_append,
      sourceNodeRootWrites, Function.comp_apply, List.nil_append, List.append_nil,
      List.append_assoc, Option.map_none, Option.map_some,
      sourceExprRootWrites_scopes, sourceStmtListRootWrites_scopes]
    all_goals rfl))

theorem sourceNodeRootWrites_children (env : PEnv) (node : DemandNode) :
    sourceNodeRootWrites env node =
      sourceChildRootWrites env node.children ++ sourceNodeOwnRootWrites env node := by
  cases node with
  | expression expression =>
    cases expression
    all_goals source_node_writes_finish sourceExprRootWrites.eq_def
  | place place =>
    cases place
    all_goals source_node_writes_finish sourcePlaceRootWrites.eq_def
  | view view =>
    cases view
    all_goals source_node_writes_finish sourceViewRootWrites.eq_def
  | bound bound =>
    cases bound
    all_goals source_node_writes_finish sourceBoundRootWrites.eq_def
  | statement statement =>
    cases statement
    case' resize place count fill origin => cases fill
    case' ifS condition yes no origin => cases no
    case' ret value origin => cases value
    all_goals source_node_writes_finish sourceStmtRootWrites.eq_def
  | block block =>
    cases block with
    | mk scope statements value =>
      cases value
      all_goals source_node_writes_finish sourceBlockRootWrites.eq_def

theorem sourceNodeRootWrites_child (env : PEnv) (parent child : DemandNode)
    (index : Nat) (present : parent.child? index = some child) :
    ∀ entry ∈ sourceNodeRootWrites env child, entry ∈ sourceNodeRootWrites env parent := by
  intro entry member
  rw [sourceNodeRootWrites_children]
  apply List.mem_append_left
  unfold sourceChildRootWrites
  apply List.mem_flatMap.mpr
  refine ⟨some child, ?_, member⟩
  exact List.mem_of_getElem? (Option.join_eq_some_iff.mp present)

theorem sourceNodeRootWrites_at (env : PEnv) {root node : DemandNode} {path : List Nat}
    (location : DemandNodeAt root path node) :
    ∀ entry ∈ sourceNodeRootWrites env node, entry ∈ sourceNodeRootWrites env root := by
  induction location with
  | here => exact fun _ member => member
  | @child parent child node index path present location ih =>
    exact fun entry member => sourceNodeRootWrites_child env parent child index present entry (ih entry member)

end Goose.Lower.Validation.SourceCanonicalRootFloors
