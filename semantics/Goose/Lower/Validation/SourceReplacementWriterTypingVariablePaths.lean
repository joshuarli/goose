import Goose.Lower.Validation.SourceReplacementWriterTypingRhsVisibility
import Goose.Lower.Validation.SourceReplacementWriterLedgerInductionSyntax

namespace Goose.Lower.Validation.SourceReplacementWriterTyping

open Goose.Core Goose.Core.Sound SourceReplacementLexicalWriters SourceCanonicalRootFloors

theorem variable_or_child {node : DemandNode} {found : VarId} (used : found ∈ node.variables) :
    node = .place (.var found) ∨ ∃ child, some child ∈ node.children ∧ found ∈ child.variables := by
  cases node with
  | expression expression =>
    cases expression with
    | call function arguments origin =>
      simp only [DemandNode.variables, Expr.variables] at used
      obtain ⟨argument, member, used⟩ := List.mem_flatMap.mp used
      cases argument with
      | byVal expression =>
        exact Or.inr ⟨.expression expression, List.mem_map.mpr ⟨.byVal expression, member, rfl⟩, by simpa [DemandNode.variables, Arg.variables, PrintArg.variables] using used⟩
      | byRef mutability place =>
        exact Or.inr ⟨.place place, List.mem_map.mpr ⟨.byRef mutability place, member, rfl⟩, by simpa [DemandNode.variables, Arg.variables, PrintArg.variables] using used⟩
    | _ =>
      simp_all [DemandNode.children, DemandNode.variables, Expr.variables,
        List.mem_flatMap, List.mem_map] <;>
      grind [DemandNode.variables, Expr.variables, Arg.variables, Stmt.variables, PrintArg.variables, Block.variables]
  | place place =>
    cases place <;> simp_all [DemandNode.children, DemandNode.variables, Place.variables] <;>
      grind [DemandNode.variables]
  | view view =>
    cases view <;> simp_all [DemandNode.children, DemandNode.variables, View.variables] <;>
      grind [DemandNode.variables]
  | bound bound =>
    cases bound <;> simp_all [DemandNode.children, DemandNode.variables, Bound.variables] <;>
      grind [DemandNode.variables]
  | statement statement =>
    cases statement with
    | resize owner size fill origin =>
      cases fill <;> simp_all [DemandNode.children, DemandNode.variables, Stmt.variables] <;>
        grind [DemandNode.variables]
    | ifS condition yes no origin =>
      cases no <;> simp_all [DemandNode.children, DemandNode.variables, Stmt.variables] <;>
        grind [DemandNode.variables]
    | ret value origin =>
      cases value <;> simp_all [DemandNode.children, DemandNode.variables, Stmt.variables] <;>
        grind [DemandNode.variables]
    | print arguments origin =>
      simp only [DemandNode.variables, Stmt.variables] at used
      obtain ⟨argument, member, used⟩ := List.mem_flatMap.mp used
      cases argument with
      | text text => simp [PrintArg.variables] at used
      | expr expression =>
        exact Or.inr ⟨.expression expression, List.mem_map.mpr ⟨.expr expression, member, rfl⟩, by simpa [DemandNode.variables, Arg.variables, PrintArg.variables] using used⟩
    | _ =>
      simp_all [DemandNode.children, DemandNode.variables, Stmt.variables] <;> grind [DemandNode.variables, PrintArg.variables]
  | block body =>
    cases body with
    | mk scope statements value =>
      cases value <;> simp_all [DemandNode.children, DemandNode.variables, Block.variables,
        List.mem_flatMap, List.mem_map] <;> grind [DemandNode.variables]

theorem variable_path {node : DemandNode} {found : VarId} (used : found ∈ node.variables) :
    ∃ path, DemandNodeAt node path (.place (.var found)) := by
  rcases variable_or_child used with same | ⟨child, member, childUsed⟩
  · subst node
    exact ⟨[], .here _⟩
  · obtain ⟨index, row⟩ := List.mem_iff_getElem?.mp member
    have childAt : node.child? index = some child := by simp [DemandNode.child?, row]
    obtain ⟨path, source⟩ := variable_path childUsed
    exact ⟨index :: path, .child childAt source⟩
termination_by sizeOf node
decreasing_by exact SourceReplacementWriterLedger.demand_child_size _ _ member

theorem accepted_inactive_rhs_variable_scope {module : Core.Module} {context : Context} {implementation : Impl}
    {contextIndex : ContextId} (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[contextIndex]? = some context)
    (implementationAt : module.impls[context.impl]? = some implementation)
    {path : List Nat} {place : Place} {rhs : Expr} {origin : OriginId}
    (source : DemandNodeAt (.block implementation.body) path (.statement (.assignWhole place rhs origin)))
    (demand : ReplacementDemandContext module contextIndex path place rhs origin)
    {found : VarId} {localVar : LocalVar} (variableAt : implementation.vars[found]? = some localVar)
    (used : found ∈ rhs.variables) (inactive : found ∉ demand.statement.expected.frame.active) :
    localVar.scope ∈ sourceNodeScopeKeys (.expression rhs) := by
  obtain ⟨suffix, variableSource⟩ := variable_path (node := .expression rhs) (by simpa [DemandNode.variables] using used)
  obtain ⟨env, scopes, stackAt, moduleEq, varsEq, implEq, typed, origin⟩ :=
    accepted_rhs_descendant_visible accepted contextAt implementationAt source demand variableSource
  have visible : found ∈ env.visible := by
    cases typed with
    | place source =>
      simp only [Core.tyPlace] at source
      obtain ⟨declared, next, checked, rest⟩ := (st_bind_ok _ _ _ _).mp source
      exact ((varOf_ok _ _ _ _).mp checked).1
  rcases origin found visible with active | ⟨actual, actualAt, fresh⟩
  · exact False.elim (inactive active)
  · have actualRow : implementation.vars[found]? = some actual := by simpa only [varsEq] using actualAt
    have same : actual = localVar := Option.some.inj (actualRow.symm.trans variableAt)
    exact same ▸ fresh

#print axioms variable_or_child
#print axioms variable_path
#print axioms accepted_inactive_rhs_variable_scope

end Goose.Lower.Validation.SourceReplacementWriterTyping
