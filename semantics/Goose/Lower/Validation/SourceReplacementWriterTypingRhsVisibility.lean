import Goose.Lower.Validation.SourceReplacementWriterTypingIndexedAccepted

namespace Goose.Lower.Validation.SourceReplacementWriterTyping

open Goose.Core Goose.Core.Sound SourceReplacementLexicalWriters SourceCanonicalRootFloors

theorem accepted_rhs_descendant_visible {module : Core.Module} {context : Context} {implementation : Impl}
    {contextIndex : ContextId} (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[contextIndex]? = some context)
    (implementationAt : module.impls[context.impl]? = some implementation)
    {path : List Nat} {place : Place} {rhs : Expr} {origin : OriginId}
    (source : DemandNodeAt (.block implementation.body) path (.statement (.assignWhole place rhs origin)))
    (demand : ReplacementDemandContext module contextIndex path place rhs origin)
    {suffix : List Nat} {node : DemandNode} (descendant : DemandNodeAt (.expression rhs) suffix node) :
    ∃ env scopes, lexicalScopes? (.expression rhs) suffix = some scopes ∧
      env.mod = module ∧ env.vars = implementation.vars ∧ env.impl = some implementation ∧
      NodeTyped env node ∧
      (∀ found, found ∈ env.visible → found ∈ demand.statement.expected.frame.active ∨
        ∃ localVar, implementation.vars[found]? = some localVar ∧ localVar.scope ∈ sourceNodeScopeKeys (.expression rhs)) := by
  obtain ⟨statementEnv, stack, stackAt, moduleEq, varsEq, implEq, scopesEq, visible, typed, active⟩ :=
    accepted_context_node_typed_active accepted contextAt implementationAt demand.owner_eq source demand.statement
  have childAt : (DemandNode.statement (.assignWhole place rhs origin)).child? 1 = some (.expression rhs) := by
    simp [DemandNode.child?, DemandNode.children]
  obtain ⟨rhsEnv, child, rhsTyped⟩ := typed.indexed_child childAt
  have rhsActive : demand.rhsTransition.context.ActiveMatches rhsEnv := by
    intro found
    change found ∈ demand.rhsTransition.context.expected.frame.active ↔ found ∈ rhsEnv.visible
    rw [demand.rhsTransition.expectedFrameEq,
      DemandNode.phaseFrame_active demand.rhsTransition.phaseFrameEq,
      DemandNode.childFrame_active demand.rhsTransition.childFrameEq]
    exact ((DemandNode.statement (.assignWhole place rhs origin)).visibleForChild_mem_congr 1 active found).trans
      (child.visibleMatches found).symm
  have rhsScopes : rhsEnv.scopes = stack.reverse := by
    simpa [ownScopeKeys] using child.scopesEq.trans (congrArg (fun scopes => [] ++ scopes) scopesEq)
  have rhsVisible : StorageWalkVisible rhsEnv (ownScopeKeys (.expression rhs) ++ stack) := by
    simpa [ownScopeKeys] using child.visible stack visible
  obtain ⟨env, scopes, selected, lookup, childModule, childVars, childImpl, finalScopes,
    finalVisible, finalTyped, finalActive, origin⟩ :=
    NodeTyped.at_path_context rhsTyped descendant demand.rhsTransition.context rhsActive rhsScopes rhsVisible
  refine ⟨env, scopes, lookup, childModule.trans (child.moduleEq.trans moduleEq),
    childVars.trans (child.varsEq.trans varsEq), childImpl.trans (child.implEq.trans implEq), finalTyped, ?_⟩
  intro found member
  rcases origin found member with previous | ⟨localVar, row, declaredScope⟩
  · apply Or.inl
    apply (active found).mpr
    exact (child.visibleMatches found).mp previous
  · exact Or.inr ⟨localVar, by simpa only [child.varsEq, varsEq] using row, declaredScope⟩

#print axioms accepted_rhs_descendant_visible

end Goose.Lower.Validation.SourceReplacementWriterTyping
