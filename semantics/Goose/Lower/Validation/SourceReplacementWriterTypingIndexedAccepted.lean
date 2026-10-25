import Goose.Lower.Validation.SourceReplacementWriterTypingIndexedStatements
import Goose.Lower.Validation.SourceReplacementWriterTypingIndexedBlocks
import Goose.Lower.Validation.SourceReplacementCallContentsApartVisibility

namespace Goose.Lower.Validation.SourceReplacementWriterTyping

open Goose.Core Goose.Core.Sound SourceReplacementLexicalWriters SourceCanonicalRootFloors

theorem NodeTyped.indexed_child {env : TEnv} {parent child : DemandNode} {index : Nat}
    (typed : NodeTyped env parent) (row : parent.child? index = some child) :
    ∃ after, IndexedChildContext env parent index child after ∧ NodeTyped after child := by
  cases typed with
  | expression source => exact expression_indexed_child source row
  | sliceReference source => exact slice_reference_indexed_child source row
  | place source => exact place_indexed_child source row
  | view source => exact view_indexed_child source row
  | bound source => exact bound_indexed_child source row
  | statement active source => exact statement_indexed_child source row
  | block source => exact block_indexed_child source row

private theorem own_keys_subset (node : DemandNode) : ownScopeKeys node ⊆ sourceNodeScopeKeys node := by
  rw [scope_keys_children]
  exact fun _ member => List.mem_append_left _ member

private theorem indexed_origin_root {env after : TEnv} {parent child : DemandNode} {index found : Nat}
    (context : IndexedChildContext env parent index child after) (row : parent.child? index = some child)
    (member : found ∈ after.visible) :
    found ∈ env.visible ∨ ∃ localVar, env.vars[found]? = some localVar ∧ localVar.scope ∈ sourceNodeScopeKeys parent := by
  rcases context.visibleOrigin found member with previous | ⟨localVar, variableAt, declaredScope⟩
  · exact Or.inl previous
  · refine Or.inr ⟨localVar, variableAt, ?_⟩
    rcases List.mem_append.mp declaredScope with own | nested
    · exact own_keys_subset parent own
    · exact child_keys_subset row (own_keys_subset child nested)

theorem NodeTyped.at_path_context {module : Core.Module} {plans : Array (Array DemandPoint)}
    {pc : PlanContext module plans} {env : TEnv} {root node : DemandNode} {path front stack : List Nat}
    (typed : NodeTyped env root) (source : DemandNodeAt root path node)
    (context : NodeContext pc front root root.primaryPhase) (active : context.ActiveMatches env)
    (scopesEq : env.scopes = stack.reverse)
    (visible : StorageWalkVisible env (ownScopeKeys root ++ stack)) :
    ∃ after scopes, ∃ selected : NodeContext pc (front ++ path) node node.primaryPhase,
      lexicalScopes? root path = some scopes ∧ after.mod = env.mod ∧ after.vars = env.vars ∧ after.impl = env.impl ∧
      after.scopes = (stack ++ scopes).reverse ∧ StorageWalkVisible after (ownScopeKeys node ++ stack ++ scopes) ∧
      NodeTyped after node ∧ selected.ActiveMatches after ∧
      (∀ found, found ∈ after.visible → found ∈ env.visible ∨
        ∃ localVar, env.vars[found]? = some localVar ∧ localVar.scope ∈ sourceNodeScopeKeys root) := by
  induction source generalizing env front stack with
  | here node =>
    rw [List.append_nil]
    exact ⟨env, [], context, rfl, rfl, rfl, rfl, by simpa only [List.append_nil] using scopesEq,
      by simpa only [List.append_nil] using visible, typed, active,
      fun found member => Or.inl member⟩
  | @child parent child node index path next remaining ih =>
    obtain ⟨middle, childContext, childTyped⟩ := typed.indexed_child next
    have phase : DemandNodeHasPhase child child.primaryPhase := by
      cases child <;> simp [DemandNodeHasPhase, DemandNode.primaryPhase, DemandNode.phaseMatches]
    let transition := context.child rfl index child child.primaryPhase next phase
    have middleActive : transition.context.ActiveMatches middle := by
      intro found
      change found ∈ transition.context.expected.frame.active ↔ found ∈ middle.visible
      rw [transition.expectedFrameEq, DemandNode.phaseFrame_active transition.phaseFrameEq,
        DemandNode.childFrame_active transition.childFrameEq]
      exact (parent.visibleForChild_mem_congr index active found).trans (childContext.visibleMatches found).symm
    have middleScopes : middle.scopes = (stack ++ ownScopeKeys parent).reverse := by
      rw [childContext.scopesEq, scopesEq, List.reverse_append]
    have middleVisible : StorageWalkVisible middle (ownScopeKeys child ++ (stack ++ ownScopeKeys parent)) := by
      simpa only [List.append_assoc] using childContext.visible stack visible
    obtain ⟨after, scopes, selected, lookup, moduleEq, varsEq, implEq, finalScopes, finalVisible,
      finalTyped, finalActive, origin⟩ := ih childTyped transition.context middleActive middleScopes middleVisible
    have pathEq : (front ++ [index]) ++ path = front ++ index :: path := by simp [List.append_assoc]
    rw [← pathEq]
    refine ⟨after, ownScopeKeys parent ++ scopes, selected, ?_, moduleEq.trans childContext.moduleEq,
      varsEq.trans childContext.varsEq, implEq.trans childContext.implEq, ?_, ?_, finalTyped, finalActive, ?_⟩
    · simp only [lexicalScopes?, next, bind, Option.bind, lookup, pure]
    · simpa only [List.append_assoc] using finalScopes
    · simpa only [List.append_assoc] using finalVisible
    · intro found member
      rcases origin found member with previous | ⟨localVar, row, declaredScope⟩
      · exact indexed_origin_root childContext next previous
      · exact Or.inr ⟨localVar, by simpa only [childContext.varsEq] using row, child_keys_subset next declaredScope⟩

private theorem implementation_parameter_visible {module : Core.Module} {implementation : Impl}
    {index : ImplId} (accepted : Core.validate module = .ok ())
    (implementationAt : module.impls[index]? = some implementation) :
    ∀ found, found ∈ (implEnv module implementation).visible ↔
      found ∈ implementation.params.toList.map (·.var) := by
  intro found
  change found ∈ List.range implementation.params.size ↔ found ∈ implementation.params.toList.map (·.var)
  constructor
  · intro member
    have bounded := List.mem_range.mp member
    let parameter := implementation.params[found]
    have row : implementation.params[found]? = some parameter := Array.getElem?_eq_getElem bounded
    exact List.mem_map.mpr ⟨parameter, List.mem_of_getElem? (by simpa using row),
      (validate_modOk module accepted).impl _ implementation implementationAt |>.params found parameter row |>.1⟩
  · intro member
    obtain ⟨parameter, inParameters, variableEq⟩ := List.mem_map.mp member
    obtain ⟨position, row⟩ := List.mem_iff_getElem?.mp inParameters
    have parameterAt : implementation.params[position]? = some parameter := by simpa using row
    have source := (validate_modOk module accepted).impl _ implementation implementationAt |>.params position parameter parameterAt
    rw [source.1] at variableEq
    subst found
    exact List.mem_range.mpr (Array.getElem?_eq_some_iff.mp parameterAt).1

theorem accepted_context_node_typed_active {module : Core.Module} {context : Context} {implementation : Impl}
    {contextIndex : ContextId} (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[contextIndex]? = some context)
    (implementationAt : module.impls[context.impl]? = some implementation)
    {plans : Array (Array DemandPoint)} {pc : PlanContext module plans} (ownerEq : pc.owner = contextIndex)
    {path : List Nat} {node : DemandNode} (source : DemandNodeAt (.block implementation.body) path node)
    (actual : NodeContext pc path node node.primaryPhase) :
    ∃ env scopes, lexicalScopes? (.block implementation.body) path = some scopes ∧
      env.mod = module ∧ env.vars = implementation.vars ∧ env.impl = some implementation ∧
      env.scopes = scopes.reverse ∧ StorageWalkVisible env (ownScopeKeys node ++ scopes) ∧
      NodeTyped env node ∧ actual.ActiveMatches env := by
  have checked := validate_implementation_checks accepted
    (Array.mem_toList_iff.mpr (Array.mem_of_getElem? implementationAt))
  obtain ⟨type, finish, typed, result⟩ := (checkImpl_ok module implementation checked).body
  have bounded := (Array.getElem?_eq_some_iff.mp contextAt).1
  have rootAt : demandRoot? module pc.owner = some (.block implementation.body) := by
    have contextEq := (Array.getElem?_eq_some_iff.mp contextAt).2
    simp [demandRoot?, ownerEq, bounded, contextEq, implementationAt]
  let initial := NodeContext.atRoot pc (.block implementation.body) rootAt
  have initialActive : initial.ActiveMatches (implEnv module implementation) := by
    intro found
    change found ∈ initial.expected.frame.active ↔ found ∈ (implEnv module implementation).visible
    rw [NodeContext.atRoot_active, ownerEq]
    simp only [demandInitialActive, bounded, ite_true, contextAt, implementationAt]
    exact (implementation_parameter_visible accepted implementationAt found).symm
  have initialVisible : StorageWalkVisible (implEnv module implementation) (ownScopeKeys (.block implementation.body) ++ []) := by
    have visible := storageWalk_impl_visible checked []
    cases bodyAt : implementation.body
    simpa [ownScopeKeys, bodyAt, Core.Block.scope] using visible
  obtain ⟨env, scopes, selected, lookup, moduleEq, varsEq, implEq, finalScopes, finalVisible,
      finalTyped, finalActive, origin⟩ :=
    NodeTyped.at_path_context (.block typed) source initial initialActive (stack := []) rfl initialVisible
  refine ⟨env, scopes, lookup, moduleEq, varsEq, implEq, ?_, ?_, finalTyped, ?_⟩
  · simpa only [List.nil_append] using finalScopes
  · simpa only [List.append_nil, List.nil_append] using finalVisible
  · intro found
    exact (NodeContext.active_matches actual selected found).trans (finalActive found)

#print axioms NodeTyped.indexed_child
#print axioms NodeTyped.at_path_context
#print axioms accepted_context_node_typed_active

end Goose.Lower.Validation.SourceReplacementWriterTyping
