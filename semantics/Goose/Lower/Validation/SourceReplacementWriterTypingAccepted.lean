import Goose.Lower.Validation.SourceReplacementWriterTypingBlocks

namespace Goose.Lower.Validation.SourceReplacementWriterTyping

open Goose.Core Goose.Core.Sound SourceReplacementLexicalWriters

private theorem child_member {parent child : DemandNode} {index : Nat}
    (source : parent.child? index = some child) : some child ∈ parent.children := by
  unfold DemandNode.child? at source
  cases row : parent.children[index]? with
  | none => simp [row] at source
  | some candidate =>
    cases candidate with
    | none => simp [row] at source
    | some actual =>
      have same : actual = child := by simpa [row] using source
      subst actual
      exact List.mem_of_getElem? row

theorem NodeTyped.at_path {env : TEnv} {root node : DemandNode} {path : List Nat} {stack : List Nat}
    (typed : NodeTyped env root) (source : DemandNodeAt root path node)
    (scopesEq : env.scopes = stack.reverse)
    (visible : StorageWalkVisible env (ownScopeKeys root ++ stack)) :
    ∃ after scopes, lexicalScopes? root path = some scopes ∧
      after.mod = env.mod ∧ after.vars = env.vars ∧ after.impl = env.impl ∧
      after.scopes = (stack ++ scopes).reverse ∧
      StorageWalkVisible after (ownScopeKeys node ++ stack ++ scopes) ∧ NodeTyped after node := by
  induction source generalizing env stack with
  | here node =>
    exact ⟨env, [], rfl, rfl, rfl, rfl, by simpa using scopesEq, by simpa using visible, typed⟩
  | @child parent child node index path next remaining ih =>
    obtain ⟨middle, context, childTyped⟩ := typed.child (child_member next)
    have middleScopes : middle.scopes = (stack ++ ownScopeKeys parent).reverse := by
      rw [context.scopesEq, scopesEq, List.reverse_append]
    have middleVisible : StorageWalkVisible middle (ownScopeKeys child ++ (stack ++ ownScopeKeys parent)) := by
      simpa only [List.append_assoc] using context.visible stack visible
    obtain ⟨after, scopes, lookup, moduleEq, varsEq, implEq, finalScopes, finalVisible, finalTyped⟩ :=
      ih childTyped middleScopes middleVisible
    refine ⟨after, ownScopeKeys parent ++ scopes, ?_, moduleEq.trans context.moduleEq,
      varsEq.trans context.varsEq, implEq.trans context.implEq, ?_, ?_, finalTyped⟩
    · simp only [lexicalScopes?, next, bind, Option.bind, lookup, pure]
    · simpa only [List.append_assoc] using finalScopes
    · simpa only [List.append_assoc] using finalVisible

theorem accepted_implementation_node_typed {module : Core.Module} {implementation : Impl}
    {implementationIndex : ImplId} (accepted : Core.validate module = .ok ())
    (implementationAt : module.impls[implementationIndex]? = some implementation)
    {path : List Nat} {node : DemandNode} (source : DemandNodeAt (.block implementation.body) path node) :
    ∃ env scopes, lexicalScopes? (.block implementation.body) path = some scopes ∧
      env.mod = module ∧ env.vars = implementation.vars ∧ env.impl = some implementation ∧
      env.scopes = scopes.reverse ∧ StorageWalkVisible env (ownScopeKeys node ++ scopes) ∧ NodeTyped env node := by
  have checked := validate_implementation_checks accepted
    (Array.mem_toList_iff.mpr (Array.mem_of_getElem? implementationAt))
  obtain ⟨type, finish, typed, result⟩ := (checkImpl_ok module implementation checked).body
  have visible : StorageWalkVisible (implEnv module implementation) (ownScopeKeys (.block implementation.body) ++ []) := by
    have actual := storageWalk_impl_visible checked []
    cases bodyAt : implementation.body
    simpa [ownScopeKeys, bodyAt, Core.Block.scope] using actual
  obtain ⟨env, scopes, lookup, moduleEq, varsEq, implEq, finalScopes, finalVisible, finalTyped⟩ :=
    NodeTyped.at_path (.block typed) source (stack := []) rfl visible
  refine ⟨env, scopes, lookup, moduleEq, varsEq, implEq, ?_, ?_, finalTyped⟩
  · simpa only [List.nil_append] using finalScopes
  · simpa only [List.append_nil, List.nil_append] using finalVisible

#print axioms NodeTyped.at_path
#print axioms accepted_implementation_node_typed

end Goose.Lower.Validation.SourceReplacementWriterTyping
