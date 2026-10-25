import Goose.Lower.Validation.ScopeWalk

namespace Goose.Lower.Validation

open Goose.GIR

def ScopeEntriesAgree (entries : Array (Option (List ScopeId)))
    (stacks : BlockId → List ScopeId) : Prop :=
  ∀ block stack, entries[block]? = some (some stack) → stack = stacks block

def recordScopeSuccessor (out : List ScopeId)
    (state : Array (Option (List ScopeId)) × List BlockId × ScopeWalk) (target : BlockId) :=
  let (entries, pending, walk) := state
  match entries[target]? with
  | some none => (entries.set! target (some out), target :: pending, walk)
  | some (some stack) =>
    if stack == out then (entries, pending, walk)
    else (entries, pending, walk.noteJoin s!"block {target} is reached with different scopes entered")
  | none => (entries, pending, walk)

theorem recordScopeSuccessor_preserves {entries : Array (Option (List ScopeId))}
    {stacks : BlockId → List ScopeId} (agree : ScopeEntriesAgree entries stacks)
    (pending : List BlockId) (walk : ScopeWalk) (out : List ScopeId) (target : BlockId)
    (edge : stacks target = out) :
    let next := recordScopeSuccessor out (entries, pending, walk) target
    ScopeEntriesAgree next.1 stacks ∧ next.2.2.scopes = walk.scopes ∧
      next.2.2.join = walk.join := by
  simp only [recordScopeSuccessor]
  cases found : entries[target]? with
  | none => exact ⟨agree, by trivial, by trivial⟩
  | some previous =>
    cases previous with
    | none =>
      refine ⟨?_, by trivial, by trivial⟩
      intro block stack lookup
      simp only [Array.set!, Array.getElem?_setIfInBounds] at lookup
      split at lookup
      · rename_i same
        subst block
        split at lookup
        · simp only [Option.some.injEq] at lookup
          cases lookup
          exact edge.symm
        · cases lookup
      · exact agree block stack lookup
    | some stack =>
      have equality : stack = out := (agree target stack found).trans edge
      simp only [equality, beq_self_eq_true, ite_true]
      exact ⟨agree, by trivial, by trivial⟩

theorem recordScopeSuccessors_preserves {entries : Array (Option (List ScopeId))}
    {stacks : BlockId → List ScopeId} (agree : ScopeEntriesAgree entries stacks)
    (pending : List BlockId) (walk : ScopeWalk) (out : List ScopeId) (targets : List BlockId)
    (edges : ∀ target ∈ targets, stacks target = out) :
    let next := targets.foldl (recordScopeSuccessor out) (entries, pending, walk)
    ScopeEntriesAgree next.1 stacks ∧ next.2.2.scopes = walk.scopes ∧
      next.2.2.join = walk.join := by
  induction targets generalizing entries pending walk with
  | nil => exact ⟨agree, by trivial, by trivial⟩
  | cons target targets ih =>
    have one := recordScopeSuccessor_preserves agree pending walk out target (edges target (by simp))
    have rest := ih one.1
      (recordScopeSuccessor out (entries, pending, walk) target).2.1
      (recordScopeSuccessor out (entries, pending, walk) target).2.2
      (fun next member => edges next (by simp [member]))
    exact ⟨rest.1, rest.2.1.trans one.2.1, rest.2.2.trans one.2.2⟩

structure ScopeGraph (func : Func) where
  entry : BlockId → List ScopeId
  exit : BlockId → List ScopeId
  initial : entry 0 = []
  trace : ∀ block body, func.blocks[block]? = some body →
    ScopeTrace func.scopes (entry block) body.insts (exit block)
  edge : ∀ block body, func.blocks[block]? = some body →
    ∀ target ∈ body.terms.flatMap Term.successors, entry target = exit block

theorem ScopeGraph.go_preserves {func : Func} (graph : ScopeGraph func)
    (fuel : Nat) (pending : List BlockId) (entries : Array (Option (List ScopeId)))
    (walk : ScopeWalk) (agree : ScopeEntriesAgree entries graph.entry) :
    (walkScopes.go func fuel pending entries walk).scopes = walk.scopes ∧
      (walkScopes.go func fuel pending entries walk).join = walk.join := by
  induction fuel generalizing pending entries walk with
  | zero => exact ⟨rfl, rfl⟩
  | succ fuel ih =>
    cases pending with
    | nil => exact ⟨rfl, rfl⟩
    | cons block pending =>
      simp only [walkScopes.go]
      cases bodyLookup : func.blocks[block]? with
      | none => exact ih pending entries walk agree
      | some body =>
        cases stackLookup : entries[block]? with
        | none => exact ih pending entries walk agree
        | some previous =>
          cases previous with
          | none => exact ih pending entries walk agree
          | some stack =>
            have same := agree block stack stackLookup
            subst stack
            have localWalk := (graph.trace block body bodyLookup).walkBlock block body.params walk
            have next := recordScopeSuccessors_preserves agree pending
              (walkBlock func block body (graph.entry block) walk).2 (graph.exit block)
              (body.terms.flatMap Term.successors) (graph.edge block body bodyLookup)
            simp only [localWalk.1]
            change let nextState := ((body.terms.flatMap Term.successors).foldl
              (recordScopeSuccessor (graph.exit block))
              (entries, pending, (walkBlock func block body (graph.entry block) walk).2));
              (walkScopes.go func fuel nextState.2.1 nextState.1 nextState.2.2).scopes = walk.scopes ∧
                (walkScopes.go func fuel nextState.2.1 nextState.1 nextState.2.2).join = walk.join
            let state := (body.terms.flatMap Term.successors).foldl
              (recordScopeSuccessor (graph.exit block))
              (entries, pending, (walkBlock func block body (graph.entry block) walk).2)
            have rest := ih state.2.1 state.1 state.2.2 next.1
            exact ⟨rest.1.trans (next.2.1.trans localWalk.2.1),
              rest.2.trans (next.2.2.trans localWalk.2.2)⟩

theorem ScopeGraph.walkScopes {func : Func} (graph : ScopeGraph func) (label : String) :
    (walkScopes label func).scopes = none := by
  have agree : ScopeEntriesAgree
      ((Array.replicate func.blocks.size none).set! 0 (some [])) graph.entry := by
    intro block stack lookup
    simp only [Array.set!, Array.getElem?_setIfInBounds, Array.getElem?_replicate] at lookup
    split at lookup
    · rename_i same
      subst block
      split at lookup
      · simp only [Option.some.injEq] at lookup
        cases lookup
        exact graph.initial.symm
      · cases lookup
    · split at lookup <;> cases lookup
  have result := graph.go_preserves (func.blocks.size + 1) [0]
    ((Array.replicate func.blocks.size none).set! 0 (some [])) {} agree
  simp only [Goose.GIR.walkScopes, result.1, result.2]
  rfl

end Goose.Lower.Validation
