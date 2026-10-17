import Goose.Lower.Validation.StorageWalkFlowFork
import Goose.Lower.Validation.ScopeGraph

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def StorageWalkEntriesAgree (entries : Array (Option (List ScopeId)))
    (stacks : BlockId → List ScopeId) : Prop :=
  ∀ block stack, entries[block]? = some (some stack) → stack = stacks block

theorem recordScopeSuccessor_storage (out : List ScopeId)
    (state : Array (Option (List ScopeId)) × List BlockId × ScopeWalk) (target : BlockId) :
    (recordScopeSuccessor out state target).2.2.storage = state.2.2.storage := by
  cases state with
  | mk entries state =>
    cases state with
    | mk pending walk =>
      cases found : entries[target]? with
      | none => simp [recordScopeSuccessor, found]
      | some previous =>
        cases previous with
        | none => simp [recordScopeSuccessor, found]
        | some stack =>
          cases equality : (stack == out) <;> cases join : walk.join <;>
            simp [recordScopeSuccessor, found, equality, ScopeWalk.noteJoin, join]

theorem recordScopeSuccessors_storage {entries : Array (Option (List ScopeId))}
    (pending : List BlockId) (walk : ScopeWalk) (out : List ScopeId) (targets : List BlockId) :
    (targets.foldl (recordScopeSuccessor out) (entries, pending, walk)).2.2.storage = walk.storage := by
  induction targets generalizing entries pending walk with
  | nil => rfl
  | cons target targets ih =>
    simp only [List.foldl_cons]
    let first := recordScopeSuccessor out (entries, pending, walk) target
    have rest := @ih first.1 first.2.1 first.2.2
    have one := recordScopeSuccessor_storage out (entries, pending, walk) target
    change (List.foldl (recordScopeSuccessor out) first targets).2.2.storage = walk.storage
    rw [rest]
    exact one

structure StorageWalkGraph (func : Func) where
  entry : BlockId → List ScopeId
  exit : BlockId → List ScopeId
  initial : entry 0 = []
  trace : ∀ block body, func.blocks[block]? = some body →
    StorageWalkTrace func.slots (entry block) body.insts (exit block)
  edge : ∀ block body, func.blocks[block]? = some body →
    ∀ target ∈ body.terms.flatMap Term.successors, entry target = exit block

theorem StorageWalkGraph.go_preserves_storage {func : Func} (graph : StorageWalkGraph func)
    (fuel : Nat) (pending : List BlockId) (entries : Array (Option (List ScopeId)))
    (walk : ScopeWalk) (agree : StorageWalkEntriesAgree entries graph.entry) :
    (walkScopes.go func fuel pending entries walk).storage = walk.storage := by
  induction fuel generalizing pending entries walk with
  | zero => rfl
  | succ fuel ih =>
    cases pending with
    | nil => rfl
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
            have nextAgree := recordScopeSuccessors_preserves agree pending
              (walkBlock func block body (graph.entry block) walk).2 (graph.exit block)
              (body.terms.flatMap Term.successors)
              (graph.edge block body bodyLookup)
            simp only [localWalk.1]
            let state := (body.terms.flatMap Term.successors).foldl
              (recordScopeSuccessor (graph.exit block))
              (entries, pending, (walkBlock func block body (graph.entry block) walk).2)
            change (walkScopes.go func fuel state.2.1 state.1 state.2.2).storage = walk.storage
            have rest := ih state.2.1 state.1 state.2.2 nextAgree.1
            have nextStorage : state.2.2.storage =
                (walkBlock func block body (graph.entry block) walk).2.storage := by
              dsimp [state]
              exact recordScopeSuccessors_storage pending
                (walkBlock func block body (graph.entry block) walk).2 (graph.exit block)
                (body.terms.flatMap Term.successors)
            exact rest.trans (nextStorage.trans localWalk.2)


theorem StorageWalkGraph.walkScopes_storage {func : Func} (graph : StorageWalkGraph func)
    (label : String) : (walkScopes label func).storage = none := by
  have agree : StorageWalkEntriesAgree
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
  have result := graph.go_preserves_storage (func.blocks.size + 1) [0]
    ((Array.replicate func.blocks.size none).set! 0 (some [])) {} agree
  simp only [Goose.GIR.walkScopes]
  rw [result]
  rfl

def StorageWalkBuilder.finish {slots : Array Slot}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (builder : StorageWalkBuilder slots entry exit before) (initial : entry 0 = [])
    (edges : ∀ block body, before.blocks[block]? = some body →
      ∀ target ∈ (GIR.Block.mk body.params body.insts.toList).terms.flatMap Term.successors,
        entry target = exit block)
    (func : Func) (slotTable : func.slots = slots)
    (blocks : func.blocks = finishBlocks before.blocks) : StorageWalkGraph func := by
  refine ⟨entry, exit, initial, ?_, ?_⟩
  · intro block body lookup
    rw [blocks] at lookup
    simp only [finishBlocks, Array.getElem?_map] at lookup
    cases beforeLookup : before.blocks[block]? with
    | none => simp [beforeLookup] at lookup
    | some beforeBody =>
      simp only [beforeLookup, Option.map_some, Option.some.injEq] at lookup
      subst body
      rw [slotTable]
      exact builder.traces block beforeBody beforeLookup
  · intro block body lookup target member
    rw [blocks] at lookup
    simp only [finishBlocks, Array.getElem?_map] at lookup
    cases beforeLookup : before.blocks[block]? with
    | none => simp [beforeLookup] at lookup
    | some beforeBody =>
      simp only [beforeLookup, Option.map_some, Option.some.injEq] at lookup
      subst body
      exact edges block beforeBody beforeLookup target member

end Goose.Lower.Validation
