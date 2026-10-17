import Goose.Lower.Validation.CfgGeneratedEdgeIf

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem edge_scFork_targets (isAnd : Bool) (value : ValueId) (env : LEnv) (before after : LS)
    (result : BlockId × BlockId × ValueId) (run : scFork isAnd value env before = (result, after))
    (checked : BuilderEdgeArguments before)
    (typed : before.vals[value]? = some (some (.data .bool))) :
    EdgeArguments after result.1 [] ∧
      (∀ argument, after.vals[argument]? = some (some (.data .bool)) →
        EdgeArguments after result.2.1 [argument]) ∧
      after.vals[result.2.2]? = some (some (.data .bool)) := by
  have expression : scFork isAnd value = (do
      let (rhs, _) ← newBlock []
      let (join, parameters) ← newBlock [.data .bool]
      emitTerm (if isAnd then .condbr value rhs [] join [value] else .condbr value join [value] rhs [])
      pure (rhs, join, parameters.headD 0)) := by cases isAnd <;> rfl
  rw [expression] at run
  simp only [bind_eq] at run
  obtain ⟨⟨rhs, rhsParams⟩, first, rhsRun, ⟨join, joinParams⟩, second, joinRun,
    ignored, closed, termRun, finished⟩ := run
  rw [pure_run] at finished
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj finished
  obtain ⟨firstExtension, firstChecked⟩ := edge_newBlock0 env before _ first rhsRun checked
  obtain ⟨secondExtension, secondChecked⟩ := edge_newBlock1 (.data .bool) env first _ second joinRun firstChecked
  have rhsEdge := (edge_newBlock0_target rhsRun).extend secondExtension
  have joinEdge := edge_newBlock1_target joinRun (firstExtension.types value (.data .bool) typed)
  have arguments : BuilderTermArguments second
      (if isAnd then .condbr value rhs [] join [value] else .condbr value join [value] rhs []) := by
    cases isAnd
    · exact ⟨joinEdge, rhsEdge⟩
    · exact ⟨rhsEdge, joinEdge⟩
  obtain ⟨lastExtension, lastChecked⟩ := edge_emitTerm_at _ env second closed ignored termRun secondChecked (fun _ => arguments)
  have parameter := lastExtension.types _ _ (edge_newBlock1_parameter joinRun)
  constructor
  · exact rhsEdge.extend lastExtension
  constructor
  · intro argument typed
    rw [newBlock1_run] at joinRun
    obtain ⟨equal, stateEqual⟩ := Prod.mk.inj joinRun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
    subst second
    obtain ⟨body, row, params, _⟩ := lastExtension.blocks.2 first.blocks.size
      ⟨[(first.vals.size, .data .bool)], #[]⟩ (by simp)
    refine ⟨body, row, by simp [params], ?_⟩
    intro pair member
    simp [params] at member
    subst pair
    exact typed
  · exact parameter

theorem generated_edge_shortCircuit_at (env : LEnv) (context : Option LoopCtx)
    (isAnd : Bool) (value : ValueId) {rhs : B ValueId}
    (rhsEdges : GeneratedEdgeRun env context rhs)
    (rhsTyped : ∀ before result after, rhs env before = (result, after) → GeneratedBuilderState before →
      after.cur.isSome = true → after.vals[result]? = some (some (.data .bool)))
    (before after : LS) (result : ValueId)
    (run : shortCircuit isAnd value rhs env before = (result, after))
    (generated : GeneratedBuilderState before) (loop : LoopEdgeArguments context before)
    (checked : BuilderEdgeArguments before)
    (initialTyped : before.cur.isSome = true → before.vals[value]? = some (some (.data .bool))) :
    GeneratedBuilderState after ∧ EdgeExtension before after ∧ BuilderEdgeArguments after := by
  cases current : before.cur with
  | none =>
    rw [shortCircuit, whenLive_none _ _ env current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact ⟨generated, .refl before, checked⟩
  | some block =>
    rw [shortCircuit, whenLive_some _ _ env current] at run
    simp only [bind_eq] at run
    obtain ⟨⟨rhsBlock, join, parameter⟩, forked, forkRun, ignored, selected, selectRun,
      rhsValue, rhsEnd, rhsRun, ignored', closed, closeRun, ignored'', joined, joinRun, finalRun⟩ := run
    rw [pure_run] at finalRun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj finalRun
    have valueTyped := initialTyped (by simp [current])
    obtain ⟨forkExtension, forkChecked⟩ := edge_scFork_at isAnd value env before forked _ forkRun checked valueTyped
    have forkGenerated := generated.scFork isAnd value forkRun
    obtain ⟨rhsEdge, joinEdges, parameterTyped⟩ := edge_scFork_targets isAnd value env before forked _ forkRun checked valueTyped
    have joinEdge := joinEdges parameter parameterTyped
    obtain ⟨selectedGenerated, selectExtension, selectedChecked⟩ :=
      generated_edge_setCur_at (some rhsBlock) env forked selected ignored selectRun forkGenerated forkChecked
        (by intro target same; have equal := Option.some.inj same; simpa [← equal] using rhsEdge.bound)
    have beforeRhs := forkExtension.trans selectExtension
    obtain ⟨rhsGenerated, rhsExtension, rhsChecked⟩ := rhsEdges selected rhsValue rhsEnd rhsRun selectedGenerated
      (loop.extend beforeRhs) selectedChecked
    have throughRhs := selectExtension.trans rhsExtension
    have rhsJoin := joinEdge.extend throughRhs
    have arguments : rhsEnd.cur.isSome = true → BuilderTermArguments rhsEnd (.br join [rhsValue]) := by
      intro live
      obtain ⟨body, row, arity, typed⟩ := rhsJoin
      have oldTyped := throughRhs.types parameter (.data .bool) parameterTyped
      cases params : body.params with
      | nil => simp [params] at arity
      | cons formal rest =>
        have restEmpty : rest = [] := by simpa [params] using arity
        have formalTyped := typed (formal, parameter) (by simp [params, restEmpty])
        rw [oldTyped] at formalTyped
        have sameTy := Option.some.inj (Option.some.inj formalTyped)
        refine ⟨body, row, arity, ?_⟩
        intro pair member
        simp only [params, restEmpty, List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at member
        subst pair
        rw [← sameTy]
        exact rhsTyped selected rhsValue rhsEnd rhsRun selectedGenerated live
    obtain ⟨closeExtension, closeChecked⟩ := edge_emitTerm_at (.br join [rhsValue]) env rhsEnd closed ignored' closeRun rhsChecked arguments
    have closedGenerated := rhsGenerated.emitTerm (.br join [rhsValue])
      (by intro target member; simp only [Term.successors, List.mem_singleton] at member; subst target; exact rhsJoin.bound) closeRun
    have closedJoin := rhsJoin.extend closeExtension
    obtain ⟨afterGenerated, joinExtension, afterChecked⟩ :=
      generated_edge_setCur_at (some join) env closed joined ignored'' joinRun closedGenerated closeChecked
        (by intro target same; have equal := Option.some.inj same; simpa [← equal] using closedJoin.bound)
    exact ⟨afterGenerated, beforeRhs.trans (rhsExtension.trans (closeExtension.trans joinExtension)), afterChecked⟩

end Goose.Lower.Validation
