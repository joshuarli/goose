import Goose.Lower.DemandCallSplitReadPrefix

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem scalar_read_argument_state {cfg : Cfg} {env : Env} {place : Place} {state after : St} {value : Val}
    (form : ScalarReadPlace place) (evaluated : evalArg 3 cfg env (.byVal (.read place)) state = .ok value after) :
    after = state := by
  cases form with
  | global id =>
    simp only [evalArg, evalExpr, evalPlace, pure_apply, bind_apply, readLoc] at evaluated
    cases found : state.store.read ⟨.global id, []⟩ <;> simp [found] at evaluated
    exact evaluated.2.symm
  | slot id =>
    simp only [evalArg, evalExpr, evalPlace, bind_apply, rootOf] at evaluated
    cases found : env.vars[id]? with
    | none => simp [found, fault, M.stop] at evaluated
    | some lv =>
      cases scope : env.scopes.lookup lv.scope with
      | none => simp [found, scope, fault, M.stop] at evaluated
      | some si =>
        simp only [found, scope, pure_apply, readLoc] at evaluated
        cases read : state.store.read ⟨.local env.act si id, []⟩ <;> simp [read] at evaluated
        exact evaluated.2.symm

#print axioms scalar_read_argument_state
theorem accepted_generated_call_split_read_prefix_post {cfg : Cfg} {env : Env} {initialState state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) initialState)
    {index : Nat} {place : Place} (found : arguments[index]? = some (.byVal (.read place)))
    (child : ExprSource cfg env (.read place) state) (form : ScalarReadPlace place)
    (canonical : (ArgSource.byVal child).MatchesContext source.world source.typingEnv source.rootsEnv
      (callArgContext source.context index (.byVal (.read place)) found))
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.call context arguments origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) {values : List (ValueId × RetainedAlias)} {slots : List SliceSlotArgumentCell}
    (split : SplitCallArgumentRows source.rootsEnv.access source.path 0 (arguments.take index)
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).1 values slots)
    {initial : GIR.Frame} {start : Pt}
    (realized : (⟨⟨values ++ map.values, map.runs⟩, slots⟩ : SplitCallRetained).Realizes
      cfg.mod source.world env ⟨start, initial, state⟩)
    (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : (⟨⟨values ++ map.values, map.runs⟩, slots⟩ : SplitCallRetained).Bounded
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2.vals.size)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2 initial start)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)

    (shrink : cfg.mod.profile = .shrink)
    (checked : ∀ cell ∈ slots, cell.Checked source index initial)
    {taken : Nat} {runtime : DemandRuntimePoint} (completed : 2 ≤ taken)
    (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ runtime) :
    ∃ (middle : DemandRuntimePoint) (aliases : List RetainedAlias) (value : Val),
      DemandRuntimePrefix cx 2 ⟨start, initial, state⟩ middle ∧
      DemandRuntimePrefix cx (taken - 2) middle runtime ∧
      evalArg 3 cfg env (.byVal (.read place)) state = .ok value middle.state ∧
      middle.state = state ∧
      Post cfg env cx (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2 initial
        (lowerExpr (.read place) (lowerEnv cfg.mod env.vars results)
          (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2).2 middle.frame middle.point
        [((lowerExpr (.read place) (lowerEnv cfg.mod env.vars results)
          (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2).1, .val value)] ∧
      let id := (lowerExpr (.read place) (lowerEnv cfg.mod env.vars results)
        (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2).1
      let nextValues := values ++ aliases.map (fun alias => (id, alias))
      SplitCallArgumentRows source.rootsEnv.access source.path 0 (arguments.take (index + 1))
        (lowerArgs (arguments.take (index + 1)) (lowerEnv cfg.mod env.vars results) before).1 nextValues slots ∧
      (⟨⟨nextValues ++ map.values, map.runs⟩, slots⟩ : SplitCallRetained).Realizes cfg.mod source.world env middle ∧
      (⟨⟨nextValues ++ map.values, map.runs⟩, slots⟩ : SplitCallRetained).Bounded
        (lowerArgs (arguments.take (index + 1)) (lowerEnv cfg.mod env.vars results) before).2.vals.size ∧
      (∀ cell ∈ slots, cell.Checked source (index + 1) middle.frame) ∧
      GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv
        (lowerArgs (arguments.take (index + 1)) (lowerEnv cfg.mod env.vars results) before).2 middle.frame middle.point := by
  obtain ⟨middle, aliases, value, leading, residual, evaluated, nextRows, nextRealized, nextBounded, nextChecked, nextInput⟩ :=
    accepted_generated_call_split_read_prefix source found child form canonical occurrence rows coverage split
      realized admitted bounded input extended shrink checked completed steps
  obtain ⟨other, otherEvaluated, boundary⟩ := accepted_generated_call_split_read_complete source found child form canonical
    occurrence rows coverage split realized admitted bounded input extended leading
  have same : other = value := by
    have equal : evalArg 3 cfg env (.byVal (.read place)) state = .ok other middle.state := by
      simp [evalArg, otherEvaluated]
    exact (Res.ok.inj (equal.symm.trans evaluated)).1
  subst other
  exact ⟨middle, aliases, value, leading, residual, evaluated, scalar_read_argument_state form evaluated,
    boundary.post, nextRows, nextRealized, nextBounded, nextChecked, nextInput⟩

#print axioms accepted_generated_call_split_read_prefix_post
end Goose.Lower
