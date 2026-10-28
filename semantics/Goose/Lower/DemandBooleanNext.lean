import Goose.Lower.DemandBooleanExpressions

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem DemandUniformTraversal.runtimePrefix_next {cx : FnCtx} {invariant : DemandRuntimePoint → Prop}
    {length : Nat} {before after : DemandRuntimePoint}
    (traversal : DemandUniformTraversal cx invariant length before after)
    {taken : Nat} {reached : DemandRuntimePoint}
    (bounded : taken < length) (steps : DemandRuntimePrefix cx taken before reached) :
    ∃ next, ∀ fuel, DemandInstructionStep cx fuel reached next := by
  induction traversal generalizing taken reached with
  | done valid => omega
  | next valid step rest ih =>
    cases steps with
    | zero => exact ⟨_, step⟩
    | next first tail =>
      obtain ⟨fuel, first⟩ := runtimeStep_demandInstructionStep first
      have same := (step fuel).deterministic first
      cases same
      exact ih (by omega) tail

theorem DemandUniformTraversal.runtimePrefix_split {cx : FnCtx} {invariant : DemandRuntimePoint → Prop}
    {length : Nat} {before after : DemandRuntimePoint}
    (traversal : DemandUniformTraversal cx invariant length before after)
    {taken : Nat} {reached : DemandRuntimePoint}
    (bounded : length ≤ taken) (steps : DemandRuntimePrefix cx taken before reached) :
    ∃ remaining, taken = length + remaining ∧ DemandRuntimePrefix cx length before after ∧
      DemandRuntimePrefix cx remaining after reached := by
  induction traversal generalizing taken reached with
  | done valid => exact ⟨taken, by omega, .zero _, steps⟩
  | next valid step rest ih =>
    cases steps with
    | zero => omega
    | next first tail =>
      obtain ⟨fuel, actual⟩ := runtimeStep_demandInstructionStep first
      have same := actual.deterministic (step fuel)
      cases same
      obtain ⟨remaining, count, traversed, residual⟩ := ih (by omega) tail
      exact ⟨remaining, by omega, .next first traversed, residual⟩

theorem accepted_boolean_expression_next {cfg : Cfg} {env : Env} {expression : Expr}
    {state : St} (fragment : BooleanNotExpression expression) (source : ExprSource cfg env expression state)
    {map : RetainedSsaMap} (admitted : map.Admitted cfg.mod.profile source.context.retained)
    {cx : FnCtx} {before built : LS} {initial : GIR.Frame} {start : Pt} {id : ValueId} {le : LEnv}
    (bounded : map.Bounded before.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (lowered : lowerExpr expression le before = (id, built))
    (point : before.pp = some start) (extension : ExtT built cx.fn.blocks)
    (related : Rel cfg env cx initial before)
    {taken : Nat} {runtime : DemandRuntimePoint} (unfinished : taken < fragment.instructions)
    (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ runtime) :
    CanonicalExpressionDemand map cx source runtime ∧ ∃ next, ∀ fuel, DemandInstructionStep cx fuel runtime next := by
  obtain ⟨_, _, _, _, _, _, traversal⟩ :=
    accepted_boolean_expression_demand_traversal fragment source admitted bounded realized lowered point extension related
  exact ⟨traversal.runtimePrefix_invariant (by omega) steps, traversal.runtimePrefix_next unfinished steps⟩

theorem accepted_boolean_expression_no_terminal_stop {cfg : Cfg} {env : Env} {expression : Expr}
    {state : St} (fragment : BooleanNotExpression expression) (source : ExprSource cfg env expression state)
    {map : RetainedSsaMap} (admitted : map.Admitted cfg.mod.profile source.context.retained)
    {cx : FnCtx} {before built : LS} {initial : GIR.Frame} {start : Pt} {id : ValueId} {le : LEnv}
    (bounded : map.Bounded before.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (lowered : lowerExpr expression le before = (id, built))
    (point : before.pp = some start) (extension : ExtT built cx.fn.blocks)
    (related : Rel cfg env cx initial before)
    {taken : Nat} {runtime : DemandRuntimePoint} (unfinished : taken < fragment.instructions)
    (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ runtime)
    {fuel : Nat} {stop : Stop} {after : St} (stopped : DemandInstructionStop cx fuel runtime stop after)
    (nonTimeout : stop ≠ .timeout) : False := by
  obtain ⟨_, next, step⟩ := accepted_boolean_expression_next fragment source admitted bounded realized lowered point extension related unfinished steps
  exact stopped.excludes_step_nonTimeout nonTimeout (step fuel)

theorem accepted_boolean_expression_maximal_after_completion {cfg : Cfg} {env : Env} {expression : Expr}
    {state : St} (fragment : BooleanNotExpression expression) (source : ExprSource cfg env expression state)
    {map : RetainedSsaMap} (admitted : map.Admitted cfg.mod.profile source.context.retained)
    {cx : FnCtx} {before built : LS} {initial : GIR.Frame} {start : Pt} {id : ValueId} {le : LEnv}
    (bounded : map.Bounded before.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (lowered : lowerExpr expression le before = (id, built))
    (point : before.pp = some start) (extension : ExtT built cx.fn.blocks)
    (related : Rel cfg env cx initial before)
    {taken : Nat} {runtime : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ runtime)
    {fuel : Nat} (maximal : ∀ next, ¬ DemandInstructionStep cx fuel runtime next) :
    fragment.instructions ≤ taken := by
  by_cases unfinished : taken < fragment.instructions
  · obtain ⟨_, next, step⟩ := accepted_boolean_expression_next fragment source admitted bounded realized lowered point extension related unfinished steps
    exact (maximal next (step fuel)).elim
  · omega

#print axioms DemandUniformTraversal.runtimePrefix_next
#print axioms DemandUniformTraversal.runtimePrefix_split
#print axioms accepted_boolean_expression_next
#print axioms accepted_boolean_expression_no_terminal_stop
#print axioms accepted_boolean_expression_maximal_after_completion
end Goose.Lower
