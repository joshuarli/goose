import Goose.Lower.DemandCallSplitValueBoundary
import Goose.Lower.DemandCallScalarLiteral

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence
open Goose.Lower.Validation.ReplacementContentFlowSource

theorem accepted_generated_call_split_scalar_literal_stage {cfg : Cfg} {env : Env} {initialState state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) initialState)
    {index : Nat} {expression : Expr} {value : Val} {operation : Op}
    (literal : CallScalarLiteral expression value operation) (found : arguments[index]? = some (.byVal expression))
    (child : ExprSource cfg env expression state)
    (canonical : (ArgSource.byVal child).MatchesContext source.world source.typingEnv source.rootsEnv
      (callArgContext source.context index (.byVal expression) found))
    {cx : FnCtx} {results : List Ty} {before : LS} {loop : Option LoopCtx}
    {map : RetainedSsaMap} (admitted : map.Admitted cfg.mod.profile source.context.retained)
    {values : List (ValueId × RetainedAlias)} {slots : List SliceSlotArgumentCell}
    (split : SplitCallArgumentRows source.rootsEnv.access source.path 0 (arguments.take index)
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).1 values slots)
    {initial : GIR.Frame} {start : Pt}
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2 initial start)
    (bounded : (⟨⟨values ++ map.values, map.runs⟩, slots⟩ : SplitCallRetained).Bounded
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2.vals.size)
    (realized : (⟨⟨values ++ map.values, map.runs⟩, slots⟩ : SplitCallRetained).Realizes
      cfg.mod source.world env ⟨start, initial, state⟩)
    (checked : ∀ cell ∈ slots, cell.Checked source index initial)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    :
    ∃ (point : Pt) (frame : GIR.Frame),
      let le := lowerEnv cfg.mod env.vars results
      let stage := (lowerArgs (arguments.take index) le before).2
      let id := (lowerExpr expression le stage).1
      evalArg 2 cfg env (.byVal expression) state = .ok value state ∧
      DemandRuntimePrefix cx 1 ⟨start, initial, state⟩ ⟨point, frame, state⟩ ∧
      Post cfg env cx stage initial (lowerExpr expression le stage).2 frame point [(id, .val value)] ∧
      SplitCallArgumentRows source.rootsEnv.access source.path 0 (arguments.take (index + 1))
        (lowerArgs (arguments.take (index + 1)) le before).1 (values) slots ∧
      (⟨⟨(values) ++ map.values, map.runs⟩, slots⟩ : SplitCallRetained).Realizes
        cfg.mod source.world env ⟨point, frame, state⟩ ∧
      (⟨⟨(values) ++ map.values, map.runs⟩, slots⟩ : SplitCallRetained).Bounded
        (lowerArgs (arguments.take (index + 1)) le before).2.vals.size ∧
      (∀ cell ∈ slots, cell.Checked source (index + 1) frame) ∧
      GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv
        (lowerArgs (arguments.take (index + 1)) le before).2 frame point := by
  let le := lowerEnv cfg.mod env.vars results
  let stage := (lowerArgs (arguments.take index) le before).2
  let id := (lowerExpr expression le stage).1
  let result := (lowerExpr expression le stage).2
  obtain ⟨ids, middle, after, argsRun, definition, tail⟩ := lowerExpr_call_split
    (show lowerExpr (.call context arguments origin) le before =
      ((lowerExpr (.call context arguments origin) le before).1, (lowerExpr (.call context arguments origin) le before).2) from rfl)
  have afterExtended : ExtT after cx.fn.blocks := by
    rcases tail with ⟨_, term⟩ | ⟨_, rfl⟩
    · exact extended.of_adv (adv_emitTerm term)
    · exact extended
  have argsExtended : ExtT (lowerArgs arguments le before).2 cx.fn.blocks := by
    rw [argsRun]
    exact afterExtended.of_adv (adv_emitDef definition)
  obtain ⟨earlier, later, argsSplit, length, _, _, advance⟩ := lowerArgs_argument_checkpoint found le before
  have earlierEq : arguments.take index = earlier := by
    rw [argsSplit, ← length]
    simp
  have childExtended : ExtT result cx.fn.blocks := by
    rw [show result = (lowerExpr expression le (lowerArgs (arguments.take index) le before).2).2 from rfl, earlierEq]
    exact argsExtended.of_adv (by simpa [lowerArg] using advance)
  have emitted : emitDef operation le stage = (id, result) := by
    cases literal <;> rfl
  obtain ⟨post, instruction⟩ := Post.def_leaf (Post.init input.related input.atPoint) emitted childExtended (.val value)
  have done : evalExpr 1 cfg env expression state = .ok value state := by
    cases literal <;> simp [evalExpr, pure_apply]
  have childAdmission := (SplitCallRetained.byValAdmission source found child canonical admitted split).1
  have childRealized : (⟨values ++ map.values, map.runs⟩ : RetainedSsaMap).Realizes cfg.mod child.world env ⟨start, initial, state⟩ := by
    simpa only [canonical.2.2.1] using realized.1
  have boundary := ExpressionDemandBoundary.of_result (child.result 1 value done) childAdmission bounded.1 childRealized post
  have step : DemandInstructionStep cx 0 ⟨start, initial, state⟩
      ⟨(start.1, start.2 + 1), initial.set id (.val value), state⟩ := by
    apply DemandInstructionStep.definition instruction
    cases literal <;> simp [execOp, execPure, pure_apply]
  have query : source.rootsEnv.access.aliasArg (source.path ++ [index]) (.byVal expression) = .ok [] := by
    cases literal <;> simp [AccessEnv.aliasArg, AccessEnv.aliasExpr, AccessEnv.exprType?, Ty.interiorTarget?, pure, Except.pure]
  obtain ⟨nextRows, nextRealized, nextBounded, nextChecked⟩ :=
    accepted_generated_call_split_value_finish (cx := cx) (results := results) (map := map)
      (runtime := ⟨(start.1, start.2 + 1), initial.set id (.val value), state⟩)
      source found child canonical split query boundary checked bounded.2
  simp only [List.map_nil, List.append_nil] at nextRows nextRealized nextBounded
  have nextInput := accepted_generated_call_value_next_input (map := ⟨values ++ map.values, map.runs⟩)
    (runtime := ⟨(start.1, start.2 + 1), initial.set id (.val value), state⟩) source found child input boundary
  exact ⟨(start.1, start.2 + 1), initial.set id (.val value), by simpa [evalArg, done],
    .next step.runtime (.zero _), post, nextRows, nextRealized, nextBounded, nextChecked, nextInput⟩


theorem accepted_generated_call_split_boolean_stage {cfg : Cfg} {env : Env} {initialState state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) initialState)
    {index : Nat} {boolean : Bool} (found : arguments[index]? = some (.byVal (.bool boolean)))
    (child : ExprSource cfg env (.bool boolean) state)
    (canonical : (ArgSource.byVal child).MatchesContext source.world source.typingEnv source.rootsEnv
      (callArgContext source.context index (.byVal (.bool boolean)) found))
    {cx : FnCtx} {results : List Ty} {before : LS} {loop : Option LoopCtx}
    {map : RetainedSsaMap} (admitted : map.Admitted cfg.mod.profile source.context.retained)
    {values : List (ValueId × RetainedAlias)} {slots : List SliceSlotArgumentCell}
    (split : SplitCallArgumentRows source.rootsEnv.access source.path 0 (arguments.take index)
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).1 values slots)
    {initial : GIR.Frame} {start : Pt}
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2 initial start)
    (bounded : (⟨⟨values ++ map.values, map.runs⟩, slots⟩ : SplitCallRetained).Bounded
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2.vals.size)
    (realized : (⟨⟨values ++ map.values, map.runs⟩, slots⟩ : SplitCallRetained).Realizes
      cfg.mod source.world env ⟨start, initial, state⟩)
    (checked : ∀ cell ∈ slots, cell.Checked source index initial)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    :
    ∃ (point : Pt) (frame : GIR.Frame),
      let le := lowerEnv cfg.mod env.vars results
      let stage := (lowerArgs (arguments.take index) le before).2
      let id := (lowerExpr (.bool boolean) le stage).1
      evalArg 2 cfg env (.byVal (.bool boolean)) state = .ok (.bool boolean) state ∧
      DemandRuntimePrefix cx 1 ⟨start, initial, state⟩ ⟨point, frame, state⟩ ∧
      Post cfg env cx stage initial (lowerExpr (.bool boolean) le stage).2 frame point [(id, .val (.bool boolean))] ∧
      SplitCallArgumentRows source.rootsEnv.access source.path 0 (arguments.take (index + 1))
        (lowerArgs (arguments.take (index + 1)) le before).1 (values) slots ∧
      (⟨⟨(values) ++ map.values, map.runs⟩, slots⟩ : SplitCallRetained).Realizes
        cfg.mod source.world env ⟨point, frame, state⟩ ∧
      (⟨⟨(values) ++ map.values, map.runs⟩, slots⟩ : SplitCallRetained).Bounded
        (lowerArgs (arguments.take (index + 1)) le before).2.vals.size ∧
      (∀ cell ∈ slots, cell.Checked source (index + 1) frame) ∧
      GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv
        (lowerArgs (arguments.take (index + 1)) le before).2 frame point := by
  exact accepted_generated_call_split_scalar_literal_stage source (.boolean boolean) found child canonical admitted split input bounded realized checked extended

#print axioms accepted_generated_call_split_scalar_literal_stage

#print axioms accepted_generated_call_split_boolean_stage
end Goose.Lower
