import Goose.Lower.DemandGeneratedShortCircuit

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

theorem shortCircuit_join_builder {isAnd : Bool} {x : ValueId} {rhs : B ValueId} {le : LEnv} {before : LS}
    {result : ValueId} {built : LS} {point : Pt} {blocks : Array GIR.Block}
    (run : shortCircuit isAnd x rhs le before = (result, built)) (atPoint : before.pp = some point)
    (extended : ExtT built blocks) (rhsAdv : AdvB rhs) :
    result = before.vals.size ∧ built.pp = some (before.blocks.size + 1, 0) ∧
      built.stack = before.stack ∧ before.vals.size < built.vals.size := by
  obtain ⟨block, current, blockAt, pointEq⟩ := LS.pp_some atPoint
  unfold shortCircuit at run
  rw [whenLive_some _ _ _ current] at run
  simp only [bind_eq] at run
  obtain ⟨⟨rhsId, joinId, parameter⟩, forked, fork, u2, entered, enter, y, rhsEnd, rhsRun,
    u4, jumped, jump, u5, joined, join, returned⟩ := run
  rw [pure_run] at returned
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj returned
  have rhsStep : entered.Adv rhsEnd := rhsAdv _ _ _ _ rhsRun
  have jumpStep := adv_emitTerm jump
  have joinEq : joined = { jumped with cur := some joinId } := by
    rw [setCur_run] at join
    exact (Prod.mk.inj join).2.symm
  have enterEq : entered = { forked with cur := some rhsId } := by
    rw [setCur_run] at enter
    exact (Prod.mk.inj enter).2.symm
  have jumpExtended : ExtT jumped blocks := by rw [joinEq] at extended; exact extended
  have rhsExtended : ExtT rhsEnd blocks := jumpExtended.of_adv jumpStep
  have enteredExtended : ExtT entered blocks := rhsExtended.of_adv rhsStep
  have forkExtended : ExtT forked blocks := by rw [enterEq] at enteredExtended; exact enteredExtended
  obtain ⟨rhsEq, joinIdEq, parameterEq, valsEq, stackEq, currentEq, instruction, rhsAt, joinAt⟩ :=
    scFork_facts fork atPoint forkExtended
  obtain ⟨_, forkSize⟩ := scFork_ids fork
  subst rhsId joinId parameter
  have enteredBlocks : entered.blocks = forked.blocks := by rw [enterEq]
  have enteredStack : entered.stack = before.stack := by rw [enterEq]; exact stackEq
  have enteredVals : entered.vals.size = before.vals.size + 1 := by rw [enterEq]; exact valsEq
  have joinEntered : entered.blocks[before.blocks.size + 1]? = some ⟨[(before.vals.size, .data .bool)], #[]⟩ := by
    rw [enteredBlocks]
    exact joinAt
  have joinRhs : rhsEnd.blocks[before.blocks.size + 1]? = some ⟨[(before.vals.size, .data .bool)], #[]⟩ := by
    refine rhsStep.keep _ _ ?_ joinEntered
    rw [enterEq]
    intro same
    have := Option.some.inj same
    nat_omega
  have joinJumped : jumped.blocks[before.blocks.size + 1]? = some ⟨[(before.vals.size, .data .bool)], #[]⟩ := by
    cases rhsCurrent : rhsEnd.cur with
    | none =>
      rw [emitTerm_none _ _ rhsCurrent] at jump
      obtain ⟨_, rfl⟩ := Prod.mk.inj jump
      exact joinRhs
    | some currentId =>
      rw [emitTerm_run _ _ rhsCurrent] at jump
      obtain ⟨_, rfl⟩ := Prod.mk.inj jump
      have different : currentId ≠ before.blocks.size + 1 := by
        rcases rhsStep.cur with h | h | ⟨c, hc, hc1, _⟩
        · rw [rhsCurrent] at h; cases h
        · rw [rhsCurrent, enterEq] at h
          have := Option.some.inj h
          have size : entered.blocks.size = before.blocks.size + 2 := by rw [enteredBlocks]; exact forkSize
          nat_omega
        · rw [rhsCurrent] at hc
          have := Option.some.inj hc
          have size : entered.blocks.size = before.blocks.size + 2 := by rw [enteredBlocks]; exact forkSize
          nat_omega
      show (rhsEnd.blocks.modify currentId _)[before.blocks.size + 1]? = _
      rw [getElem?_modify_ne different]
      exact joinRhs
  refine ⟨rfl, ?_, ?_, ?_⟩
  · rw [joinEq]
    exact LS.pp_cur joinJumped
  · rw [joinEq]
    show jumped.stack = _
    rw [jumpStep.stack, rhsStep.stack, enteredStack]
  · rw [joinEq]
    show before.vals.size < jumped.vals.size
    have := jumpStep.vals
    have := rhsStep.vals
    omega

theorem accepted_shortCircuit_skip_boundary {cfg : Cfg} {env : Env} {a b : Expr} {state after : St}
    (isAnd : Bool) (source : ExprSource cfg env (if isAnd then .and a b else .or a b) state)
    (left : ExprSource cfg env a state) {fuel : Nat}
    (leftDone : evalExpr fuel cfg env a state = .ok (.bool (!isAnd)) after)
    {cx : FnCtx} {le : LEnv} {before : LS} {initial frame : GIR.Frame} {point start : Pt}
    {map : RetainedSsaMap} (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (boundary : ExpressionDemandBoundary left map cx before initial (lowerExpr a le before).2
      (lowerExpr a le before).1 (.bool (!isAnd)) after point frame)
    (extended : ExtT (lowerExpr (if isAnd then .and a b else .or a b) le before).2 cx.fn.blocks)
    {next : Pt} {nextFrame : GIR.Frame} {nextState : St}
    (actual : Evidence.RuntimeStep cx.cfg cx.fn point frame after next nextFrame nextState) :
    evalExpr (fuel + 1) cfg env (if isAnd then .and a b else .or a b) state =
        .ok (.bool (!isAnd)) nextState ∧
      ExpressionDemandBoundary source map cx before initial
        (lowerExpr (if isAnd then .and a b else .or a b) le before).2
        (lowerExpr (if isAnd then .and a b else .or a b) le before).1 (.bool (!isAnd)) nextState next nextFrame := by
  let first := lowerExpr a le before
  let fork := demandShortCircuitFork isAnd a le before
  let built := lowerExpr (if isAnd then .and a b else .or a b) le before
  have run : shortCircuit isAnd first.1 (lowerExpr b) le first.2 = built := by
    cases isAnd <;> rfl
  have ⟨resultEq, atJoin, stackEq, valsBound⟩ :=
    shortCircuit_join_builder run boundary.post.pp extended (advB_lowerExpr b)
  have forkExtended := generated_shortCircuit_fork_extended (right := b) boundary.post.pp extended
  have ⟨rhsEq, joinEq, parameterEq, valsEq, forkStack, forkCurrent, instruction, rhsAt, joinAt⟩ :=
    scFork_facts (show scFork isAnd first.1 le first.2 = (fork.1, fork.2) from rfl) boundary.post.pp forkExtended
  have cell := boundary.post.has (first.1, .val (.bool (!isAnd))) (by simp [first])
  obtain ⟨stepFuel, actualStep⟩ := runtimeStep_demandInstructionStep actual
  have expected := shortCircuit_control_step (state := after) .skip (show scFork isAnd first.1 le first.2 = (fork.1, fork.2) from rfl)
    boundary.post.pp forkExtended cell stepFuel
  have same := actualStep.deterministic expected
  have nextEq := congrArg DemandRuntimePoint.point same
  have frameEq := congrArg DemandRuntimePoint.frame same
  have stateEq := congrArg DemandRuntimePoint.state same
  dsimp only [ShortCircuitPath.target, ShortCircuitPath.frame] at nextEq frameEq stateEq
  change first.2.vals.size < built.2.vals.size at valsBound
  have piece : Post cfg env cx first.2 frame built.2
      (frame.set first.2.vals.size (.val (.bool (!isAnd)))) (first.2.blocks.size + 1, 0)
      [(built.1, .val (.bool (!isAnd)))] := by
    rw [resultEq]
    exact Post.join (Same.refl _ _) boundary.post.rel (Nat.le_refl _) valsBound (Nat.le_of_lt valsBound) stackEq atJoin
  have whole : Post cfg env cx before initial built.2
      (frame.set first.2.vals.size (.val (.bool (!isAnd)))) (first.2.blocks.size + 1, 0)
      [(built.1, .val (.bool (!isAnd)))] := (boundary.post.comp piece).sub (by simp)
  have done : evalExpr (fuel + 1) cfg env (if isAnd then .and a b else .or a b) state =
      .ok (.bool (!isAnd)) after := by
    cases isAnd <;> simp [evalExpr, leftDone, bind_apply, Core.expectBool, pure_apply]
  have result := source.result (fuel + 1) (.bool (!isAnd)) done
  have final : ExpressionDemandBoundary source map cx before initial built.2 built.1 (.bool (!isAnd))
      after (first.2.blocks.size + 1, 0) (frame.set first.2.vals.size (.val (.bool (!isAnd)))) :=
    ExpressionDemandBoundary.of_result result admitted bounded realized whole
  rw [nextEq, frameEq, stateEq, joinEq, parameterEq]
  exact ⟨done, final⟩

#print axioms accepted_shortCircuit_skip_boundary

#print axioms shortCircuit_join_builder

end Goose.Lower
