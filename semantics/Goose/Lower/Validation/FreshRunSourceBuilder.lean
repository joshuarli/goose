import Goose.Lower.Validation.FreshRunSourceShape

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

private theorem frameRun_none {action : B α} (source : GeneratedTargetFrameRun none action)
    {env : LEnv} {before after : LS} {value : α} (run : action env before = (value, after)) :
    TermEdgesFramed none before after ∧ before.Ext after :=
  source before env before value after (.refl before) trivial (.refl none before) run

mutual
theorem ownerFreshExpr_future (expr : Expr) (source : OwnerFreshExpr expr)
    {env : LEnv} {before captured : LS} {value : ValueId}
    (run : lowerExpr expr env before = (value, captured)) (live : captured.cur.isSome = true)
    (generated : GeneratedBuilderState before) : FutureLiteralValue before captured value := by
  cases source with
  | literal ty values owner => exact futureLiteralValue_arrLit run live generated owner
  | block fresh => exact ownerFreshBlock_future _ fresh run live generated
  | @conditional condition yes no yesFresh noFresh =>
    simp only [lowerExpr] at run
    obtain ⟨conditionValue, middle, conditionRun, run⟩ := bind_eq.mp run
    cases current : middle.cur with
    | none =>
      rw [whenLive_none _ _ _ current] at run
      obtain ⟨_, rfl⟩ := Prod.mk.inj run
      simp [current] at live
    | some block =>
      rw [whenLive_some _ _ _ current] at run
      obtain ⟨arms, forked, forkRun, run⟩ := bind_eq.mp run
      obtain ⟨_, thenStart, thenStartRun, run⟩ := bind_eq.mp run
      obtain ⟨thenValue, thenAfter, thenRun, thenTailRun⟩ := bind_eq.mp run
      obtain ⟨thenEnd, thenClosed, thenEndRun, run⟩ := bind_eq.mp thenTailRun
      rw [curBlock_run] at thenEndRun
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj thenEndRun
      obtain ⟨_, elseStart, elseStartRun, run⟩ := bind_eq.mp run
      obtain ⟨elseValue, elseAfter, elseRun, elseTailRun⟩ := bind_eq.mp run
      obtain ⟨elseEnd, elseClosed, elseEndRun, joinRun⟩ := bind_eq.mp elseTailRun
      rw [curBlock_run] at elseEndRun
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj elseEndRun
      have conditionExt := (frameRun_none (generatedTargetFrame_lowerExpr none condition) conditionRun).2
      have forkExt := (frameRun_none (generatedTargetFrame_fork none conditionValue) forkRun).2
      have thenSelectExt := (frameRun_none (generatedTargetFrame_setCur none (some arms.1)) thenStartRun).2
      have thenExt := (frameRun_none (generatedTargetFrame_lowerBlock none [] true yes) thenRun).2
      have elseSelectExt := (frameRun_none (generatedTargetFrame_setCur none (some arms.2)) elseStartRun).2
      have elseExt := (frameRun_none (generatedTargetFrame_lowerBlock none [] true no) elseRun).2
      have thenPrefix := conditionExt.trans (forkExt.trans thenSelectExt)
      have elsePrefix := thenPrefix.trans (thenExt.trans elseSelectExt)
      have beforeJoin := elsePrefix.trans elseExt
      have conditionGenerated := generated.lowerExpr condition conditionRun
      have forkGenerated := conditionGenerated.fork conditionValue forkRun
      obtain ⟨⟨thenBody, thenAt, _⟩, ⟨elseBody, elseAt, _⟩⟩ := fork_emptyRows forkRun
      have thenGenerated := forkGenerated.setCur (some arms.1) (by
        intro selected equal
        cases equal
        exact (Array.getElem?_eq_some_iff.mp thenAt).1) thenStartRun
      have thenAfterGenerated := thenGenerated.lowerBlock none [] true yes trivial thenRun
      have elseGenerated := thenAfterGenerated.setCur (some arms.2) (by
        intro selected equal
        cases equal
        exact Nat.lt_of_lt_of_le ((Array.getElem?_eq_some_iff.mp elseAt).1)
          (thenSelectExt.trans thenExt).1) elseStartRun
      have elseAfterGenerated := elseGenerated.lowerBlock none [] true no trivial elseRun
      apply futureLiteralValue_joinValue joinRun live elseAfterGenerated.targets
      · intro selected selectedAt
        exact Nat.lt_of_lt_of_le (thenAfterGenerated.live selected selectedAt) (elseSelectExt.trans elseExt).1
      · exact elseAfterGenerated.live
      · exact beforeJoin
      · intro thenLive
        have child := ownerFreshBlock_future yes yesFresh thenRun thenLive thenGenerated
        apply child.weaken thenPrefix
        · exact (frameRun_none
            (GeneratedTargetFrameRun.bind (generatedTargetFrame_curBlock none) fun thenEnd =>
              GeneratedTargetFrameRun.bind (generatedTargetFrame_setCur none (some arms.2)) fun _ =>
                GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerBlock none [] true no) fun elseValue =>
                  GeneratedTargetFrameRun.bind (generatedTargetFrame_curBlock none) fun elseEnd =>
                    generatedTargetFrame_joinValue none thenEnd elseEnd thenValue elseValue)
            thenTailRun).2
        · exact (frameRun_none
            (GeneratedTargetFrameRun.bind (generatedTargetFrame_curBlock none) fun thenEnd =>
              GeneratedTargetFrameRun.bind (generatedTargetFrame_setCur none (some arms.2)) fun _ =>
                GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerBlock none [] true no) fun elseValue =>
                  GeneratedTargetFrameRun.bind (generatedTargetFrame_curBlock none) fun elseEnd =>
                    generatedTargetFrame_joinValue none thenEnd elseEnd thenValue elseValue)
            thenTailRun).1
      · intro elseLive
        have child := ownerFreshBlock_future no noFresh elseRun elseLive elseGenerated
        have tail := frameRun_none
          (GeneratedTargetFrameRun.bind (generatedTargetFrame_curBlock none) fun elseEnd =>
            generatedTargetFrame_joinValue none thenAfter.cur elseEnd thenValue elseValue) elseTailRun
        exact child.weaken elsePrefix tail.2 tail.1

theorem ownerFreshBlock_future (body : Core.Block) (source : OwnerFreshBlock body)
    {env : LEnv} {before captured : LS} {value : ValueId}
    (run : lowerBlock none [] true body env before = (value, captured))
    (live : captured.cur.isSome = true) (generated : GeneratedBuilderState before) :
    FutureLiteralValue before captured value := by
  cases source with
  | @result scope statements expr fresh =>
    simp only [lowerBlock, inScope] at run
    obtain ⟨_, entered, enterRun, run⟩ := bind_eq.mp run
    obtain ⟨_, pushed, pushRun, run⟩ := bind_eq.mp run
    obtain ⟨result, bodyAfter, bodyRun, run⟩ := bind_eq.mp run
    obtain ⟨_, popped, popRun, run⟩ := bind_eq.mp run
    obtain ⟨rfl, rfl⟩ := pure_eq.mp run
    obtain ⟨_, initialized, initRun, bodyRun⟩ := bind_eq.mp bodyRun
    obtain ⟨_, statementsAfter, statementsRun, bodyRun⟩ := bind_eq.mp bodyRun
    obtain ⟨result, valueAfter, valueRun, bodyRun⟩ := bind_eq.mp bodyRun
    obtain ⟨_, left, leaveRun, bodyRun⟩ := bind_eq.mp bodyRun
    obtain ⟨rfl, rfl⟩ := pure_eq.mp bodyRun
    have valueLive := (dead_emitEffect (.leave scope)).live_before leaveRun
      (dead_popScope.live_before popRun live)
    have enteredGenerated := generated.emitEffect (.enter scope) enterRun
    rw [pushScope_run] at pushRun
    obtain ⟨_, rfl⟩ := Prod.mk.inj pushRun
    have pushedGenerated : GeneratedBuilderState { entered with stack := scope :: entered.stack } :=
      ⟨enteredGenerated.dense, enteredGenerated.live, enteredGenerated.targets⟩
    have initializedGenerated := pushedGenerated.initSlots [] initRun
    have statementsGenerated := initializedGenerated.lowerStmts none statements trivial statementsRun
    have child := ownerFreshExpr_future expr fresh valueRun valueLive statementsGenerated
    have enterExt := (frameRun_none (generatedTargetFrame_emitEffect none (.enter scope)) enterRun).2
    have pushExt : entered.Ext { entered with stack := scope :: entered.stack } := .refl entered
    have initExt := (frameRun_none (generatedTargetFrame_initSlots none []) initRun).2
    have statementsExt := (frameRun_none (generatedTargetFrame_lowerStmts none statements) statementsRun).2
    have leave := frameRun_none (generatedTargetFrame_emitEffect none (.leave scope)) leaveRun
    rw [popScope_run] at popRun
    obtain ⟨_, rfl⟩ := Prod.mk.inj popRun
    exact child.weaken (enterExt.trans (pushExt.trans (initExt.trans statementsExt)))
      leave.2 (leave.1.of_blocks rfl)
end

theorem lowerExpr_freshOwner_freshRuns {expr : Expr} {env : Core.TEnv} {ty : Ty} {start finish : Nat}
    (source : Core.tyExpr env expr start = .ok (ty, finish)) (fresh : expr.freshOwner = true)
    (owner : isLiteralRunType ty = true) {results : List Ty} {before captured : LS} {value : ValueId}
    (run : lowerExpr expr (lowerEnv env.mod env.vars results) before = (value, captured))
    (live : captured.cur.isSome = true) (generated : GeneratedBuilderState before)
    {after : LS} {func : Func} {types : Array (Option VTy)}
    (framed : IntervalEdgesFramed before captured after)
    (extension : captured.Ext after) (closed : ∀ body ∈ after.blocks.toList, ClosedBlock body)
    (blocks : func.blocks = finishBlocks after.blocks)
    (dense : (func.blocks.toList.flatMap GIR.Block.defs).Perm (List.range func.numValues))
    (rows : OwnerLiteralRows func types) : (freshRuns func types)[value]? = some true := by
  have shape := ownerFreshExpr_of_source expr source fresh owner
  have future := ownerFreshExpr_future expr shape run live generated
  exact (future after func types framed extension closed blocks dense rows).checked
    (Func.parameter_ids_bounded_of_dense dense)

theorem lowerBlock_freshOwner_freshRuns {body : Core.Block} {env : Core.TEnv} {ty : Ty} {start finish : Nat}
    (source : Core.tyBlock env [] body start = .ok (ty, finish)) (fresh : body.freshOwner = true)
    (owner : isLiteralRunType ty = true) {results : List Ty} {before captured : LS} {value : ValueId}
    (run : lowerBlock none [] true body (lowerEnv env.mod env.vars results) before = (value, captured))
    (live : captured.cur.isSome = true) (generated : GeneratedBuilderState before)
    {after : LS} {func : Func} {types : Array (Option VTy)}
    (framed : IntervalEdgesFramed before captured after)
    (extension : captured.Ext after) (closed : ∀ body ∈ after.blocks.toList, ClosedBlock body)
    (blocks : func.blocks = finishBlocks after.blocks)
    (dense : (func.blocks.toList.flatMap GIR.Block.defs).Perm (List.range func.numValues))
    (rows : OwnerLiteralRows func types) : (freshRuns func types)[value]? = some true := by
  have shape := ownerFreshBlock_of_source body source fresh owner
  have future := ownerFreshBlock_future body shape run live generated
  exact (future after func types framed extension closed blocks dense rows).checked
    (Func.parameter_ids_bounded_of_dense dense)

end Goose.Lower.Validation
