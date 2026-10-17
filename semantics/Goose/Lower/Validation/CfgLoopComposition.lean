import Goose.Lower.Validation.CfgHeaderPaths

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem paths_whenLive_live (default : α) {action : B α} (preserves : LivePathRun action) :
    BoundedRun ReachableBuilder (whenLive default fun _ => action) := by
  intro env before result after run paths bounded
  cases current : before.cur with
  | none =>
    rw [whenLive_none _ _ env current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact paths
  | some block =>
    rw [whenLive_some _ _ env current] at run
    exact preserves env before result after run paths bounded (by simp [current])

theorem LivePathRun.bind {first : B α} {next : α → B β}
    (advance : AdvB first) (preserves : BoundedRun ReachableBuilder first)
    (current : ∀ env state, (first env state).2.cur = state.cur)
    (rest : ∀ result, LivePathRun (next result)) : LivePathRun (first >>= next) := by
  intro env before result after run paths bounded live
  obtain ⟨value, middle, firstRun, nextRun⟩ := bind_eq.mp run
  have middleBound := liveBound_of_adv (advance env before value middle firstRun) bounded
  have middlePaths := preserves env before value middle firstRun paths bounded
  have middleCurrent := current env before
  rw [firstRun] at middleCurrent
  dsimp only at middleCurrent
  exact rest value env middle result after nextRun middlePaths middleBound (by simpa [middleCurrent] using live)

theorem emitDef_current (op : Op) (env : LEnv) (state : LS) :
    (emitDef op env state).2.cur = state.cur := by
  cases current : state.cur with
  | none => rw [emitDef_none op env current]; exact current
  | some block => rw [emitDef_run op env current]; exact current

theorem paths_rangeBack (ty : IntTy) (counter : ValueId) (header : BlockId) :
    BoundedRun ReachableBuilder (rangeBack ty counter header) := by
  unfold rangeBack
  refine BoundedRun.bind advB_isLive (paths_of_blocks_unchanged fun _ _ => rfl) fun live => ?_
  cases live with
  | false => exact BoundedRun.pure _ _
  | true => exact BoundedRun.bind (advB_emitDef _) (paths_emitDef _) fun _ => paths_emitTerm _

theorem paths_loopBody_live {condition : ValueId} {body : Nat → BlockId → B ValueId} {back : B Unit}
    (bodyAdvance : ∀ depth exit, AdvB (body depth exit))
    (bodyPaths : ∀ depth exit, BoundedRun ReachableBuilder (body depth exit))
    (backPaths : BoundedRun ReachableBuilder back) : LivePathRun (loopBody condition body back) := by
  intro env before result after run paths bounded live
  cases current : before.cur with
  | none => simp [current] at live
  | some source => exact paths_loopBody bodyAdvance bodyPaths backPaths run current paths bounded

theorem paths_lowerWhile (header : BlockId) {condition : B ValueId} {body : Nat → BlockId → B ValueId}
    (conditionAdvance : AdvB condition) (conditionPaths : BoundedRun ReachableBuilder condition)
    (bodyAdvance : ∀ depth exit, AdvB (body depth exit))
    (bodyPaths : ∀ depth exit, BoundedRun ReachableBuilder (body depth exit)) :
    BoundedRun ReachableBuilder (lowerWhile header condition body) := by
  unfold lowerWhile
  exact BoundedRun.bind conditionAdvance conditionPaths fun _ =>
    paths_whenLive_live _ (paths_loopBody_live bodyAdvance bodyPaths (paths_emitTerm _))

theorem paths_lowerRange (ty : IntTy) (counter bound : ValueId) (header : BlockId)
    {body : Nat → BlockId → B ValueId} (bodyAdvance : ∀ depth exit, AdvB (body depth exit))
    (bodyPaths : ∀ depth exit, BoundedRun ReachableBuilder (body depth exit)) :
    LivePathRun (lowerRange ty counter bound header body) := by
  unfold lowerRange
  exact LivePathRun.bind (advB_emitDef _) (paths_emitDef _) (emitDef_current _) fun _ =>
    paths_loopBody_live bodyAdvance bodyPaths (paths_rangeBack _ _ _)

theorem paths_eachLen (regrow : Bool) (owner : Option ValueId) (sampled : ValueId) :
    BoundedRun ReachableBuilder (eachLen regrow owner sampled) := by
  unfold eachLen
  cases regrow
  · exact BoundedRun.pure _ _
  · exact paths_emitDef _

theorem eachLen_current (regrow : Bool) (owner : Option ValueId) (sampled : ValueId)
    (env : LEnv) (state : LS) : (eachLen regrow owner sampled env state).2.cur = state.cur := by
  unfold eachLen
  cases regrow
  · rfl
  · exact emitDef_current _ env state

theorem paths_lowerEach (regrow : Bool) (owner : Option ValueId) (sampled header counter : Nat)
    {body : Nat → BlockId → B ValueId} (bodyAdvance : ∀ depth exit, AdvB (body depth exit))
    (bodyPaths : ∀ depth exit, BoundedRun ReachableBuilder (body depth exit)) :
    LivePathRun (lowerEach regrow owner sampled header counter body) := by
  unfold lowerEach
  refine LivePathRun.bind (advB_eachLen _ _ _) (paths_eachLen _ _ _) (eachLen_current _ _ _) fun _ => ?_
  exact LivePathRun.bind (advB_emitDef _) (paths_emitDef _) (emitDef_current _) fun _ =>
    paths_loopBody_live bodyAdvance bodyPaths (paths_rangeBack _ _ _)

end Goose.Lower.Validation
