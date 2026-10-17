import Goose.Lower.Validation.CfgOpenControl

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem opens_emitDef (op : Op) : BoundedRun CurrentOpen (emitDef op) := by
  intro env before result after run openCurrent _
  have preserved := openCurrent.emitDef op env
  rw [run] at preserved
  exact preserved

theorem opens_emitEffect (effect : Effect) : BoundedRun CurrentOpen (emitEffect effect) := by
  intro env before result after run openCurrent _
  have preserved := openCurrent.emitEffect effect env
  rw [run] at preserved
  exact preserved

theorem opens_emitTerm (term : Term) : BoundedRun CurrentOpen (emitTerm term) := by
  intro env before result after run _ _
  have preserved := currentOpen_emitTerm before term env
  rw [run] at preserved
  exact preserved

theorem opens_of_state_unchanged {action : B α}
    (blocks : ∀ env state, (action env state).2.blocks = state.blocks)
    (current : ∀ env state, (action env state).2.cur = state.cur) : BoundedRun CurrentOpen action := by
  intro env before result after run openCurrent _
  apply openCurrent.of_state
  · have same := blocks env before; simpa only [run] using same
  · have same := current env before; simpa only [run] using same

theorem opens_valTy (value : ValueId) : BoundedRun CurrentOpen (valTy value) :=
  opens_of_state_unchanged (fun env state => by rw [valTy_run]) (fun env state => by rw [valTy_run])

theorem opens_intTyOf (value : ValueId) : BoundedRun CurrentOpen (intTyOf value) :=
  opens_of_state_unchanged
    (fun env state => congrArg LS.blocks (intTyOf_eq (v := value) (le := env) (ls := state) rfl))
    (fun env state => congrArg LS.cur (intTyOf_eq (v := value) (le := env) (ls := state) rfl))

theorem opens_read : BoundedRun CurrentOpen (read : B LEnv) :=
  opens_of_state_unchanged (fun _ _ => rfl) (fun _ _ => rfl)

def LiveOpenRun (action : B α) : Prop :=
  ∀ env before result after, action env before = (result, after) →
    CurrentOpen before → LiveBound before → before.cur.isSome = true → CurrentOpen after

theorem LiveOpenRun.of_bounded {action : B α} (preserves : BoundedRun CurrentOpen action) :
    LiveOpenRun action := fun env before result after run openCurrent bounded _ =>
  preserves env before result after run openCurrent bounded

theorem opens_whenLive_live (default : α) {action : B α} (preserves : LiveOpenRun action) :
    BoundedRun CurrentOpen (whenLive default fun _ => action) := by
  intro env before result after run openCurrent bounded
  cases current : before.cur with
  | none =>
    rw [whenLive_none _ _ env current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact openCurrent
  | some block =>
    rw [whenLive_some _ _ env current] at run
    exact preserves env before result after run openCurrent bounded (by simp [current])

theorem LiveOpenRun.bind {first : B α} {next : α → B β}
    (advance : AdvB first) (preserves : BoundedRun CurrentOpen first)
    (current : ∀ env state, (first env state).2.cur = state.cur)
    (rest : ∀ result, LiveOpenRun (next result)) : LiveOpenRun (first >>= next) := by
  intro env before result after run openCurrent bounded live
  obtain ⟨value, middle, firstRun, nextRun⟩ := bind_eq.mp run
  have middleBound := liveBound_of_adv (advance env before value middle firstRun) bounded
  have middleOpen := preserves env before value middle firstRun openCurrent bounded
  have middleCurrent := current env before
  rw [firstRun] at middleCurrent
  dsimp only at middleCurrent
  exact rest value env middle result after nextRun middleOpen middleBound (by simpa [middleCurrent] using live)

theorem opens_rangeBack (ty : IntTy) (counter : ValueId) (header : BlockId) :
    BoundedRun CurrentOpen (rangeBack ty counter header) := by
  unfold rangeBack
  refine BoundedRun.bind advB_isLive (opens_of_state_unchanged (fun _ _ => rfl) (fun _ _ => rfl)) fun live => ?_
  cases live with
  | false => exact BoundedRun.pure _ _
  | true => exact BoundedRun.bind (advB_emitDef _) (opens_emitDef _) fun _ => opens_emitTerm _

theorem opens_loopBody_live {condition : ValueId} {body : Nat → BlockId → B ValueId} {back : B Unit}
    (bodyAdvance : ∀ depth exit, AdvB (body depth exit)) (backAdvance : AdvB back) :
    LiveOpenRun (loopBody condition body back) := by
  intro env before result after run _ bounded live
  cases current : before.cur with
  | none => simp [current] at live
  | some source =>
    unfold loopBody at run
    simp only [bind_eq] at run
    obtain ⟨state, first, readRun, ⟨bodyBlock, exitBlock⟩, forked, forkRun,
      _, started, startRun, value, bodyEnd, bodyRun, _, backEnd, backRun, exitRun⟩ := run
    have same : first = before := (Prod.mk.inj readRun).2.symm
    subst first
    have targets := fork_open_targets current (bounded source current) condition env
    rw [forkRun] at targets
    obtain ⟨exitBody, exitRow, exitOpen⟩ := targets.2
    have startedRow : started.blocks[exitBlock]? = some exitBody := by
      simpa [setCur_blocks startRun] using exitRow
    have distinct := fork_distinct current forkRun
    have different : started.cur ≠ some exitBlock := by
      rw [setCur_current startRun]
      exact fun equality => distinct (Option.some.inj equality)
    exact restore_currentOpen startedRow exitOpen different
      ((bodyAdvance _ _ env started value bodyEnd bodyRun).trans (backAdvance env bodyEnd _ backEnd backRun)) exitRun

theorem opens_lowerWhile (header : BlockId) {condition : B ValueId} {body : Nat → BlockId → B ValueId}
    (conditionAdvance : AdvB condition) (conditionOpen : BoundedRun CurrentOpen condition)
    (bodyAdvance : ∀ depth exit, AdvB (body depth exit)) :
    BoundedRun CurrentOpen (lowerWhile header condition body) := by
  unfold lowerWhile
  exact BoundedRun.bind conditionAdvance conditionOpen fun _ =>
    opens_whenLive_live _ (opens_loopBody_live bodyAdvance (advB_emitTerm _))

theorem opens_lowerRange (ty : IntTy) (counter bound : ValueId) (header : BlockId)
    {body : Nat → BlockId → B ValueId} (bodyAdvance : ∀ depth exit, AdvB (body depth exit)) :
    LiveOpenRun (lowerRange ty counter bound header body) := by
  unfold lowerRange
  exact LiveOpenRun.bind (advB_emitDef _) (opens_emitDef _) (emitDef_current _) fun _ =>
    opens_loopBody_live bodyAdvance (advB_rangeBack _ _ _)

theorem opens_lowerEach (regrow : Bool) (owner : Option ValueId) (sampled header counter : Nat)
    {body : Nat → BlockId → B ValueId} (bodyAdvance : ∀ depth exit, AdvB (body depth exit)) :
    LiveOpenRun (lowerEach regrow owner sampled header counter body) := by
  unfold lowerEach
  have eachOpen : BoundedRun CurrentOpen (eachLen regrow owner sampled) := by
    cases regrow
    · exact BoundedRun.pure _ _
    · exact opens_emitDef _
  refine LiveOpenRun.bind (advB_eachLen _ _ _) eachOpen (eachLen_current _ _ _) fun _ => ?_
  exact LiveOpenRun.bind (advB_emitDef _) (opens_emitDef _) (emitDef_current _) fun _ =>
    opens_loopBody_live bodyAdvance (advB_rangeBack _ _ _)

end Goose.Lower.Validation
