import Goose.Lower.FuelBoundLeaves
import Goose.Lower.ReflectionEffects

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

theorem FuelBoundAt.eff_step {cx : FnCtx} {pt : Pt} {fr : Frame} {e : Effect}
    {source : Nat → M α} {nextFrame : α → Frame} {sourceFuel fuel : Nat} {state : St}
    (instruction : instAt cx.fn pt = some (.eff e))
    (equal : execEff cx.fn fr e =
      source sourceFuel >>= fun value => pure (nextFrame value)) :
    FuelBoundAt sourceFuel (fuel + 1) cx pt fr source
      (fun value _ pt' fr' => pt' = (pt.1, pt.2 + 1) ∧ fr' = nextFrame value) state := by
  intro result nonTimeout run
  have step : runAt cx pt fr (fuel + 1) state =
      (execEff cx.fn fr e >>= fun frame => runAt cx (pt.1, pt.2 + 1) frame fuel) state := by
    simp only [runAt, instsAt_cons instruction, exec]
  rw [step, bind_apply] at run
  cases effectRun : execEff cx.fn fr e state with
  | ok frame after =>
      rw [effectRun] at run
      have sourceRun := (congrFun equal state).symm.trans effectRun
      change (source sourceFuel >>= fun value => pure (nextFrame value)) state = .ok frame after at sourceRun
      rw [bind_apply] at sourceRun
      cases hsource : source sourceFuel state with
      | stop stop sourceAfter => rw [hsource] at sourceRun; cases sourceRun
      | ok value sourceAfter =>
          rw [hsource] at sourceRun
          cases sourceRun
          exact Or.inl ⟨value, after, (pt.1, pt.2 + 1), nextFrame value,
            fuel, rfl, ⟨rfl, rfl⟩, by omega, run⟩
  | stop stop after =>
      rw [effectRun] at run
      have sourceRun := (congrFun equal state).symm.trans effectRun
      change (source sourceFuel >>= fun value => pure (nextFrame value)) state = .stop stop after at sourceRun
      rw [bind_apply] at sourceRun
      cases hsource : source sourceFuel state with
      | ok value sourceAfter => rw [hsource] at sourceRun; cases sourceRun
      | stop sourceStop sourceAfter =>
          rw [hsource] at sourceRun
          cases sourceRun
          exact Or.inr ⟨stop, after, rfl, run.symm⟩

theorem leaf_eff_fuelBoundAt {cfg : Cfg} {env : Env} {cx : FnCtx}
    {ls lsk ls1 : LS} {fr frk : Frame} {ptk : Pt} {cellsk : List (ValueId × RVal)}
    {fuel sourceFuel : Nat} {state : St}
    (hP : Post cfg env cx ls fr lsk frk ptk cellsk) {e : Effect} {le : LEnv}
    (emit : emitEffect e le lsk = ((), ls1)) (hext : ExtT ls1 cx.fn.blocks)
    {source : Nat → M α}
    (equal : execEff cx.fn frk e = source sourceFuel >>= fun _ => pure frk) :
    FuelBoundAt sourceFuel (fuel + 1) cx ptk frk source
      (fun _ _ pt' fr' => Post cfg env cx ls fr ls1 fr' pt' []) state := by
  obtain ⟨post, instruction⟩ := Post.eff_leaf hP emit hext
  refine (FuelBoundAt.eff_step instruction equal).mono ?_
  intro value after pt' fr' matched
  rcases matched with ⟨rfl, rfl⟩
  exact post


theorem normalEffectFuelBound {cfg : Cfg} {env : Env} {cx : FnCtx}
    {ls lsk ls1 : LS} {fr frk : Frame} {ptk : Pt} {cells : List (ValueId × RVal)}
    {fuel sourceFuel : Nat} {state : St} {e : Effect}
    (post : Post cfg env cx ls fr lsk frk ptk cells) {le : LEnv}
    (emit : emitEffect e le lsk = ((), ls1)) (extension : ExtT ls1 cx.fn.blocks)
    {result : Type} {source : Nat → M result}
    (equal : execEff cx.fn frk e = source sourceFuel >>= fun _ => pure frk) :
    FuelBoundAt sourceFuel fuel cx ptk frk (fun n => source n >>= fun _ => pure (Flow.normal .unit))
      (fun flow _ pt' fr' => flow = .normal .unit ∧ Post cfg env cx ls fr ls1 fr' pt' []) state := by
  cases fuel with
  | zero => exact FuelBoundAt.zero sourceFuel cx ptk frk _ _ state
  | succ fuel =>
      have effect := leaf_eff_fuelBoundAt (fuel := fuel) (sourceFuel := sourceFuel)
        (state := state) post emit extension (source := source) equal
      have completed : FuelBoundAt sourceFuel (fuel + 1) cx ptk frk
          (fun n => source n >>= fun _ => pure (Flow.normal .unit))
          (fun flow _ pt' fr' => flow = .normal .unit ∧ Post cfg env cx ls fr ls1 fr' pt' []) state := by
        refine effect.bind ?_
        intro value after pt' fr' sourceRun matched residual bound
        exact FuelBoundAt.ret (sourceFuel := sourceFuel) (targetFuel := residual) ⟨rfl, matched⟩
      exact completed


end Goose.Lower
