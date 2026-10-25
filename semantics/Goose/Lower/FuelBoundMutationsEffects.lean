import Goose.Lower.FuelBoundLeaves
import Goose.Lower.FuelBoundControlSteps

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

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
