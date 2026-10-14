import Goose.Lower.EFlow
import Goose.Lower.Call

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Lower

theorem calleeBlockClaim_of_simulation {m : Core.Module} {i : ImplId} {impl : Impl}
    (hcheck : checkImpl m impl = .ok ()) (profile : NumProfile) (n : Nat)
    (hbody : ∀ pre, BlockESimulation n ⟨profile, m⟩ none (callPre impl) pre false impl.body) :
    CalleeBlockClaim n ⟨profile, m⟩ i impl := by
  intro act depth values hp
  let le := lowerEnv m impl.vars
  let body := lowerBlock none (callPre impl) false impl.body le (callEntry impl)
  let cx : FnCtx := ⟨⟨profile, lower m⟩, lowerImplAt m i impl⟩
  let fr := callFrame impl act depth values
  let env : Env := ⟨impl.vars, act, [], depth⟩
  have hlow : lowerBlock none (callPre impl) false impl.body le (callEntry impl) =
      (body.1, body.2) := (Prod.eta body).symm
  have hextTail : ExtT (bodyTail impl le body.1 body.2) cx.fn.blocks := by
    rw [lowerImplAt_call_blocks]
    exact extT_finish _
  have hextBody : ExtT body.2 cx.fn.blocks := hextTail.of_adv
    (advB_finishFunction impl body.1 le body.2 (finishFunction impl body.1 le body.2).1
      (bodyTail impl le body.1 body.2) rfl)
  have hs := hbody ((impl.params.toList.zip values).map fun (p, value) => (p.var, value))
    env (callPre_scopes hcheck) le (callEntry impl) body.2 body.1 (0, 0) cx fr
    hlow (callEntry_pp impl) hextBody (callFrame_rel m profile i impl act depth values)
    (callFrame_preRel impl act depth values hp) rfl rfl
  rw [prepareReturn_no_scopes env rfl, bind_pure] at hs
  exact hs

end Goose.Lower
