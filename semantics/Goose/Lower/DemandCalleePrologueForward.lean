import Goose.Lower.DemandCalleeEntry

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence
open Goose.Proofs.Lower (extT_finish bodyTail)

theorem accepted_callee_parameter_prologue_trace {cfg : Cfg} {ctx : Context} {impl : Impl}
    {act depth : Nat} {values : List Val} {state : St}
    (source : BlockSource cfg ⟨impl.vars, act, [], depth⟩
      ((impl.params.toList.zip values).map fun (parameter, value) => (parameter.var, value)) impl.body state)
    (arity : impl.params.size = values.length) (count : Nat) (bound : count ≤ values.length) :
    DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ (count + 1)
      ⟨(0, 0), callFrame impl act depth values, state⟩
      ⟨(0, 1 + count), { (callFrame impl act depth values) with scopes := [(impl.body.scope, state.nextScope)] },
        { state with nextScope := state.nextScope + 1, store := preStore act state.nextScope (((impl.params.toList.zip values).map fun (parameter, value) => (parameter.var, value)).take count) state.store }⟩ := by
  let le := lowerEnv cfg.mod impl.vars impl.results.toList
  let body := lowerBlock none (callPre impl) false impl.body le (callEntry impl)
  have tailExtension : ExtT (bodyTail impl le body.1 body.2) (lowerContextAt cfg.mod ctx impl).blocks := by
    rw [lowerContextAt_blocks, lowerImpl_call_blocks]
    exact extT_finish _
  have bodyExtension := tailExtension.of_adv
    (advB_finishFunction impl body.1 le body.2 (finishFunction impl body.1 le body.2).1
      (bodyTail impl le body.1 body.2) rfl)
  have trace := accepted_block_parameter_prologue_trace source
    (cx := ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩) (by rfl)
    (callEntry_pp impl) bodyExtension (callFrame_rel cfg.mod cfg.profile ctx impl act depth values)
    (callFrame_preRel impl act depth values arity) count (by simp [arity, bound])
  obtain ⟨_, scopes, _⟩ := bindCallParams_frame ⟨act, [], {}, depth⟩
    ((List.range impl.params.size).zip (callEntryTypes impl)) (values.map RVal.val)
  simpa only [callFrame, scopes] using trace

#print axioms accepted_callee_parameter_prologue_trace
end Goose.Lower
