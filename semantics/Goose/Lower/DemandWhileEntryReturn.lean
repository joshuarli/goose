import Goose.Lower.DemandWhileSourceEntryStop

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Proofs.Lower

theorem runtimeStep_excludes_return {cx : FnCtx} {before after : DemandRuntimePoint} {values : List ValueId} {origin : Option OriginId}
    (instruction : instAt cx.fn before.point = some (.term (.ret values origin)))
    (step : Evidence.RuntimeStep cx.cfg cx.fn before.point before.frame before.state after.point after.frame after.state) : False := by
  cases before
  cases after
  cases step with
  | define found _ => cases instruction.symm.trans found
  | effect found _ => cases instruction.symm.trans found
  | branch found _ _ => cases instruction.symm.trans found
  | branchTrue found _ _ _ => cases instruction.symm.trans found
  | branchFalse found _ _ _ => cases instruction.symm.trans found

theorem accepted_generated_entry_body_return {cfg : Cfg} {state bodyState : St} {ctx : Context} {impl : Impl}
    {globalFuel : Nat} (accepted : Core.validate cfg.mod = .ok ())
    (initialized : Core.initGlobals globalFuel cfg (List.range cfg.mod.globals.size) St.initial = .ok () state)
    (contextAt : cfg.mod.contexts[cfg.mod.entry]? = some ctx) (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (noValue : impl.body.value = none)
    (source : BlockSource cfg ⟨impl.vars, state.nextAct, [], 1⟩ [] impl.body { state with nextAct := state.nextAct + 1 })
    {map required : RetainedSsaMap} {frame : GIR.Frame} {point : Pt}
    (ended : GeneratedBranchBlockEnd source map required
      ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ impl.results.toList
      (callEntry impl) none (callFrame impl state.nextAct 1 []) (.normal .unit) ⟨point, frame, bodyState⟩) :
    instAt (lowerContextAt cfg.mod ctx impl) point = some (.term (.ret [] none)) ∧
    ∀ fuel, GIR.runAt ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ point frame (fuel + 1) bodyState =
      .ok .unit bodyState := by
  obtain ⟨actualCtx, actualImpl, actualContextAt, actualImplAt, noParameters, noResults, _⟩ :=
    acceptedEntryAfterGlobals accepted globalFuel initialized
  have ctxEq : actualCtx = ctx := Option.some.inj (actualContextAt.symm.trans contextAt)
  subst actualCtx
  have implEq : actualImpl = impl := Option.some.inj (actualImplAt.symm.trans implAt)
  subst actualImpl
  have emptyResults : impl.results = #[] := Array.toList_eq_nil_iff.mp noResults
  have preEmpty : callPre impl = [] := by simp [callPre, noParameters]
  let le := lowerEnv cfg.mod impl.vars impl.results.toList
  let body := lowerBlock none [] false impl.body le (callEntry impl)
  have bodyPoint : body.2.pp = some point := ended.post.pp
  obtain ⟨block, current, _, _⟩ := LS.pp_some bodyPoint
  have tailRun : emitTerm (.ret [] none) le body.2 = ((), bodyTail impl le body.1 body.2) := by
    unfold bodyTail
    simp [finishFunction, emptyResults, noValue, bind_run, isLive_run current, le]
  have tailExt : ExtT (bodyTail impl le body.1 body.2) (lowerContextAt cfg.mod ctx impl).blocks := by
    rw [lowerContextAt_blocks, lowerImpl_call_blocks, preEmpty]
    exact extT_finish _
  have instruction := (emitTerm_facts tailRun bodyPoint tailExt).2.2.2
  refine ⟨instruction, ?_⟩
  intro fuel
  simp [GIR.runAt, instsAt_cons instruction, GIR.exec, pure_apply]

#print axioms runtimeStep_excludes_return
#print axioms accepted_generated_entry_body_return
end Goose.Lower
