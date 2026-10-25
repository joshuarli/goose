import Goose.Lower.ReflectionFuel
import Goose.Lower.ContextLowering

namespace Goose.Lower

open Goose.Core Goose.GIR

theorem ReflectMFuel.callFn_of_body {cfg : Cfg} {context : ContextId} {ctx : Context} {impl : Impl}
    {depth fuel : Nat} {values : List Val} {state : St} {entryInsts : List Inst} {entryFrame : Frame}
    (contextAt : cfg.mod.contexts[context]? = some ctx)
    (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (arguments : impl.params.size = values.length) (below : depth < maxCallDepth)
    (entry : enterBlock (lowerContextAt cfg.mod ctx impl)
      ⟨state.nextAct,[],{},depth + 1⟩ 0 (values.map RVal.val) = pure (entryInsts,entryFrame))
    (body : ReflectMFuel fuel
      (fun n => Core.execBlock n cfg ⟨impl.vars,state.nextAct,[],depth + 1⟩
        ((impl.params.toList.zip values).map fun (parameter,value) => (parameter.var,value)) impl.body
          >>= expectReturned)
      (fun n => GIR.exec n ⟨⟨cfg.profile,lower cfg.mod⟩,lowerContextAt cfg.mod ctx impl⟩
        entryFrame entryInsts)
      {state with nextAct := state.nextAct + 1}) :
    ReflectMFuel (fuel + 2) (fun n => Core.enterCall n cfg depth context values)
      (fun n => GIR.callFn n ⟨cfg.profile,lower cfg.mod⟩ depth context values) state := by
  have functionAt := lower_func_at contextAt implAt
  have parameters : (lowerContextAt cfg.mod ctx impl).params.length = values.length := by
    change (impl.params.toList.map fun parameter => tyOfVar impl parameter.var).length = values.length
    simpa using arguments
  have targetStep : GIR.callFn (fuel + 2) ⟨cfg.profile,lower cfg.mod⟩ depth context values state =
      GIR.exec fuel ⟨⟨cfg.profile,lower cfg.mod⟩,lowerContextAt cfg.mod ctx impl⟩
        entryFrame entryInsts {state with nextAct := state.nextAct + 1} := by
    simp only [GIR.callFn, Nat.not_le_of_lt below, ↓reduceIte, lookupFn, functionAt, pure_bind,
      enterFn, parameters, freshAct, bind_apply, pure_apply, entry]
  intro result nonTimeout run
  change GIR.callFn (fuel + 2) ⟨cfg.profile,lower cfg.mod⟩ depth context values state = result at run
  rw [targetStep] at run
  obtain ⟨sourceFuel, source⟩ := body result nonTimeout run
  refine ⟨sourceFuel + 1, ?_⟩
  change Core.enterCall (sourceFuel + 1) cfg depth context values state = result
  simp only [Core.enterCall, Nat.not_le_of_lt below, ↓reduceIte, lookupContext, lookupImpl,
    contextAt, implAt, pure_bind, arguments, freshAct, bind_apply, pure_apply]
  exact source

end Goose.Lower
