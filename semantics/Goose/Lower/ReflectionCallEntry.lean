import Goose.Lower.ReflectionCalls
import Goose.Lower.ReflectionBlocks
import Goose.Lower.ReflectionEffects
import Goose.Lower.TypedCall

namespace Goose.Lower

open Goose.Core Goose.GIR
open Goose.Proofs.Lower (extT_finish bodyTail bodyTail_cases)

theorem callFn_reflect_of_typedBlock {cfg : Cfg} {context : ContextId} {ctx : Context} {impl : Impl}
    {fuel depth : Nat} {values : List Val} {state : St}
    (contextAt : cfg.mod.contexts[context]? = some ctx)
    (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (arguments : impl.params.size = values.length) (below : depth < maxCallDepth)
    (source : BlockSource cfg ⟨impl.vars,state.nextAct,[],depth + 1⟩
      ((impl.params.toList.zip values).map fun (parameter,value) => (parameter.var,value))
      impl.body {state with nextAct := state.nextAct + 1})
    (typing : source.typingEnv.impl = some impl) (roots : source.rootsEnv.impl = impl)
    (loops : source.typingEnv.loops = 0)
    (block : TypedBlockReflection fuel cfg impl.results.toList none (callPre impl)
      ((impl.params.toList.zip values).map fun (parameter,value) => (parameter.var,value)) false impl.body) :
    ReflectMFuel (fuel + 2) (fun n => Core.enterCall n cfg depth context values)
      (fun n => GIR.callFn n ⟨cfg.profile,lower cfg.mod⟩ depth context values) state := by
  let le := lowerEnv cfg.mod impl.vars impl.results.toList
  let env : Env := ⟨impl.vars,state.nextAct,[],depth + 1⟩
  let cx : FnCtx := ⟨⟨cfg.profile,lower cfg.mod⟩,lowerContextAt cfg.mod ctx impl⟩
  let fr := callFrame impl state.nextAct (depth + 1) values
  let body := lowerBlock none (callPre impl) false impl.body le (callEntry impl)
  let pre := (impl.params.toList.zip values).map fun (parameter,value) => (parameter.var,value)
  let initial := {state with nextAct := state.nextAct + 1}
  have metadata : SourceResults source.typingEnv source.rootsEnv impl.results.toList := by
    intro actual lookup
    rw [typing] at lookup
    cases lookup
    exact ⟨roots,rfl⟩
  have extensionTail : ExtT (bodyTail impl le body.1 body.2) cx.fn.blocks := by
    rw [lowerContextAt_blocks,lowerImpl_call_blocks]
    exact extT_finish _
  have extensionBody : ExtT body.2 cx.fn.blocks := extensionTail.of_adv
    (advB_finishFunction impl body.1 le body.2 (finishFunction impl body.1 le body.2).1
      (bodyTail impl le body.1 body.2) rfl)
  have extensionEntry : ExtT (callEntry impl) cx.fn.blocks := extensionBody.of_adv
    (advB_lowerBlock none (callPre impl) false impl.body le (callEntry impl) body.1 body.2 rfl)
  have reflected := block.function env initial source metadata loops (callEntry impl) body.2 body.1
    (0,0) cx fr rfl (callEntry_pp impl) extensionBody
    (callFrame_rel cfg.mod cfg.profile ctx impl state.nextAct (depth + 1) values)
    (callFrame_preRel impl state.nextAct (depth + 1) values arguments) rfl rfl
    (callEntry_generated cfg.mod impl)
  simp only [prepareReturn_no_scopes env rfl,bind_pure] at reflected
  have returned : ReflectMFuel fuel (fun n => execBlock n cfg env pre impl.body >>= expectReturned)
      (fun n => runAt cx (0,0) fr n) initial := by
    refine reflected.complete_expectReturned ?_
    intro n flow after pt' fr' done matched
    rcases matched with ⟨value,rfl,unitValue,post⟩ | ⟨value,origin,rfl,site⟩
    · have nondivergent := SourceDivergence.normalBlock_diverges_false n cfg env pre impl.body initial after value done
      rcases bodyTail_cases impl le body.1 body.2 nondivergent with ⟨closed,_⟩ | ⟨current,live,term⟩
      · obtain ⟨row,point,_⟩ := LS.pp_some post.pp
        rw [closed] at point
        cases point
      obtain ⟨_,_,_,instruction⟩ := emitTerm_facts term post.pp extensionTail
      change instAt cx.fn pt' = some (.term (.ret (if impl.body.value.isSome then [body.1] else []) none)) at instruction
      refine ⟨value,Or.inl rfl,_,none,instruction,?_⟩
      cases hasValue : impl.body.value.isSome with
      | false =>
        have noValue : impl.body.value = none := by simpa using hasValue
        exact Or.inl ⟨by simp,unitValue noValue⟩
      | true =>
        exact Or.inr ⟨body.1,by simp,post.has (body.1,.val value) (by simp [blockCells,hasValue])⟩
    · obtain ⟨ids,instruction,result⟩ := site.instruction
      exact ⟨value,Or.inr rfl,ids,some origin,instruction,result⟩
  obtain ⟨entry,entryAt,entryParameters⟩ := extensionEntry.params (b := 0)
    (blk := ⟨(List.range impl.params.size).zip (callEntryTypes impl),#[]⟩) rfl
  have insts : instsAt cx.fn (0,0) = entry.insts := by simp [instsAt,entryAt]
  have entryLength : ((List.range impl.params.size).zip (callEntryTypes impl)).length = values.length := by
    simp [callEntryTypes,arguments]
  have entered : enterBlock cx.fn ⟨state.nextAct,[],{},depth + 1⟩ 0 (values.map RVal.val) =
      pure (entry.insts,fr) := by
    simp only [enterBlock,entryAt,entryParameters,List.length_map,entryLength,↓reduceIte,
      bindParams_call,pure_bind]
    rfl
  apply ReflectMFuel.callFn_of_body contextAt implAt arguments below entered
  simpa only [runAt,insts] using returned

theorem callFn_reflect_of_source {cfg : Cfg} {context : ContextId} {ctx : Context} {impl : Impl}
    {fuel depth : Nat} {values : List Val} {state : St}
    (contextAt : cfg.mod.contexts[context]? = some ctx)
    (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (source : BlockSource cfg ⟨impl.vars,state.nextAct,[],depth + 1⟩
      ((impl.params.toList.zip values).map fun (parameter,value) => (parameter.var,value))
      impl.body {state with nextAct := state.nextAct + 1})
    (typing : source.typingEnv.impl = some impl) (roots : source.rootsEnv.impl = impl)
    (loops : source.typingEnv.loops = 0)
    (blocks : ∀ bodyFuel, bodyFuel + 2 = fuel →
      TypedBlockReflection bodyFuel cfg impl.results.toList none (callPre impl)
        ((impl.params.toList.zip values).map fun (parameter,value) => (parameter.var,value)) false impl.body) :
    ReflectMFuel fuel (fun n => Core.enterCall n cfg depth context values)
      (fun n => GIR.callFn n ⟨cfg.profile,lower cfg.mod⟩ depth context values) state := by
  cases fuel with
  | zero => exact ReflectMFuel.of_timeout rfl
  | succ fuel =>
    by_cases above : depth ≥ maxCallDepth
    · exact ReflectMFuel.of_timeout (by simp only [callFn,above,↓reduceIte]; rfl)
    · cases fuel with
      | zero =>
        exact ReflectMFuel.of_timeout (by
          simp only [callFn,above,↓reduceIte,lookupFn_lower contextAt implAt,pure_bind,enterFn]
          rfl)
      | succ bodyFuel =>
        by_cases arguments : impl.params.size = values.length
        · exact callFn_reflect_of_typedBlock contextAt implAt arguments (by omega) source typing roots loops
            (blocks bodyFuel rfl)
        · apply ReflectMFuel.of_eq (sourceFuel := 1)
          have parameters : (lowerContextAt cfg.mod ctx impl).params.length = impl.params.size := by
            simp [lowerContextAt,lowerImpl]
          simp only [callFn,above,↓reduceIte,lookupFn_lower contextAt implAt,pure_bind,enterFn,parameters,
            arguments,Core.enterCall,lookupContext,lookupImpl,contextAt,implAt]

end Goose.Lower

