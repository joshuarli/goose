import Goose.Lower.ReflectionCallEntry
import Goose.Lower.ReflectionReferences

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

theorem typedExprReflection_call {fuel : Nat} {cfg : Cfg} {results : List Ty}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (args : TypedArgsReflection fuel cfg results arguments)
    (blocks : ∀ bodyFuel, bodyFuel < fuel → ∀ ctx impl,
      cfg.mod.contexts[context]? = some ctx → cfg.mod.impls[ctx.impl]? = some impl →
      ∀ pre, TypedBlockReflection bodyFuel cfg impl.results.toList none (callPre impl) pre false impl.body) :
    TypedExprReflection fuel cfg results (.call context arguments origin) := by
  intro env state source metadata ls ls' resultId pt cx fr lowering point extension rel moduleEq resultsEq generated
  let sources : ∀ n, ArgsSource n cfg env arguments state := fun n =>
    Classical.choose (source.callArgs n results metadata)
  have sourceMetadata : ∀ n, (sources n).resultsMatch results := fun n =>
    Classical.choose_spec (source.callArgs n results metadata)
  obtain ⟨ids,middle,after,argsRun,definition,tail⟩ := lowerExpr_call_split lowering
  have afterExtension : ExtT after cx.fn.blocks := by
    rcases tail with ⟨_,term⟩ | ⟨_,rfl⟩
    · exact extension.of_adv (adv_emitTerm term)
    · exact extension
  have middleExtension := afterExtension.of_adv (adv_emitDef definition)
  have first := args env state sources sourceMetadata ls middle ids pt cx fr argsRun point middleExtension
    rel moduleEq resultsEq generated
  have composition : ReflectAtFuel fuel cx pt fr
      (fun n => mapList (evalArg n cfg env) arguments >>= fun values => Core.enterCall n cfg env.depth context values)
      (fun value _ pt' fr' => Post cfg env cx ls fr ls' fr' pt' [(resultId,.val value)]) state := by
    refine first.bind ?_
      (fun n k bound => MonoM.mapList (fun arg => (monoAll n k bound).arg cfg env arg) arguments)
      (fun values n k bound => (monoAll n k bound).call cfg env.depth context values)
    intro n values afterArgs pt1 fr1 argsDone matched residual bound
    obtain ⟨length,post⟩ := matched
    have readValues := mapList_getVal_cells length post.has
    have instruction := (Post.def_leaf post definition afterExtension (.val .unit)).2
    have targetCfg : cx.cfg = ⟨cfg.profile,lower cfg.mod⟩ := by
      cases actual : cx.cfg
      simp only [actual] at moduleEq
      have profile := post.rel.prof
      simp only [actual] at profile
      cases moduleEq
      cases profile
      rfl
    cases residual with
    | zero => exact ReflectAtFuel.zero cx pt1 fr1 _ _ afterArgs
    | succ operationFuel =>
      have operation : ReflectMFuel operationFuel
          (fun n => Core.enterCall n cfg env.depth context values >>= fun value => pure (.val value))
          (fun n => execOp n cx fr1 (.call context ids (some origin))) afterArgs := by
        cases operationFuel with
        | zero => exact ReflectMFuel.of_timeout rfl
        | succ callFuel =>
          obtain ⟨ctx,impl,contextAt,implAt,bodySource,typing,roots, _, _⟩ := source.calleeAfterArgs n values argsDone
          have call : ReflectMFuel callFuel (fun n => Core.enterCall n cfg env.depth context values)
              (fun n => GIR.callFn n cx.cfg fr1.depth context values) afterArgs := by
            rw [targetCfg,post.rel.depth]
            apply callFn_reflect_of_source contextAt implAt bodySource
            · simp [typing,Core.Sound.implEnv]
            · simpa using congrArg PEnv.impl roots
            · simpa [Core.Sound.implEnv] using congrArg TEnv.loops typing
            · intro bodyFuel equal
              exact blocks bodyFuel (by omega) ctx impl contextAt implAt _
          exact ReflectMFuel.call_op readValues call
      have called := ReflectAtFuel.def_step RVal.val instruction operation
      rcases tail with ⟨noReturn,_⟩ | ⟨_,rfl⟩
      · refine called.mono_success ?_
        intro callFuel value afterValue pt' fr' callDone matched
        exact (Core.Sound.noReturn_sound cfg.mod cfg.profile context noReturn callFuel env.depth values
          afterArgs value afterValue callDone).elim
      · refine called.mono ?_
        intro value afterValue pt' fr' matched
        obtain ⟨rfl,rfl⟩ := matched
        exact (Post.def_leaf post definition extension (.val value)).1
  exact composition.of_source (fun n => ⟨n + 1,by simp only [evalExpr]⟩)

end Goose.Lower
