import Goose.Lower.Validation.ExpressionContentsRules
import Goose.Lower.Validation.ExpressionTypingCallOps

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem FreshContentsEvidence.emitUnreachable {le : LEnv} {first : Nat} {before after : LS}
    {value : ValueId} (evidence : FreshContentsEvidence le first before value)
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (run : emitTerm .unreachable le before = ((), after)) :
    FreshContentsEvidence le first after value := by
  apply evidence.of_framed_run (loop := none) run (dense_emitTerm _) (advB_emitTerm _)
    (types_emitTerm _) (generatedTargetFrame_emitTerm none _ (by simp [Term.successors])) checked bounded
  trivial

theorem lowerExpr_call_fresh_contents_of_args {env : Core.TEnv} {context : ContextId} {args : List Arg}
    {origin : OriginId} {target : Ty} {start finish : Nat}
    (source : Core.tyExpr env (.call context args origin) start = .ok (.ref .mutable target, finish))
    {results : List Ty} {before middle emitted after : LS} {values : List ValueId} {value : ValueId}
    {current : BlockId}
    (argsRun : lowerArgs args (lowerEnv env.mod env.vars results) before = (values, middle))
    (argsTyped : ∀ ctx callee, env.mod.contexts[context]? = some ctx → env.mod.impls[ctx.impl]? = some callee →
      ∃ params, (lowerEnv env.mod env.vars results).sigs[context]? = some (params, callee.results.toList) ∧
        PassableValues middle params values)
    (checked : middle.DenseDefinitions) (bounded : LiveBound middle) (live : middle.cur = some current)
    (emitRun : emitDef (.call context values (some origin)) (lowerEnv env.mod env.vars results) middle = (value, emitted))
    (run : lowerExpr (.call context args origin) (lowerEnv env.mod env.vars results) before = (value, after)) :
    FreshContentsEvidence (lowerEnv env.mod env.vars results) middle.vals.size after value := by
  obtain ⟨ctx, callee, _, _, _, contextRow, calleeRow, _, _, resultSource⟩ := tyExpr_call_tables source
  obtain ⟨params, signature, typed⟩ := argsTyped ctx callee contextRow calleeRow
  have operation := call_resultTy_of_passable signature typed resultSource origin
  have evidence := freshContentsEvidence_intrinsic (.call ..) operation checked bounded live emitRun
  have tailRun := run
  simp only [lowerExpr, bind_run, argsRun, emitRun] at tailRun
  have reader : (read : B LEnv) (lowerEnv env.mod env.vars results) emitted =
      (lowerEnv env.mod env.vars results, emitted) := rfl
  simp only [reader] at tailRun
  by_cases noReturn : (lowerEnv env.mod env.vars results).mod.noReturn context = true
  · simp only [noReturn, ite_true, bind_run, pure_run] at tailRun
    have afterEq : (emitTerm .unreachable (lowerEnv env.mod env.vars results) emitted).2 = after :=
      congrArg Prod.snd tailRun
    have termRun : emitTerm .unreachable (lowerEnv env.mod env.vars results) emitted = ((), after) := by
      exact Prod.ext (Subsingleton.elim _ _) afterEq
    have dense := dense_emitDef _ _ _ _ _ emitRun checked bounded
    exact evidence.emitUnreachable dense.1 dense.2.1 termRun
  · have isFalse : (lowerEnv env.mod env.vars results).mod.noReturn context = false := Bool.eq_false_iff.mpr noReturn
    simp only [isFalse, Bool.false_eq_true, ite_false, pure_run] at tailRun
    have same : emitted = after := congrArg Prod.snd tailRun
    simpa only [same] using evidence

#print axioms FreshContentsEvidence.emitUnreachable
#print axioms lowerExpr_call_fresh_contents_of_args

end Goose.Lower.Validation
