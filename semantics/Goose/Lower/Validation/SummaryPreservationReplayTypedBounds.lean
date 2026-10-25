import Goose.Lower.Validation.SummaryPreservationReplayTypedPlacesContracts
import Goose.Lower.Validation.ExpressionTypingSliceOps

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

theorem typedBound {typingEnv : TEnv} {env : PEnv} {bound : Bound} {start finish : Nat}
    {before after : RState} {results : Array (List RootRef)} {vt : Array (Option VTy)}
    {target : Core.Eff} {scopeCount : Nat} {ls : LS} {upper : Prov}
    (source : tyBound typingEnv bound start = .ok ((), finish))
    (replayed : rpBound env bound before = .ok ((), after))
    (wholeEffect : EffectRefinement (lowerContextAt env.mod env.ctx env.impl) after.eff target)
    (ready : ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
      (typedContextSlotUpper env.mod env.ctx env.impl) ls upper)
    (generated : GeneratedBuilderState ls)
    (native : NativeRows vt (lowerBound bound (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2)
    (expressionChild : ∀ expression, bound = .expr expression ∨ bound = .fromEnd expression →
      ExpressionReplayAt typingEnv env results vt target scopeCount expression ls upper) :
    ∃ next, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
        (typedContextSlotUpper env.mod env.ctx env.impl)
        (lowerBound bound (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2 next ∧
      ((lowerBound bound (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2.cur.isSome = true →
        ∀ value ∈ (lowerBound bound (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).1.uses,
          value < (lowerBound bound (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2.vals.size) ∧
      ∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old := by
  cases bound with
  | omitted => exact ⟨upper, ready, by simp [lowerBound, pure_run, Bnd.uses], fun _ _ => rfl⟩
  | expr expression | fromEnd expression =>
    obtain ⟨integer, childFinish, childTyped⟩ := tyBound_child source
    obtain ⟨roots, middle, childReplay, tail⟩ := (st_bind_ok _ _ _ _).mp replayed
    have sourceEq := congrArg Prod.snd ((st_pure_ok _ _ _).mp tail)
    dsimp only at sourceEq
    subst after
    obtain ⟨next, nextReady, value, retained⟩ := expressionChild expression (by simp)
      (.int integer) start childFinish before middle roots childTyped childReplay wholeEffect ready generated native
    refine ⟨next, nextReady, ?_, retained⟩
    intro live
    simpa [lowerBound, bind_run, pure_run, Bnd.uses] using (value live).bound

#print axioms typedBound

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
