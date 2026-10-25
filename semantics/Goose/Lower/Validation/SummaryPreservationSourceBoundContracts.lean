import Goose.Lower.Validation.SummaryPreservationReplayTypedBounds

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

def BoundReplayAt (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (target : Core.Eff) (scopeCount : Nat)
    (bound : Bound) (initial : LS) (upper : Prov) : Prop :=
  ∀ start finish before after,
    Core.tyBound typingEnv bound start = .ok ((), finish) →
    rpBound env bound before = .ok ((), after) →
    EffectRefinement (lowerContextAt env.mod env.ctx env.impl) after.eff target →
    ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
      (typedContextSlotUpper env.mod env.ctx env.impl) initial upper →
    GeneratedBuilderState initial → NativeRows vt (lowerBound bound
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 →
    ∃ next, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
        (typedContextSlotUpper env.mod env.ctx env.impl)
        (lowerBound bound (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 next ∧
      ((lowerBound bound (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2.cur.isSome = true →
        ∀ value ∈ (lowerBound bound (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).1.uses,
          value < (lowerBound bound (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2.vals.size) ∧
      ∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old

theorem boundReplay_of_expression {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat} {bound : Bound} {initial : LS} {upper : Prov}
    (child : ∀ expression, bound = .expr expression ∨ bound = .fromEnd expression →
      ExpressionReplayAt typingEnv env results vt target scopeCount expression initial upper) :
    BoundReplayAt typingEnv env results vt target scopeCount bound initial upper := by
  intro start finish before after typed replay ceiling ready generated native
  exact ReplayBuilder.typedBound typed replay ceiling ready generated native child

#print axioms boundReplay_of_expression

end Goose.Lower.Validation.SummaryPreservation
