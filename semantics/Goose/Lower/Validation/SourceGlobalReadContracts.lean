import Goose.Lower.Validation.SummaryPreservationReplayValue
import Goose.Lower.Validation.SummaryPreservationReplayNativeTypes
import Goose.Lower.Validation.SourceGlobalReadShape
import Goose.Lower.Validation.SummaryPreservationSourceEffectCeiling

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

def GlobalExpressionReplayAt (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (func : Func) (returnTypes : List Ty) (slots : Array (List RootRef)) (target : Core.Eff) (scopeCount : Nat)
    (expression : Expr) (initial : LS) (upper : Prov) : Prop :=
  ∀ type start finish before after sourceRoots,
    tyExpr typingEnv expression start = .ok (type, finish) →
    rpExpr env expression before = .ok (sourceRoots, after) →
    EffectRefinement func after.eff target →
    ReplayBuilder (lower env.mod) results vt func target
      (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
      slots initial upper →
    GeneratedBuilderState initial →
    NativeRows vt (lowerExpr expression (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    ∃ next, ReplayBuilder (lower env.mod) results vt func target
        (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
        slots
        (lowerExpr expression (lowerEnv env.mod env.impl.vars returnTypes) initial).2 next ∧
      ((lowerExpr expression (lowerEnv env.mod env.impl.vars returnTypes) initial).2.cur.isSome = true →
        ReplayValue func next
          (lowerExpr expression (lowerEnv env.mod env.impl.vars returnTypes) initial).2
          (lowerExpr expression (lowerEnv env.mod env.impl.vars returnTypes) initial).1 sourceRoots (.data type)) ∧
      ∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old

def GlobalPlaceReplayAt (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (func : Func) (returnTypes : List Ty) (slots : Array (List RootRef)) (target : Core.Eff) (scopeCount : Nat)
    (place : Place) (initial : LS) (upper : Prov) : Prop :=
  ∀ info start finish before after sourceRoots,
    tyPlace typingEnv place start = .ok (info, finish) →
    rpPlace env place before = .ok (sourceRoots, after) →
    EffectRefinement func after.eff target →
    ReplayBuilder (lower env.mod) results vt func target
      (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
      slots initial upper →
    GeneratedBuilderState initial →
    NativeRows vt (lowerPlace place (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    ∃ next, ReplayBuilder (lower env.mod) results vt func target
        (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
        slots
        (lowerPlace place (lowerEnv env.mod env.impl.vars returnTypes) initial).2 next ∧
      ((lowerPlace place (lowerEnv env.mod env.impl.vars returnTypes) initial).2.cur.isSome = true →
        (lowerPlace place (lowerEnv env.mod env.impl.vars returnTypes) initial).1 <
          (lowerPlace place (lowerEnv env.mod env.impl.vars returnTypes) initial).2.vals.size ∧
        RootsRefine func
          (rootsAt next.vals (lowerPlace place (lowerEnv env.mod env.impl.vars returnTypes) initial).1) sourceRoots) ∧
      ∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old

def GlobalViewReplayAt (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (func : Func) (returnTypes : List Ty) (slots : Array (List RootRef)) (target : Core.Eff) (scopeCount : Nat)
    (view : View) (initial : LS) (upper : Prov) : Prop :=
  ∀ info start finish before after sourceRoots,
    tyView typingEnv view start = .ok (info, finish) →
    rpView env view before = .ok (sourceRoots, after) →
    EffectRefinement func after.eff target →
    ReplayBuilder (lower env.mod) results vt func target
      (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
      slots initial upper →
    GeneratedBuilderState initial →
    NativeRows vt (lowerView view (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    ∃ next, ReplayBuilder (lower env.mod) results vt func target
        (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
        slots
        (lowerView view (lowerEnv env.mod env.impl.vars returnTypes) initial).2 next ∧
      ((lowerView view (lowerEnv env.mod env.impl.vars returnTypes) initial).2.cur.isSome = true →
        ReplayValue func next
          (lowerView view (lowerEnv env.mod env.impl.vars returnTypes) initial).2
          (lowerView view (lowerEnv env.mod env.impl.vars returnTypes) initial).1 sourceRoots (.view .readOnly info.1)) ∧
      ∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old

end Goose.Lower.Validation.SummaryPreservation
