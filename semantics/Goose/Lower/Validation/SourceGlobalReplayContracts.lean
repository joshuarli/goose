import Goose.Lower.Validation.SourceGlobalRead
import Goose.Lower.Validation.SummaryPreservationSourceScopeBounds
import Goose.Lower.Validation.SummaryPreservationSourceControlKernelsBounds

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

def GlobalBoundReplayAt (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (func : Func) (returnTypes : List Ty) (slots : Array (List RootRef)) (target : Core.Eff) (scopeCount : Nat)
    (bound : Bound) (initial : LS) (upper : Prov) : Prop :=
  ∀ start finish before after,
    Core.tyBound typingEnv bound start = .ok ((), finish) →
    rpBound env bound before = .ok ((), after) →
    EffectRefinement func after.eff target →
    ReplayBuilder (lower env.mod) results vt func target
      (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
      slots initial upper →
    GeneratedBuilderState initial → NativeRows vt (lowerBound bound
      (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    ∃ next, ReplayBuilder (lower env.mod) results vt func target
        (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
        slots
        (lowerBound bound (lowerEnv env.mod env.impl.vars returnTypes) initial).2 next ∧
      ((lowerBound bound (lowerEnv env.mod env.impl.vars returnTypes) initial).2.cur.isSome = true →
        ∀ value ∈ (lowerBound bound (lowerEnv env.mod env.impl.vars returnTypes) initial).1.uses,
          value < (lowerBound bound (lowerEnv env.mod env.impl.vars returnTypes) initial).2.vals.size) ∧
      ∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old

def GlobalBlockReplayAt (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (func : Func) (returnTypes : List Ty) (slots : Array (List RootRef)) (target : Core.Eff) (scopeCount : Nat)
    (loop : Option LoopCtx) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool)
    (body : Core.Block) (initial : LS) (upper : Prov) : Prop :=
  ∀ type start finish before after sourceRoots range,
    Core.tyBlock typingEnv [] body start = .ok (type, finish) →
    rpBlockValue env [] body before = .ok ((sourceRoots, range), after) →
    EffectRefinement func after.eff target →
    SourceScopesWithin scopeCount (Core.blockScopes none body) →
    (∀ binding ∈ bindings, binding.1 < env.impl.vars.size ∧ binding.2.2 < env.mod.origins.size) →
    (initial.cur.isSome = true → ∀ binding ∈ bindings, binding.2.1 < initial.vals.size) →
    (∀ binding ∈ bindings, ∀ root ∈ rootsAt upper.vals binding.2.1,
      root ∈ rootsAt slots binding.1) →
    (typingEnv.inExpr = false → ∀ entered ∈ initial.stack, entered < scopeCount) →
    ReplayBuilder (lower env.mod) results vt func target
      (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
      slots initial upper →
    GeneratedBuilderState initial → LoopBuilderTargets loop initial →
    LoopReplayBounds loop scopeCount initial →
    NativeRows vt (lowerBlock loop bindings want body
      (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    ∃ next, ReplayBuilder (lower env.mod) results vt func target
        (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
        slots
        (lowerBlock loop bindings want body (lowerEnv env.mod env.impl.vars returnTypes) initial).2 next ∧
      (want = true →
        (lowerBlock loop bindings want body (lowerEnv env.mod env.impl.vars returnTypes) initial).2.cur.isSome = true →
        ReplayValue func next
          (lowerBlock loop bindings want body (lowerEnv env.mod env.impl.vars returnTypes) initial).2
          (lowerBlock loop bindings want body (lowerEnv env.mod env.impl.vars returnTypes) initial).1 sourceRoots (.data type)) ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old)

end Goose.Lower.Validation.SummaryPreservation
