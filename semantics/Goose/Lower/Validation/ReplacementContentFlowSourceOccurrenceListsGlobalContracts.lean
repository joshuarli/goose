import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceGlobalContracts
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlRecipeFrames

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR SummaryPreservation

def GlobalExpressionsOccurrenceReplayAt (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (func : Func) (returnTypes : List Ty)
    (slots : Array (List RootRef)) (target : Core.Eff) (scopeCount : Nat)
    (siteRoot : DemandNode) (siteTargets : List BlockId) (anchor : DemandNode)
    (expressions : List Expr) (initial : LS) (upper : Prov) : Prop :=
  (∃ path, DemandNodeAt siteRoot path anchor) →
  (∀ expression ∈ expressions, ∃ path, DemandNodeAt anchor path (.expression expression)) →
  ∀ types start finish before after,
    tyStructExprs typingEnv types expressions start = .ok ((), finish) →
    rpExprs env expressions before = .ok ((), after) →
    EffectRefinement func after.eff target →
    ReplayBuilder (lower env.mod) results vt func target
      (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
      slots initial upper →
    OccurrenceSitesBuilder env siteRoot siteTargets
      (lowerEnv env.mod env.impl.vars returnTypes) initial
      func vt upper →
    ReplacementTargetsBound siteTargets initial →
    GeneratedBuilderState initial →
    NativeRows vt (lowerExprs expressions (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot func
      (lowerExprs expressions (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    NativeBuilderContinuation func (lowerExprs expressions (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    ∃ next, ReplayBuilder (lower env.mod) results vt func target
        (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
        slots
        (lowerExprs expressions (lowerEnv env.mod env.impl.vars returnTypes) initial).2 next ∧
      ((lowerExprs expressions (lowerEnv env.mod env.impl.vars returnTypes) initial).2.cur.isSome = true →
        ∀ value ∈ (lowerExprs expressions (lowerEnv env.mod env.impl.vars returnTypes) initial).1,
          value < (lowerExprs expressions (lowerEnv env.mod env.impl.vars returnTypes) initial).2.vals.size ∧
          OperandOccurrence env anchor func next value) ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      OccurrenceLedger env anchor func vt next initial
        (lowerExprs expressions (lowerEnv env.mod env.impl.vars returnTypes) initial).2 ∧
      OccurrenceSitesBuilder env siteRoot siteTargets
        (lowerEnv env.mod env.impl.vars returnTypes)
        (lowerExprs expressions (lowerEnv env.mod env.impl.vars returnTypes) initial).2
        func vt next

end Goose.Lower.Validation.ReplacementContentFlowSource
