import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceListsGlobalContracts

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR SummaryPreservation

def GlobalPrintArgumentsOccurrenceReplayAt (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (func : Func) (returnTypes : List Ty)
    (slots : Array (List RootRef)) (target : Core.Eff) (scopeCount : Nat)
    (siteRoot : DemandNode) (siteTargets : List BlockId) (anchor : DemandNode)
    (arguments : List PrintArg) (initial : LS) (upper : Prov) : Prop :=
  (∃ path, DemandNodeAt siteRoot path anchor) →
  (∀ expression, .expr expression ∈ arguments → ∃ path, DemandNodeAt anchor path (.expression expression)) →
  ∀ start finish before after,
    tyPrintArgs typingEnv arguments start = .ok ((), finish) →
    rpPrintArgs env arguments before = .ok ((), after) →
    EffectRefinement func after.eff target →
    ReplayBuilder (lower env.mod) results vt func target
      (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
      slots initial upper →
    OccurrenceSitesBuilder env siteRoot siteTargets
      (lowerEnv env.mod env.impl.vars returnTypes) initial
      func vt upper →
    ReplacementTargetsBound siteTargets initial → GeneratedBuilderState initial →
    NativeRows vt (lowerPrintArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot func
      (lowerPrintArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    NativeBuilderContinuation func (lowerPrintArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    ∃ next, ReplayBuilder (lower env.mod) results vt func target
        (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
        slots
        (lowerPrintArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).2 next ∧
      ((lowerPrintArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).2.cur.isSome = true →
        ∀ value ∈ (lowerPrintArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).1.flatMap PrintPart.uses,
          value < (lowerPrintArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).2.vals.size ∧
          OperandOccurrence env anchor func next value) ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      OccurrenceLedger env anchor func vt next initial
        (lowerPrintArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).2 ∧
      OccurrenceSitesBuilder env siteRoot siteTargets
        (lowerEnv env.mod env.impl.vars returnTypes)
        (lowerPrintArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).2
        func vt next

end Goose.Lower.Validation.ReplacementContentFlowSource
