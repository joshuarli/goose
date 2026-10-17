import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceArgumentsNodes
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceListsGlobalContracts
import Goose.Lower.Validation.SummaryPreservationReplayArgumentSource
import Goose.Lower.Validation.SummaryPreservationArgumentReplay

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR SummaryPreservation

def GlobalArgumentOccurrenceReplayAt (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (func : Func) (returnTypes : List Ty)
    (slots : Array (List RootRef)) (target : Core.Eff) (scopeCount : Nat)
    (siteRoot : DemandNode) (siteTargets : List BlockId) (anchor : DemandNode)
    (argument : Arg) (initial : LS) (upper : Prov) : Prop :=
  (∃ path, DemandNodeAt siteRoot path anchor) →
  (∃ path, DemandNodeAt anchor path (argumentDemandNode argument)) →
  ∀ start finish before after sourceRoots,
    ArgumentTyping typingEnv argument start finish →
    ArgumentReplay env argument before sourceRoots after →
    EffectRefinement func after.eff target →
    ReplayBuilder (lower env.mod) results vt func target
      (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
      slots initial upper →
    OccurrenceSitesBuilder env siteRoot siteTargets
      (lowerEnv env.mod env.impl.vars returnTypes) initial
      func vt upper →
    ReplacementTargetsBound siteTargets initial → GeneratedBuilderState initial →
    NativeRows vt (lowerArg argument (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot func
      (lowerArg argument (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    NativeBuilderContinuation func (lowerArg argument (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    ∃ next, ReplayBuilder (lower env.mod) results vt func target
        (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
        slots
        (lowerArg argument (lowerEnv env.mod env.impl.vars returnTypes) initial).2 next ∧
      ((lowerArg argument (lowerEnv env.mod env.impl.vars returnTypes) initial).2.cur.isSome = true →
        (lowerArg argument (lowerEnv env.mod env.impl.vars returnTypes) initial).1 <
          (lowerArg argument (lowerEnv env.mod env.impl.vars returnTypes) initial).2.vals.size ∧
        GIR.RootsRefine func
          (rootsAt next.vals (lowerArg argument (lowerEnv env.mod env.impl.vars returnTypes) initial).1) sourceRoots ∧
        OperandOccurrence env anchor func next
          (lowerArg argument (lowerEnv env.mod env.impl.vars returnTypes) initial).1) ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      OccurrenceLedger env anchor func vt next initial
        (lowerArg argument (lowerEnv env.mod env.impl.vars returnTypes) initial).2 ∧
      OccurrenceSitesBuilder env siteRoot siteTargets
        (lowerEnv env.mod env.impl.vars returnTypes)
        (lowerArg argument (lowerEnv env.mod env.impl.vars returnTypes) initial).2
        func vt next

def GlobalArgumentsOccurrenceReplayAt (typingEnv : TEnv) (env : PEnv) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (func : Func) (returnTypes : List Ty)
    (slots : Array (List RootRef)) (target : Core.Eff) (scopeCount : Nat)
    (siteRoot : DemandNode) (siteTargets : List BlockId) (anchor : DemandNode)
    (arguments : List Arg) (initial : LS) (upper : Prov) : Prop :=
  (∃ path, DemandNodeAt siteRoot path anchor) →
  (∀ argument ∈ arguments, ∃ path, DemandNodeAt anchor path (argumentDemandNode argument)) →
  ∀ callee parameters start finish before after sourceRoots,
    tyArgs typingEnv callee parameters arguments start = .ok ((), finish) →
    parameters.length = arguments.length →
    rpArgs env arguments before = .ok (sourceRoots, after) →
    EffectRefinement func after.eff target →
    ReplayBuilder (lower env.mod) results vt func target
      (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
      slots initial upper →
    OccurrenceSitesBuilder env siteRoot siteTargets
      (lowerEnv env.mod env.impl.vars returnTypes) initial
      func vt upper →
    ReplacementTargetsBound siteTargets initial → GeneratedBuilderState initial →
    NativeRows vt (lowerArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot func
      (lowerArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    NativeBuilderContinuation func (lowerArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).2 →
    ∃ next, ReplayBuilder (lower env.mod) results vt func target
        (lowerEnv env.mod env.impl.vars returnTypes) scopeCount
        slots
        (lowerArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).2 next ∧
      ((lowerArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).2.cur.isSome = true →
        (lowerArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).1.length = arguments.length ∧
        ∀ (index : Nat) (value : ValueId),
          (lowerArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).1[index]? = some value →
          value < (lowerArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).2.vals.size ∧
          (∃ roots, sourceRoots[index]? = some roots ∧
            GIR.RootsRefine func (rootsAt next.vals value) roots) ∧
          OperandOccurrence env anchor func next value) ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      OccurrenceLedger env anchor func vt next initial
        (lowerArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).2 ∧
      OccurrenceSitesBuilder env siteRoot siteTargets
        (lowerEnv env.mod env.impl.vars returnTypes)
        (lowerArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).2
        func vt next

end Goose.Lower.Validation.ReplacementContentFlowSource
