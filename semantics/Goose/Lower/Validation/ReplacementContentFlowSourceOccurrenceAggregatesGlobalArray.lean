import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceGlobalContracts
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceAggregatesConsumed
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceListsGlobal
import Goose.Lower.Validation.SummaryPreservationReplayAggregates

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)} {target : Core.Eff} {scopeCount : Nat} {siteRoot : DemandNode}
  {siteTargets : List BlockId} {initial : LS} {upper : Prov}

theorem globalExpressionOccurrence_arrayLiteral {type : Ty} {elements : List Expr}
    (tables : SourceRootTables typingEnv env)
    (children : ∀ expression ∈ elements, ∀ state provenance,
      GlobalExpressionOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets expression state provenance) :
    GlobalExpressionOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets (.arrLit type elements) initial upper := by
  intro rooted resultType start finish before after roots typed replay ceiling ready sites targetBounds generated native metadata continuation
  obtain ⟨sameType, elementType, childStart, childFinish, elementShape, _, childrenTyped⟩ := tyExpr_arrayLiteral_children typed
  subst resultType
  obtain ⟨ignored, middleSource, elementsReplay, tailReplay⟩ :=
    (st_bind_ok _ _ _ _).mp replay
  cases ignored
  have afterEq : after = middleSource := congrArg Prod.snd ((st_pure_ok _ _ _).mp tailReplay)
  subst after
  let le := lowerEnv env.mod env.impl.vars returnTypes
  let lowered := lowerExprs elements le initial
  have childNative := native.of_prefix (types_emitDef (.arrLit type lowered.1) le lowered.2 _ _ rfl)
  have childMetadata := metadata.of_advance (advB_emitDef (.arrLit type lowered.1) le lowered.2 _ _ rfl)
  have childContinuation := continuation.of_advance (advB_emitDef (.arrLit type lowered.1) le lowered.2 _ _ rfl)
  have paths : ∀ expression ∈ elements, ∃ path,
      DemandNodeAt (.expression (.arrLit type elements)) path (.expression expression) := by
    intro expression member
    obtain ⟨index, row⟩ := List.mem_iff_getElem?.mp member
    exact ⟨[index], .child (by simp [DemandNode.child?, DemandNode.children, List.getElem?_map, row]) (.here _)⟩
  obtain ⟨middle, listReady, listValues, listRoots, listLedger, listSites⟩ :=
    typedGlobalExpressionsAsOccurrence (anchor := .expression (.arrLit type elements)) elements children initial upper rooted paths
      elementType childStart childFinish before middleSource childrenTyped elementsReplay ceiling ready sites targetBounds generated childNative childMetadata childContinuation
  obtain ⟨next, completed, value, retained⟩ := listReady.arrayLiteral elementsReplay replay
    (rfl : lowerExprs elements le initial = lowered) (fun live value member => (listValues live value member).1)
  refine ⟨next, completed, value, ?_, ?_⟩
  · intro index bound
    have growth : upper.vals.size ≤ middle.vals.size := by
      rw [ready.roots.valueSize, listReady.roots.valueSize]
      exact (advB_lowerExprs elements le initial lowered.1 lowered.2 rfl).vals
    exact (retained index (Nat.lt_of_lt_of_le bound growth)).trans (listRoots index bound)
  · apply listLedger.emitDef_sites listSites listReady completed rfl retained
    · intro live candidate member
      simp only [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses] at member
      exact (listValues live candidate member).2
    · intro address same; cases same
    · intro callee arguments org same; cases same
    · intro live candidate member mutability payload reference
      simp only [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses] at member
      have typedValues := lowerExprs_generated_typed (results := returnTypes) (values := lowered.1) (after := lowered.2) elements (tyExprsAs_structExprs childrenTyped)
        (by
          change lowerExprs elements (lowerEnv typingEnv.mod typingEnv.vars returnTypes) initial = lowered
          rw [← tables.moduleEq, ← tables.variablesEq]) live generated
      exact False.elim (typedValues_no_reference typedValues childNative (fun type member => (List.eq_of_mem_replicate member) ▸ sourceArrayElement_flat typed elementShape) candidate member mutability payload reference)

#print axioms globalExpressionOccurrence_arrayLiteral

end Goose.Lower.Validation.ReplacementContentFlowSource
