import Goose.Lower.Validation.SourceGlobalReplayContracts
import Goose.Lower.Validation.SummaryPreservationReplayNativeExpressions
import Goose.Lower.Validation.SummaryPreservationReplayAggregates

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)} {target : Core.Eff} {scopeCount : Nat} {initial : LS} {upper : Prov}

theorem globalExpressionReplay_arrayLiteral {type : Ty} {elements : List Expr}
    (children : ∀ earlier expression later, elements = earlier ++ expression :: later →
      ∀ provenance, GlobalExpressionReplayAt typingEnv env results vt func returnTypes slots target scopeCount expression
        (lowerExprs earlier (lowerEnv env.mod env.impl.vars returnTypes) initial).2 provenance) :
    GlobalExpressionReplayAt typingEnv env results vt func returnTypes slots target scopeCount (.arrLit type elements) initial upper := by
  intro resultType start finish before after roots typed replay ceiling ready generated native
  obtain ⟨sameType, elementType, childStart, childFinish, _, _, childrenTyped⟩ := tyExpr_arrayLiteral_children typed
  subst resultType
  obtain ⟨ignored, middleSource, elementsReplay, tailReplay⟩ :=
    (st_bind_ok _ _ _ _).mp replay
  cases ignored
  have afterEq : after = middleSource := congrArg Prod.snd ((st_pure_ok _ _ _).mp tailReplay)
  subst after
  let le := lowerEnv env.mod env.impl.vars returnTypes
  let lowered := lowerExprs elements le initial
  have childNative := native.of_prefix (types_emitDef (.arrLit type lowered.1) le lowered.2 _ _ rfl)
  obtain ⟨middle, listReady, listValues, listRoots⟩ :=
    ReplayBuilder.typedExpressionsAsNative elements elementType ready childrenTyped
      (fun earlier expression later member childType tn1 tn2 sourceBefore sourceAfter childRoots provenance
        childTyped childReplay childEffect childReady childGenerated childNative =>
        children earlier expression later member provenance childType tn1 tn2 sourceBefore sourceAfter childRoots
          childTyped childReplay childEffect childReady childGenerated childNative)
      elementsReplay ceiling generated childNative
  obtain ⟨next, completed, value, retained⟩ := listReady.arrayLiteral elementsReplay replay
    (rfl : lowerExprs elements le initial = lowered) listValues
  refine ⟨next, completed, value, ?_⟩
  intro index bound
  have growth : upper.vals.size ≤ middle.vals.size := by
    rw [ready.roots.valueSize, listReady.roots.valueSize]
    exact (advB_lowerExprs elements le initial lowered.1 lowered.2 rfl).vals
  exact (retained index (Nat.lt_of_lt_of_le bound growth)).trans (listRoots index bound)

theorem globalExpressionReplay_structLiteral {type : Ty} {elements : List Expr}
    (children : ∀ earlier expression later, elements = earlier ++ expression :: later →
      ∀ provenance, GlobalExpressionReplayAt typingEnv env results vt func returnTypes slots target scopeCount expression
        (lowerExprs earlier (lowerEnv env.mod env.impl.vars returnTypes) initial).2 provenance) :
    GlobalExpressionReplayAt typingEnv env results vt func returnTypes slots target scopeCount (.structLit type elements) initial upper := by
  intro resultType start finish before after roots typed replay ceiling ready generated native
  obtain ⟨sameType, descriptor, definitionFinish, childStart, childFinish, _, childrenTyped⟩ :=
    tyExpr_structLiteral_children typed
  subst resultType
  obtain ⟨ignored, middleSource, elementsReplay, tailReplay⟩ :=
    (st_bind_ok _ _ _ _).mp replay
  cases ignored
  have afterEq : after = middleSource := congrArg Prod.snd ((st_pure_ok _ _ _).mp tailReplay)
  subst after
  let le := lowerEnv env.mod env.impl.vars returnTypes
  let lowered := lowerExprs elements le initial
  have childNative := native.of_prefix (types_emitDef (.structLit type lowered.1) le lowered.2 _ _ rfl)
  obtain ⟨middle, listReady, listValues, listRoots⟩ :=
    ReplayBuilder.typedExpressionsNative elements (descriptor.fields.toList.map (·.ty)) ready childrenTyped
      (fun earlier expression later member childType tn1 tn2 sourceBefore sourceAfter childRoots provenance
        childTyped childReplay childEffect childReady childGenerated childNative =>
        children earlier expression later member provenance childType tn1 tn2 sourceBefore sourceAfter childRoots
          childTyped childReplay childEffect childReady childGenerated childNative)
      elementsReplay ceiling generated childNative
  obtain ⟨next, completed, value, retained⟩ := listReady.structLiteral elementsReplay replay
    (rfl : lowerExprs elements le initial = lowered) listValues
  refine ⟨next, completed, value, ?_⟩
  intro index bound
  have growth : upper.vals.size ≤ middle.vals.size := by
    rw [ready.roots.valueSize, listReady.roots.valueSize]
    exact (advB_lowerExprs elements le initial lowered.1 lowered.2 rfl).vals
  exact (retained index (Nat.lt_of_lt_of_le bound growth)).trans (listRoots index bound)

theorem globalExpressionReplay_arrayFill {type : Ty} {element : Expr}
    (child : GlobalExpressionReplayAt typingEnv env results vt func returnTypes slots target scopeCount element initial upper) :
    GlobalExpressionReplayAt typingEnv env results vt func returnTypes slots target scopeCount (.fill type element) initial upper := by
  intro resultType start finish before after roots typed replay ceiling ready generated native
  obtain ⟨sameType, elementType, count, childStart, childFinish, shape, childTyped⟩ := tyExpr_fill_child typed
  subst resultType
  obtain ⟨childRoots, middleSource, elementReplay, tailReplay⟩ :=
    (st_bind_ok _ _ _ _).mp replay
  have afterEq : after = middleSource := congrArg Prod.snd ((st_pure_ok _ _ _).mp tailReplay)
  subst after
  let le := lowerEnv env.mod env.impl.vars returnTypes
  let lowered := lowerExpr element le initial
  have childNative := native.of_prefix (types_emitDef (.arrFill type lowered.1) le lowered.2 _ _ rfl)
  obtain ⟨middle, childReady, childValue, childRoots⟩ := child elementType childStart childFinish
    before middleSource childRoots childTyped elementReplay ceiling ready generated childNative
  obtain ⟨next, completed, value, retained⟩ := childReady.arrayFill elementReplay replay
    (rfl : lowerExpr element le initial = lowered) (fun live => (childValue live).bound)
  refine ⟨next, completed, value, ?_⟩
  intro index bound
  have growth : upper.vals.size ≤ middle.vals.size := by
    rw [ready.roots.valueSize, childReady.roots.valueSize]
    exact (advB_lowerExpr element le initial lowered.1 lowered.2 rfl).vals
  exact (retained index (Nat.lt_of_lt_of_le bound growth)).trans (childRoots index bound)

#print axioms globalExpressionReplay_arrayLiteral
#print axioms globalExpressionReplay_structLiteral
#print axioms globalExpressionReplay_arrayFill

end Goose.Lower.Validation.SummaryPreservation
