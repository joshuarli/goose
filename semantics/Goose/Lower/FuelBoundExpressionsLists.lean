import Goose.Lower.FuelBoundTyped
import Goose.Lower.ReflectionTypedAggregates
import Goose.Lower.ReflectionReferences

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

def TypedExprChildrenFuelBound (sourceFuel fuel : Nat) (cfg : Cfg) (results : List Ty)
    (expressions : List Expr) : Prop :=
  ∀ residual, residual ≤ fuel → ∀ expression, expression ∈ expressions →
    TypedExprFuelBound sourceFuel residual cfg results expression

theorem typedExprsFuelBound_of_children {sourceFuel fuel : Nat} {cfg : Cfg} {results : List Ty} :
    ∀ (expressions : List Expr), TypedExprChildrenFuelBound sourceFuel fuel cfg results expressions →
      TypedExprsFuelBound sourceFuel fuel cfg results expressions := by
  intro expressions
  induction expressions generalizing fuel with
  | nil =>
    intro children env state sources sourceMetadata ls after ids pt cx fr lowering point extension rel
      moduleEq resultsEq generated
    simp only [lowerExprs, pure_run] at lowering
    obtain ⟨idsEq, afterEq⟩ := Prod.mk.inj lowering
    subst ids
    subst after
    change FuelBoundAt sourceFuel fuel cx pt fr (fun _ => pure ([] : List Val))
      (fun (values : List Val) _ pt' fr' => ([] : List Val).length = values.length ∧
        Post cfg env cx ls fr ls fr' pt' (cellsOf [] values)) state
    exact FuelBoundAt.ret (sourceFuel := sourceFuel) (targetFuel := fuel) (value := ([] : List Val)) ⟨rfl, Post.init rel point⟩
  | cons expression rest induction =>
    intro children env state sources sourceMetadata ls after ids pt cx fr lowering point extension rel
      moduleEq resultsEq generated
    simp only [lowerExprs, bind_eq] at lowering
    obtain ⟨id, middle, headRun, tailIds, after, tailRun, finish⟩ := lowering
    rw [pure_run] at finish
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj finish
    have middleExtension : ExtT middle cx.fn.blocks :=
      extension.of_adv (advB_lowerExprs rest _ _ _ _ tailRun)
    let sourceAt := sources sourceFuel
    have sourceAtMetadata : sourceAt.resultsMatch results := by
      simpa only [sourceAt] using sourceMetadata sourceFuel
    have head := children fuel (Nat.le_refl _) expression (by simp) env state
      sourceAt.head (sourceAt.head_resultsMatch sourceAtMetadata)
      ls middle id pt cx fr headRun point middleExtension rel moduleEq resultsEq generated
    let tailSource : Val → Nat → M (List Val) := fun value n => do
      let values ← mapList (evalExpr n cfg env) rest
      pure (value :: values)
    have composition : FuelBoundAt sourceFuel fuel cx pt fr
        (fun n => mapList (evalExpr n cfg env) (expression :: rest))
        (fun values _ pt' fr' => (id :: tailIds).length = values.length ∧
          Post cfg env cx ls fr after fr' pt' (cellsOf (id :: tailIds) values)) state := by
      refine head.bind ?_
      intro value next pt' fr' headDone headPost residual residualBound
      let tailSources : ∀ k, ExprsSource k cfg env rest next := fun k =>
        ExprsSource.afterHead sources headDone k
      have tailMetadata : ∀ k, (tailSources k).resultsMatch results := fun k =>
        ExprsSource.afterHead_resultsMatch sources sourceMetadata headDone k
      have tailChildren : TypedExprChildrenFuelBound sourceFuel residual cfg results rest := by
        intro remaining remainingBound child member
        exact children remaining (Nat.le_trans remainingBound residualBound) child (by simp [member])
      have tailReflection := induction tailChildren env next tailSources tailMetadata
        middle after tailIds pt' cx fr' tailRun headPost.pp extension headPost.rel moduleEq resultsEq
        (generated.lowerExpr expression headRun)
      have sourceWithHead : FuelBoundAt sourceFuel residual cx pt' fr'
          (tailSource value)
          (fun values _ pt'' fr'' => (id :: tailIds).length = values.length ∧
            Post cfg env cx ls fr after fr'' pt'' (cellsOf (id :: tailIds) values)) next := by
        refine tailReflection.bind ?_
        intro values final pt'' fr'' tailDone tailPost remaining remainingBound
        obtain ⟨tailLength, tailPost⟩ := tailPost
        exact FuelBoundAt.ret (sourceFuel := sourceFuel) (targetFuel := remaining) ⟨by simp [tailLength], by
          simpa [cellsOf] using headPost.comp tailPost⟩
      exact sourceWithHead
    exact composition.of_source (otherFuel := sourceFuel) (by simp only [mapList])


def TypedArgChildrenFuelBound (sourceFuel fuel : Nat) (cfg : Cfg) (results : List Ty)
    (arguments : List Arg) : Prop :=
  ∀ residual, residual ≤ fuel → ∀ argument, argument ∈ arguments →
    TypedArgFuelBound sourceFuel residual cfg results argument

theorem typedArgsFuelBound_of_children {sourceFuel fuel : Nat} {cfg : Cfg} {results : List Ty} :
    ∀ (arguments : List Arg), TypedArgChildrenFuelBound sourceFuel fuel cfg results arguments →
      TypedArgsFuelBound sourceFuel fuel cfg results arguments := by
  intro arguments
  induction arguments generalizing fuel with
  | nil =>
    intro children env state sources sourceMetadata ls after ids pt cx fr lowering point extension
      rel moduleEq resultsEq generated
    simp only [lowerArgs, pure_run] at lowering
    obtain ⟨idsEq, afterEq⟩ := Prod.mk.inj lowering
    subst ids
    subst after
    change FuelBoundAt sourceFuel fuel cx pt fr (fun _ => pure ([] : List Val))
      (fun (values : List Val) _ pt' fr' =>
        ([] : List ValueId).length = values.length ∧
          Post cfg env cx ls fr ls fr' pt' (cellsOf [] values)) state
    exact FuelBoundAt.ret (sourceFuel := sourceFuel) (targetFuel := fuel) (value := ([] : List Val))
      ⟨rfl, by simpa [cellsOf] using Post.init rel point⟩
  | cons argument rest induction =>
    intro children env state sources sourceMetadata ls after ids pt cx fr lowering point extension
      rel moduleEq resultsEq generated
    simp only [lowerArgs, bind_eq] at lowering
    obtain ⟨id, middle, headRun, tailIds, after, tailRun, finish⟩ := lowering
    rw [pure_run] at finish
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj finish
    have middleExtension : ExtT middle cx.fn.blocks :=
      extension.of_adv (advB_lowerArgs rest _ _ _ _ tailRun)
    cases sourceAt : sources sourceFuel with
    | cons head tail =>
      have sourceAtMetadata : (sources sourceFuel).resultsMatch results := sourceMetadata sourceFuel
      rw [sourceAt] at sourceAtMetadata
      have headMetadata : head.resultsMatch results := by
        simpa only [ArgsSource.resultsMatch] using sourceAtMetadata.1
      have headReflection := children fuel (Nat.le_refl _) argument (by simp) env state head
        headMetadata ls middle id pt cx fr headRun point middleExtension rel moduleEq resultsEq generated
      let tailSource : Val → Nat → M (List Val) := fun value n => do
        let values ← mapList (evalArg n cfg env) rest
        pure (value :: values)
      have composition : FuelBoundAt sourceFuel fuel cx pt fr
          (fun n => mapList (evalArg n cfg env) (argument :: rest))
          (fun values _ pt' fr' => (id :: tailIds).length = values.length ∧
            Post cfg env cx ls fr after fr' pt' (cellsOf (id :: tailIds) values)) state := by
        refine headReflection.bind ?_
        intro value nextState pt' fr' headDone headPost residual residualBound
        let tailSources : ∀ k, ArgsSource k cfg env rest nextState := fun k =>
          ArgsSource.afterHead sources headDone k
        have tailMetadata : ∀ k, (tailSources k).resultsMatch results := fun k =>
          ArgsSource.afterHead_resultsMatch sources sourceMetadata headDone k
        have tailChildren : TypedArgChildrenFuelBound sourceFuel residual cfg results rest := by
          intro remaining remainingBound child member
          exact children remaining (Nat.le_trans remainingBound residualBound) child
            (by simp [member])
        have tailReflection := induction tailChildren env nextState tailSources tailMetadata
          middle after tailIds pt' cx fr' tailRun headPost.pp extension headPost.rel moduleEq
          resultsEq (generated.lowerArg argument headRun)
        have sourceWithHead : FuelBoundAt sourceFuel residual cx pt' fr' (tailSource value)
            (fun values _ pt'' fr'' => (id :: tailIds).length = values.length ∧
              Post cfg env cx ls fr after fr'' pt'' (cellsOf (id :: tailIds) values)) nextState := by
          refine tailReflection.bind ?_
          intro values final pt'' fr'' tailDone ⟨tailLength, tailPost⟩ remaining remainingBound
          exact FuelBoundAt.ret (sourceFuel := sourceFuel) (targetFuel := remaining) ⟨by simp [tailLength], by
            simpa [cellsOf] using headPost.comp tailPost⟩
        exact sourceWithHead
      exact composition.of_source (otherFuel := sourceFuel) (by simp only [mapList])


end Goose.Lower
