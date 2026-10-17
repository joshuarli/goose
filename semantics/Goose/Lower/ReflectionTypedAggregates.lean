import Goose.Lower.ReflectionSources

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

def TypedExprChildrenReflection (fuel : Nat) (cfg : Cfg) (results : List Ty)
    (expressions : List Expr) : Prop :=
  ∀ residual, residual ≤ fuel → ∀ expression, expression ∈ expressions →
    TypedExprReflection residual cfg results expression

def TypedExprsReflection (fuel : Nat) (cfg : Cfg) (results : List Ty)
    (expressions : List Expr) : Prop :=
  ∀ (env : Env) (state : St) (sources : ∀ n, ExprsSource n cfg env expressions state),
    (∀ n, (sources n).resultsMatch results) →
    ∀ (ls after : LS) (ids : List ValueId) (pt : Pt) (cx : FnCtx) (fr : Frame),
    lowerExprs expressions (lowerEnv cfg.mod env.vars results) ls = (ids, after) →
    ls.pp = some pt → ExtT after cx.fn.blocks → Rel cfg env cx fr ls →
    cx.cfg.mod = lower cfg.mod → cx.fn.results = results → GeneratedBuilderState ls →
    ReflectAtFuel fuel cx pt fr (fun n => mapList (evalExpr n cfg env) expressions)
      (fun values _ pt' fr' => ids.length = values.length ∧
        Post cfg env cx ls fr after fr' pt' (cellsOf ids values)) state

theorem typedExprsReflection_of_children {fuel : Nat} {cfg : Cfg} {results : List Ty} :
    ∀ (expressions : List Expr), TypedExprChildrenReflection fuel cfg results expressions →
      TypedExprsReflection fuel cfg results expressions := by
  intro expressions
  induction expressions generalizing fuel with
  | nil =>
    intro children env state sources sourceMetadata ls after ids pt cx fr lowering point extension rel
      moduleEq resultsEq generated
    simp only [lowerExprs, pure_run] at lowering
    obtain ⟨idsEq, afterEq⟩ := Prod.mk.inj lowering
    subst ids
    subst after
    change ReflectAtFuel fuel cx pt fr (fun _ => pure ([] : List Val))
      (fun (values : List Val) _ pt' fr' => ([] : List Val).length = values.length ∧
        Post cfg env cx ls fr ls fr' pt' (cellsOf [] values)) state
    exact ReflectAtFuel.ret fuel (value := ([] : List Val)) ⟨rfl, Post.init rel point⟩
  | cons expression rest induction =>
    intro children env state sources sourceMetadata ls after ids pt cx fr lowering point extension rel
      moduleEq resultsEq generated
    simp only [lowerExprs, bind_eq] at lowering
    obtain ⟨id, middle, headRun, tailIds, after, tailRun, finish⟩ := lowering
    rw [pure_run] at finish
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj finish
    have middleExtension : ExtT middle cx.fn.blocks :=
      extension.of_adv (advB_lowerExprs rest _ _ _ _ tailRun)
    let sourceAt := sources fuel
    have sourceAtMetadata : sourceAt.resultsMatch results := by
      simpa only [sourceAt] using sourceMetadata fuel
    have head := children fuel (Nat.le_refl _) expression (by simp) env state
      sourceAt.head (sourceAt.head_resultsMatch sourceAtMetadata)
      ls middle id pt cx fr headRun point middleExtension rel moduleEq resultsEq generated
    let tailSource : Val → Nat → M (List Val) := fun value n => do
      let values ← mapList (evalExpr n cfg env) rest
      pure (value :: values)
    have tailSourceMonotone : ∀ value, FuelMonotone (tailSource value) := by
      intro value n k bound
      exact MonoM.bind (MonoM.mapList (fun expression => (monoAll n k bound).expr cfg env expression) rest)
        (fun values => MonoM.refl _)
    have composition : ReflectAtFuel fuel cx pt fr
        (fun n => mapList (evalExpr n cfg env) (expression :: rest))
        (fun values _ pt' fr' => (id :: tailIds).length = values.length ∧
          Post cfg env cx ls fr after fr' pt' (cellsOf (id :: tailIds) values)) state := by
      refine head.bind ?_
        (fun n k bound => (monoAll n k bound).expr cfg env expression) tailSourceMonotone
      intro n value next pt' fr' headDone headPost residual residualBound
      let tailSources : ∀ k, ExprsSource k cfg env rest next := fun k =>
        ExprsSource.afterHead sources headDone k
      have tailMetadata : ∀ k, (tailSources k).resultsMatch results := fun k =>
        ExprsSource.afterHead_resultsMatch sources sourceMetadata headDone k
      have tailChildren : TypedExprChildrenReflection residual cfg results rest := by
        intro remaining remainingBound child member
        exact children remaining (Nat.le_trans remainingBound residualBound) child (by simp [member])
      have tailReflection := induction tailChildren env next tailSources tailMetadata
        middle after tailIds pt' cx fr' tailRun headPost.pp extension headPost.rel moduleEq resultsEq
        (generated.lowerExpr expression headRun)
      have sourceWithHead : ReflectAtFuel residual cx pt' fr'
          (tailSource value)
          (fun values _ pt'' fr'' => (id :: tailIds).length = values.length ∧
            Post cfg env cx ls fr after fr'' pt'' (cellsOf (id :: tailIds) values)) next := by
        refine tailReflection.bind ?_
          (fun n k bound => MonoM.mapList (fun child => (monoAll n k bound).expr cfg env child) rest)
          (fun values n k bound => MonoM.refl _)
        intro k values final pt'' fr'' tailDone tailPost remaining remainingBound
        obtain ⟨tailLength, tailPost⟩ := tailPost
        exact ReflectAtFuel.ret remaining ⟨by simp [tailLength], by
          simpa [cellsOf] using headPost.comp tailPost⟩
      exact sourceWithHead
    exact composition.of_source (fun n => ⟨n, by simp only [mapList]⟩)

theorem typedExprReflection_arrLit {fuel : Nat} {cfg : Cfg} {results : List Ty}
    {target : Ty} {expressions : List Expr}
    (children : TypedExprChildrenReflection fuel cfg results expressions) :
    TypedExprReflection fuel cfg results (.arrLit target expressions) := by
  intro env state source metadata ls after resultId pt cx fr lowering point extension rel moduleEq
    resultsEq generated
  let childrenSources : ∀ n, ExprsSource n cfg env expressions state := fun n =>
    Classical.choose (source.arrLitChildren n results metadata)
  have childrenMetadata : ∀ n, (childrenSources n).resultsMatch results := fun n =>
    Classical.choose_spec (source.arrLitChildren n results metadata)
  simp only [lowerExpr, bind_eq] at lowering
  obtain ⟨ids, middle, childrenRun, definition⟩ := lowering
  have middleExtension : ExtT middle cx.fn.blocks := extension.of_adv (adv_emitDef definition)
  have reflectedChildren := typedExprsReflection_of_children expressions children env state childrenSources
    childrenMetadata ls middle ids pt cx fr childrenRun point middleExtension rel moduleEq resultsEq generated
  have composed : ReflectAtFuel fuel cx pt fr
      (fun n => mapList (evalExpr n cfg env) expressions >>= fun values => expectArrayLit target values.toArray)
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(resultId,.val value)]) state := by
    refine reflectedChildren.bind ?_
      (fun n k bound => MonoM.mapList (fun expression => (monoAll n k bound).expr cfg env expression)
        expressions)
      (fun values n k bound => MonoM.refl _)
    intro n values final pt' fr' childrenDone childrenPost residual residualBound
    obtain ⟨lengthMatch, post⟩ := childrenPost
    have valuesRead := mapList_getVal_cells lengthMatch post.has
    exact leaf_def_reflectAtFuel post definition extension (by intro f args org h; cases h)
      RVal.val (sourceFuel := 0) (by
        simp only [execPure, valuesRead, pure_bind])
  exact composed.of_source (fun n => ⟨n + 1, by simp only [evalExpr]⟩)

theorem typedExprReflection_structLit {fuel : Nat} {cfg : Cfg} {results : List Ty}
    {target : Ty} {expressions : List Expr}
    (children : TypedExprChildrenReflection fuel cfg results expressions) :
    TypedExprReflection fuel cfg results (.structLit target expressions) := by
  intro env state source metadata ls after resultId pt cx fr lowering point extension rel moduleEq
    resultsEq generated
  have typing := source.typed
  simp only [tyExpr] at typing
  inv at typing
  obtain ⟨definitionSource, _, definitionTyping, _⟩ := typing
  obtain ⟨sid, fields, rfl, _⟩ := Core.Sound.structDef_ok _ _ _ _ _ definitionTyping
  let childrenSources : ∀ n, ExprsSource n cfg env expressions state := fun n =>
    Classical.choose (source.structLitChildren n results metadata)
  have childrenMetadata : ∀ n, (childrenSources n).resultsMatch results := fun n =>
    Classical.choose_spec (source.structLitChildren n results metadata)
  simp only [lowerExpr, bind_eq] at lowering
  obtain ⟨ids, middle, childrenRun, definition⟩ := lowering
  have middleExtension : ExtT middle cx.fn.blocks := extension.of_adv (adv_emitDef definition)
  have reflectedChildren := typedExprsReflection_of_children expressions children env state childrenSources
    childrenMetadata ls middle ids pt cx fr childrenRun point middleExtension rel moduleEq resultsEq generated
  have composed : ReflectAtFuel fuel cx pt fr
      (fun n => mapList (evalExpr n cfg env) expressions >>= fun values =>
        pure (.record sid values.toArray))
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(resultId,.val value)]) state := by
    refine reflectedChildren.bind ?_
      (fun n k bound => MonoM.mapList (fun expression => (monoAll n k bound).expr cfg env expression)
        expressions)
      (fun values n k bound => MonoM.refl _)
    intro n values final pt' fr' childrenDone childrenPost residual residualBound
    obtain ⟨lengthMatch, post⟩ := childrenPost
    have valuesRead := mapList_getVal_cells lengthMatch post.has
    exact leaf_def_reflectAtFuel post definition extension (by intro f args org h; cases h)
      RVal.val (sourceFuel := 0) (by simp only [execPure, valuesRead, pure_bind])
  exact composed.of_source (fun n => ⟨n + 1, by simp only [evalExpr]⟩)

end Goose.Lower
