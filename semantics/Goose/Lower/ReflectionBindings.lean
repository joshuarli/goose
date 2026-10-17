import Goose.Lower.ReflectionControl
import Goose.Lower.DestinationSim
import Goose.Lower.ReflectionEffects
import Goose.Lower.ReflectionTransfersCoercion

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

private theorem leaf_def_keep_reflectAtFuel {cfg : Cfg} {env : Env} {cx : FnCtx}
    {ls lsk ls1 : LS} {fr frk : Frame} {ptk : Pt} {cellsk : List (ValueId × RVal)}
    {fuel sourceFuel : Nat} {state : St}
    (before : Post cfg env cx ls fr lsk frk ptk cellsk) {op : Op} {le : LEnv}
    {id : ValueId} (lowering : emitDef op le lsk = (id, ls1))
    (extension : ExtT ls1 cx.fn.blocks) (noCall : ∀ fn args origin, op ≠ .call fn args origin)
    {α : Type} {source : Nat → M α} (inject : α → RVal)
    (operation : execPure cx frk op = source sourceFuel >>= fun value => pure (inject value)) :
    ReflectAtFuel fuel cx ptk frk source
      (fun value _ pt' fr' => Post cfg env cx ls fr ls1 fr' pt' ((id, inject value) :: cellsk)) state := by
  have instruction := (Post.def_leaf_keep before lowering extension (.val .unit)).2
  cases fuel with
  | zero => exact ReflectAtFuel.zero cx ptk frk source _ state
  | succ fuel =>
    have operationFuel : ReflectMFuel fuel
        (fun n => source n >>= fun value => pure (inject value))
        (fun n => execOp n cx frk op) state := by
      apply ReflectMFuel.of_eq
      have pureOp : ∀ n, execOp n cx frk op = execPure cx frk op := by
        intro n
        cases op with
        | call fn args origin => exact (noCall fn args origin rfl).elim
        | _ => simp [execOp]
      rw [pureOp fuel, operation]
    refine (ReflectAtFuel.def_step inject instruction operationFuel).mono ?_
    intro value after pt' fr' matched
    rcases matched with ⟨rfl, rfl⟩
    exact (Post.def_leaf_keep before lowering extension (inject value)).1

theorem typedStatementReflection_letS {fuel : Nat} {cfg : Cfg}
    {results : List Ty} {loop : Option LoopCtx} {slot : VarId} {expr : Expr} {org : OriginId}
    (child : TypedExprReflection fuel cfg results expr) :
    TypedStatementReflection fuel cfg results loop (.letS slot expr org) := by
  intro env state source metadata loops ls after point cx fr lowering entry extension rel module resultsEq
    depth targets counter generated frames
  obtain ⟨exprSource, declaration, variableAt, typingEq, rootsEq, passable⟩ := source.letChild
  have exprMetadata : SourceResults exprSource.typingEnv exprSource.rootsEnv results := by
    rw [typingEq, rootsEq]
    exact metadata
  have slotAt : (lowerEnv cfg.mod env.vars results).slots[slot]? =
      some (⟨declaration.ty, declaration.kind, declaration.scope, slot⟩ : Slot) := by
    simp [lowerEnv, Array.getElem?_mapIdx, variableAt]
  have lowerRun := lowering
  simp only [lowerStmt, bind_eq] at lowering
  obtain ⟨id, middle, exprRun, result, casted, castRun, effectRun⟩ := lowering
  have castLower : coerceTo declaration.ty id org
      (lowerEnv cfg.mod env.vars results) middle = (result, casted) := by
    rw [← coerceSlot_eq slotAt id org]
    exact castRun
  have effectExtension := extension
  have castExtension := effectExtension.of_adv (adv_emitEffect effectRun)
  have exprExtension := castExtension.of_adv
    (advB_coerceSlot slot id org _ _ _ _ castRun)
  have exprReflection := child env state exprSource exprMetadata ls middle id point cx fr
    exprRun entry exprExtension rel module resultsEq generated
  have generatedMiddle := generated.lowerExpr expr exprRun
  have generatedCasted := generatedMiddle.coerceSlot slot id org castRun
  have generatedAfter := generatedCasted.emitEffect (.slotInit slot result (some org)) effectRun
  have composition : ReflectAtFuel fuel cx point fr
      (fun n => evalExpr n cfg env expr >>= fun value =>
        (pure value : M Val) >>= fun _ =>
          (rootOf env slot >>= fun root => bindRoot root value) >>= fun _ =>
            pure (Flow.normal .unit))
      (fun flow _ point' frame' =>
        StatementLoopPost cfg env cx ls fr after loop flow point' frame') state := by
    refine exprReflection.bind ?_ (fun n k bound => (monoAll n k bound).expr cfg env expr)
      (fun _ n k bound => MonoM.refl _)
    intro n value nextState exprPoint exprFrame exprDone exprPost residual residualBound
    have sourceResult := exprSource.result n value exprDone
    have shape := sourceResult.coercionValue passable
    have coercion := coerceTo_reflectAtFuel (fuel := residual) (state := nextState)
      exprPost shape castLower castExtension
    have continuation : ReflectAtFuel residual cx exprPoint exprFrame
        (fun _ => (pure value : M Val) >>= fun _ =>
          (rootOf env slot >>= fun root => bindRoot root value) >>= fun _ =>
            pure (Flow.normal .unit))
        (fun flow _ point' frame' =>
          StatementLoopPost cfg env cx ls fr after loop flow point' frame') nextState := by
      refine coercion.bind ?_ (fun n k bound => MonoM.refl _)
        (fun _ n k bound => MonoM.refl _)
      intro k coercedValue castState castPoint castFrame castDone castMatched remaining remainingBound
      rcases castMatched with ⟨rfl, castPost⟩
      have resultCell := castPost.has (result, .val coercedValue) (by simp)
      let effectSource : M Unit := rootOf env slot >>= fun root => bindRoot root coercedValue
      have effectEqual : execEff cx.fn castFrame (.slotInit slot result (some org)) =
          (rootOf env slot >>= fun root => bindRoot root coercedValue) >>= fun _ => pure castFrame := by
        simp only [execEff, slotRoot_eq castPost.rel slot, getVal_of resultCell,
          bind_assoc, pure_bind]
      have effectReflection : ReflectAtFuel remaining cx castPoint castFrame
          (fun _ => effectSource)
          (fun _ _ point' frame' => Post cfg env cx ls fr after frame' point' []) castState := by
        cases remaining with
        | zero =>
          exact ReflectAtFuel.zero cx castPoint castFrame (fun _ => effectSource)
            (fun _ _ point' frame' => Post cfg env cx ls fr after frame' point' []) castState
        | succ effectFuel =>
          exact leaf_eff_reflectAtFuel (fuel := effectFuel) (state := castState)
            castPost effectRun extension (sourceFuel := 0) effectEqual
      have effectFinish : ReflectAtFuel remaining cx castPoint castFrame
          (fun _ => effectSource >>= fun _ => pure (Flow.normal .unit))
          (fun flow _ point' frame' =>
            StatementLoopPost cfg env cx ls fr after loop flow point' frame') castState := by
        refine effectReflection.bind ?_
          (fun n k bound => MonoM.refl effectSource)
          (fun (_ : Unit) n k bound => MonoM.refl (pure (Flow.normal .unit)))
        intro j _ effectState effectPoint effectFrame effectDone effectPost finalFuel finalBound
        exact ReflectAtFuel.ret finalFuel
          (Or.inl ⟨rfl, effectPost.sub (by simp)⟩)
      simpa only [effectSource, pure_bind, bind_assoc] using effectFinish
    exact continuation
  refine composition.of_source fun n => ⟨n + 1, ?_⟩
  simp only [execStmt]
  have preparedNormal : prepareLoopFlow env loop (.normal .unit) = pure (.normal .unit) := by
    cases loop <;> simp [prepareLoopFlow, prepareReturn, prepareLoopExit]
  simp only [preparedNormal, bind_assoc, pure_bind]

theorem typedStatementReflection_rebind {fuel : Nat} {cfg : Cfg}
    {results : List Ty} {loop : Option LoopCtx} {slot : VarId} {expr : Expr} {org : OriginId}
    (child : TypedExprReflection fuel cfg results expr) :
    TypedStatementReflection fuel cfg results loop (.rebind slot expr org) := by
  intro env state source metadata loops ls after point cx fr lowering entry extension rel module resultsEq
    depth targets counter generated frames
  obtain ⟨exprSource, declaration, variableAt, typingEq, rootsEq, passable⟩ := source.rebindChild
  have exprMetadata : SourceResults exprSource.typingEnv exprSource.rootsEnv results := by
    rw [typingEq, rootsEq]
    exact metadata
  have slotAt : (lowerEnv cfg.mod env.vars results).slots[slot]? =
      some (⟨declaration.ty, declaration.kind, declaration.scope, slot⟩ : Slot) := by
    simp [lowerEnv, Array.getElem?_mapIdx, variableAt]
  have lowerRun := lowering
  simp only [lowerStmt, bind_eq] at lowering
  obtain ⟨id, middle, exprRun, result, casted, castRun, address, addressed, addressRun, effectRun⟩ := lowering
  have castLower : coerceTo declaration.ty id org
      (lowerEnv cfg.mod env.vars results) middle = (result, casted) := by
    rw [← coerceSlot_eq slotAt id org]
    exact castRun
  have effectExtension := extension
  have addressExtension := effectExtension.of_adv (adv_emitEffect effectRun)
  have castExtension := addressExtension.of_adv (adv_emitDef addressRun)
  have exprExtension := castExtension.of_adv
    (advB_coerceSlot slot id org _ _ _ _ castRun)
  have exprReflection := child env state exprSource exprMetadata ls middle id point cx fr
    exprRun entry exprExtension rel module resultsEq generated
  have generatedMiddle := generated.lowerExpr expr exprRun
  have generatedCasted := generatedMiddle.coerceSlot slot id org castRun
  have generatedAddress := generatedCasted.emitDef (.slotAddr slot) addressRun
  have generatedAfter := generatedAddress.emitEffect (.store address result (some org)) effectRun
  have composition : ReflectAtFuel fuel cx point fr
      (fun n => evalExpr n cfg env expr >>= fun value =>
        (pure value : M Val) >>= fun _ =>
          (rootOf env slot >>= fun root => writeLoc ⟨root, []⟩ value) >>= fun _ =>
            pure (Flow.normal .unit))
      (fun flow _ point' frame' =>
        StatementLoopPost cfg env cx ls fr after loop flow point' frame') state := by
    refine exprReflection.bind ?_ (fun n k bound => (monoAll n k bound).expr cfg env expr)
      (fun _ n k bound => MonoM.refl _)
    intro n value nextState exprPoint exprFrame exprDone exprPost residual residualBound
    have sourceResult := exprSource.result n value exprDone
    have shape := sourceResult.coercionValue passable
    have coercion := coerceTo_reflectAtFuel (fuel := residual) (state := nextState)
      exprPost shape castLower castExtension
    have continuation : ReflectAtFuel residual cx exprPoint exprFrame
        (fun _ => (pure value : M Val) >>= fun _ =>
          (rootOf env slot >>= fun root => writeLoc ⟨root, []⟩ value) >>= fun _ =>
            pure (Flow.normal .unit))
        (fun flow _ point' frame' =>
          StatementLoopPost cfg env cx ls fr after loop flow point' frame') nextState := by
      refine coercion.bind ?_ (fun n k bound => MonoM.refl _)
        (fun _ n k bound => MonoM.refl _)
      intro k coercedValue castState castPoint castFrame castDone castMatched remaining remainingBound
      rcases castMatched with ⟨rfl, castPost⟩
      have addressReflection := leaf_def_keep_reflectAtFuel (fuel := remaining) (state := castState)
        castPost addressRun addressExtension (by intro function args origin impossible; cases impossible)
        (fun (root : RootInst) => RVal.val (.ref ⟨root, []⟩))
        (source := fun _ : Nat => rootOf env slot) (sourceFuel := 0) (by
          simp only [execPure, slotRoot_eq castPost.rel slot])
      have addressContinuation : ReflectAtFuel remaining cx castPoint castFrame
          (fun _ => rootOf env slot >>= fun root =>
            (writeLoc ⟨root, []⟩ coercedValue >>= fun _ => pure (Flow.normal .unit)))
          (fun flow _ point' frame' =>
            StatementLoopPost cfg env cx ls fr after loop flow point' frame') castState := by
        refine addressReflection.bind ?_ (fun n k bound => MonoM.refl _)
          (fun _ n k bound => MonoM.refl _)
        intro j root addressState addressPoint addressFrame addressDone addressPost effectFuel effectBound
        have addressCell := addressPost.has (address, .val (.ref ⟨root, []⟩)) (by simp)
        have resultCell := addressPost.has (result, .val coercedValue) (by simp)
        let effectSource : M Unit := writeLoc ⟨root, []⟩ coercedValue
        have effectEqual : execEff cx.fn addressFrame (.store address result (some org)) =
            writeLoc ⟨root, []⟩ coercedValue >>= fun _ => pure addressFrame := by
          simp only [execEff, getVal_of addressCell, getVal_of resultCell,
            Goose.Core.expectRef, pure_bind]
        have effectReflection : ReflectAtFuel effectFuel cx addressPoint addressFrame
            (fun _ => effectSource)
            (fun _ _ point' frame' => Post cfg env cx ls fr after frame' point' []) addressState := by
          cases effectFuel with
          | zero =>
            exact ReflectAtFuel.zero cx addressPoint addressFrame (fun _ => effectSource)
              (fun _ _ point' frame' => Post cfg env cx ls fr after frame' point' []) addressState
          | succ fuel =>
            exact leaf_eff_reflectAtFuel (fuel := fuel) (state := addressState)
              addressPost effectRun extension (sourceFuel := 0) effectEqual
        have effectFinish : ReflectAtFuel effectFuel cx addressPoint addressFrame
            (fun _ => effectSource >>= fun _ => pure (Flow.normal .unit))
            (fun flow _ point' frame' =>
              StatementLoopPost cfg env cx ls fr after loop flow point' frame') addressState := by
          refine effectReflection.bind ?_
            (fun n k bound => MonoM.refl effectSource)
            (fun (_ : Unit) n k bound => MonoM.refl (pure (Flow.normal .unit)))
          intro final _ finishState finishPoint finishFrame finishDone finishPost finalFuel finalBound
          exact ReflectAtFuel.ret finalFuel
            (Or.inl ⟨rfl, finishPost.sub (by simp)⟩)
        simpa only [effectSource, pure_bind] using effectFinish
      simpa only [bind_assoc] using addressContinuation
    exact continuation
  refine composition.of_source fun n => ⟨n + 1, ?_⟩
  simp only [execStmt]
  have preparedNormal : prepareLoopFlow env loop (.normal .unit) = pure (.normal .unit) := by
    cases loop <;> simp [prepareLoopFlow, prepareReturn, prepareLoopExit]
  simp only [preparedNormal, bind_assoc, pure_bind]

end Goose.Lower
