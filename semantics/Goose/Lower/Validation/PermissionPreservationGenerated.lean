import Goose.Lower.Validation.ExpressionTypingGenerated
import Goose.Lower.Validation.PermissionPreservationPlaces
import Goose.Lower.Validation.PermissionPreservationPlaceSources
import Goose.Lower.Validation.PermissionPreservationFreshBorrow
import Goose.Lower.Validation.PermissionPreservationJoin

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

private theorem permission_generated_pushScope {before after : LS} (generated : GeneratedBuilderState before)
    {scope : ScopeId} {le : LEnv} {result : Unit}
    (run : pushScope scope le before = (result, after)) : GeneratedBuilderState after := by
  rw [pushScope_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact ⟨generated.dense, generated.live, generated.targets⟩

private theorem permission_generated_setCur_sizes {before after : LS} {le : LEnv} {current : Option BlockId}
    {result : Unit} (run : setCur current le before = (result, after)) :
    after.blocks.size = before.blocks.size ∧ after.vals.size = before.vals.size := by
  rw [setCur_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact ⟨rfl, rfl⟩

set_option maxHeartbeats 2000000

mutual

theorem lowerExpr_generated_binding (expr : Expr)
    {env : Core.TEnv} {target : Ty} {start finish : Nat}
    (source : Core.tyExpr env expr start = .ok (.ref .mutable target, finish))
    (demand : BindingTarget env.mod.profile target)
    {results : List Ty} {before after : LS} {value : ValueId}
    (run : lowerExpr expr (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true)
    (generated : GeneratedBuilderState before := by assumption) :
    FreshWritableEvidence (lowerEnv env.mod env.vars results) before.vals.size after value := by
  have form := tyExpr_mutable_reference_form source
  cases expr with
  | read place =>
    have lowering := run
    simp only [lowerExpr] at lowering
    obtain ⟨address, middle, placeRun, emitted⟩ := bind_eq.mp lowering
    have middleLive := (dead_emitDef (.load address)).live_before emitted live
    have middleGenerated := generated.lowerPlace place placeRun
    have typed := lowerExpr_generated_typed (.read place) source run live (generated := generated)
    cases current : middle.cur with
    | none => simp [current] at middleLive
    | some block =>
      exact (freshWritableEvidence_load middleGenerated.dense middleGenerated.live current emitted typed).weaken
        (advB_lowerPlace place _ _ _ _ placeRun).vals
  | ref mu place =>
    cases mu with
    | readOnly =>
      obtain ⟨info, _, _, shape, _⟩ := tyExpr_ref_place source
      cases shape
    | mutable =>
      obtain ⟨info, placeFinish, placeSource, shape, reference, writable⟩ :=
        source_mutable_reference_permissions source
      have referent := (Ty.ref.inj shape).2
      have targetDemand : BindingTarget env.mod.profile info.ty := by simpa only [referent] using demand
      have lowering := run
      simp only [lowerExpr] at lowering
      obtain ⟨owner, middle, placeRun, borrowed⟩ := bind_eq.mp lowering
      have middleLive := (dead_borrowTo .mutable owner).live_before borrowed live
      have middleGenerated := generated.lowerPlace place placeRun
      have typed := lowerPlace_generated_writable_typed place placeSource writable placeRun middleLive (generated := generated)
      by_cases resizable : (∃ element, info.ty = .grow element) ∨ (∃ element, info.ty = .growshrink element)
      · have profile : env.mod.profile = .shrink := by
          rcases resizable with ⟨element, same⟩ | ⟨element, same⟩ <;>
            simpa only [BindingTarget, same] using targetDemand
        have container : ContentsTarget info.ty := by
          rcases resizable with ⟨element, same⟩ | ⟨element, same⟩ <;> rw [same] <;> trivial
        have contents := source_place_reference_contents placeSource container reference writable
        have evidence := lowerPlace_generated_contents place placeSource container contents placeRun middleLive (generated := generated)
        cases current : middle.cur with
        | none => simp [current] at middleLive
        | some block =>
          exact (borrowTo_owner_fresh_permissions evidence middleGenerated.dense middleGenerated.live
            current profile typed resizable borrowed).1
      · have ordinary : BindingTarget .pilot info.ty := by
          cases same : info.ty <;> simp_all [BindingTarget]
        have binding : info.bindingWritable = true := by
          cases same : info.ty <;> simp_all [BindingTarget, PlaceInfo.referenceWritable]
        have evidence := lowerPlace_generated_binding place placeSource binding targetDemand placeRun middleLive
        exact borrowTo_ordinary_fresh_binding evidence typed ordinary borrowed
  | pop owner origin =>
    have lowering := run
    simp only [lowerExpr] at lowering
    obtain ⟨address, middle, ownerRun, emitted⟩ := bind_eq.mp lowering
    have middleLive := (dead_emitDef (.pop address (some origin))).live_before emitted live
    have middleGenerated := generated.lowerPlace owner ownerRun
    have typed := lowerExpr_generated_typed (.pop owner origin) source run live (generated := generated)
    cases current : middle.cur with
    | none => simp [current] at middleLive
    | some block =>
      exact (freshWritableEvidence_pop middleGenerated.dense middleGenerated.live current emitted typed).weaken
        (advB_lowerPlace owner _ _ _ _ ownerRun).vals
  | push owner child origin =>
    have lowering := run
    simp only [lowerExpr] at lowering
    obtain ⟨address, ownerAfter, ownerRun, lowering⟩ := bind_eq.mp lowering
    obtain ⟨childValue, middle, childRun, emitted⟩ := bind_eq.mp lowering
    have ownerGenerated := generated.lowerPlace owner ownerRun
    have middleGenerated := ownerGenerated.lowerExpr child childRun
    have middleLive := (dead_emitDef (.push address childValue origin)).live_before emitted live
    have typed := lowerExpr_generated_typed (.push owner child origin) source run live (generated := generated)
    cases current : middle.cur with
    | none => simp [current] at middleLive
    | some block =>
      exact (freshWritableEvidence_push middleGenerated.dense middleGenerated.live current emitted typed).weaken
        (Nat.le_trans (advB_lowerPlace owner _ _ _ _ ownerRun).vals (advB_lowerExpr child _ _ _ _ childRun).vals)
  | call context args origin =>
    obtain ⟨ctx, callee, argsStart, argsFinish, resultStart, contextRow, calleeRow,
      sameLength, argsSource, resultSource⟩ := tyExpr_call_tables source
    have lowering := run
    simp only [lowerExpr] at lowering
    obtain ⟨arguments, middle, argsRun, lowering⟩ := bind_eq.mp lowering
    obtain ⟨emittedValue, emitted, emitRun, tailRun⟩ := bind_eq.mp lowering
    rw [call_result_tail_run] at tailRun
    by_cases returns : (lowerEnv env.mod env.vars results).mod.noReturn context = true
    · simp only [returns, ite_true] at tailRun
      cases current : emitted.cur with
      | none =>
        rw [emitTerm_none _ _ current] at tailRun
        obtain ⟨_, rfl⟩ := Prod.mk.inj tailRun
        simp [current] at live
      | some block =>
        rw [emitTerm_run _ _ current] at tailRun
        obtain ⟨_, rfl⟩ := Prod.mk.inj tailRun
        contradiction
    · simp only [returns] at tailRun
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj tailRun
      have middleLive := (dead_emitDef (.call context arguments (some origin))).live_before emitRun live
      have middleGenerated := generated.lowerArgs args argsRun
      have typed := lowerExpr_generated_typed (.call context args origin) source run live (generated := generated)
      cases current : middle.cur with
      | none => simp [current] at middleLive
      | some block =>
        exact (freshWritableEvidence_call middleGenerated.dense middleGenerated.live current emitRun typed).weaken
          (advB_lowerArgs args _ _ _ _ argsRun).vals
  | blockE body => exact lowerBlock_generated_binding body source demand run live
  | ifE condition thenBody elseBody =>
    simp only [Core.tyExpr] at source
    obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨thenTy, _, thenSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨elseTy, elseFinish, elseSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    by_cases equal : (thenTy == elseTy) = true
    · simp only [equal, ite_true] at source
      have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
      change Ty.ref .mutable target = thenTy at shape
      have typesEqual : thenTy = elseTy := eq_of_beq equal
      subst elseTy
      subst thenTy
      simp only [lowerExpr] at run
      obtain ⟨conditionValue, middle, conditionRun, run⟩ := bind_eq.mp run
      cases current : middle.cur with
      | none =>
        rw [whenLive_none _ _ _ current] at run
        obtain ⟨_, rfl⟩ := Prod.mk.inj run
        simp [current] at live
      | some block =>
        rw [whenLive_some _ _ _ current] at run
        obtain ⟨arms, forked, forkRun, run⟩ := bind_eq.mp run
        obtain ⟨_, thenStart, thenStartRun, run⟩ := bind_eq.mp run
        obtain ⟨thenValue, thenAfter, thenRun, run⟩ := bind_eq.mp run
        obtain ⟨thenEnd, thenClosed, thenEndRun, run⟩ := bind_eq.mp run
        rw [curBlock_run] at thenEndRun
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj thenEndRun
        obtain ⟨_, elseStart, elseStartRun, run⟩ := bind_eq.mp run
        obtain ⟨elseValue, elseAfter, elseRun, run⟩ := bind_eq.mp run
        obtain ⟨elseEnd, elseClosed, elseEndRun, run⟩ := bind_eq.mp run
        rw [curBlock_run] at elseEndRun
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj elseEndRun
        have middleGenerated := generated.lowerExpr condition conditionRun
        have forkGenerated := middleGenerated.fork conditionValue forkRun
        have ids := fork_ids forkRun
        have thenBound : arms.1 < forked.blocks.size := by
          rw [ids.1, ids.2]
          exact Nat.lt_add_of_pos_right (by decide : 0 < 2)
        have elseBound : arms.2 < forked.blocks.size := by
          rw [ids.1, ids.2]
          exact Nat.add_lt_add_left (by decide : 1 < 2) _
        have thenGenerated := forkGenerated.setCur (some arms.1)
          (by intro target same; cases same; exact thenBound) thenStartRun
        have thenAfterGenerated := thenGenerated.lowerBlock none [] true thenBody trivial thenRun
        have elseTargetBound : arms.2 < thenAfter.blocks.size := by
          rw [← (permission_generated_setCur_sizes thenStartRun).1] at elseBound
          exact Nat.lt_of_lt_of_le elseBound (advB_lowerBlock none [] true thenBody _ _ _ _ thenRun).ext.1
        have elseGenerated := thenAfterGenerated.setCur (some arms.2)
          (by intro target same; cases same; exact elseTargetBound) elseStartRun
        have thenTyped : thenAfter.cur.isSome = true → elseAfter.vals[thenValue]? = some (some (.data (.ref .mutable target))) := by
          intro branchLive
          have typed := lowerBlock_generated_typed thenBody thenSource thenRun branchLive (generated := thenGenerated)
          have retained := types_setCur _ _ _ _ _ elseStartRun thenValue (.data (.ref .mutable target)) typed
          exact types_lowerBlock _ _ _ _ _ _ _ _ elseRun thenValue (.data (.ref .mutable target)) retained
        have elseTyped : elseAfter.cur.isSome = true → elseAfter.vals[elseValue]? = some (some (.data (.ref .mutable target))) := by
          intro branchLive
          exact lowerBlock_generated_typed elseBody elseSource elseRun branchLive (generated := elseGenerated)
        have elseAfterGenerated := elseGenerated.lowerBlock none [] true elseBody trivial elseRun
        have beforeThen : before.vals.size ≤ thenStart.vals.size := by
          have a := (advB_lowerExpr condition _ _ _ _ conditionRun).vals
          have b := (advB_fork conditionValue _ _ _ _ forkRun).vals
          have c := (permission_generated_setCur_sizes thenStartRun).2
          omega
        have beforeElse : before.vals.size ≤ elseStart.vals.size := by
          have a := (advB_lowerBlock none [] true thenBody _ _ _ _ thenRun).vals
          have b := (permission_generated_setCur_sizes elseStartRun).2
          omega
        have beforeJoin : before.vals.size ≤ elseAfter.vals.size := Nat.le_trans beforeElse
          (advB_lowerBlock none [] true elseBody _ _ _ _ elseRun).vals
        have thenEvidence : thenAfter.cur.isSome = true →
            FreshWritableEvidence (lowerEnv env.mod env.vars results) before.vals.size elseAfter thenValue := by
          intro branchLive
          have evidence := (lowerBlock_generated_binding thenBody thenSource demand thenRun branchLive).weaken beforeThen
          have moved := evidence.setCur elseStartRun
          exact moved.of_framed_run (loop := none) elseRun (dense_lowerBlock none [] true elseBody)
            (advB_lowerBlock none [] true elseBody) (types_lowerBlock none [] true elseBody)
            (generatedTargetFrame_lowerBlock none [] true elseBody) elseGenerated.dense elseGenerated.live trivial
        have elseEvidence : elseAfter.cur.isSome = true →
            FreshWritableEvidence (lowerEnv env.mod env.vars results) before.vals.size elseAfter elseValue := by
          intro branchLive
          exact (lowerBlock_generated_binding elseBody elseSource demand elseRun branchLive).weaken beforeElse
        have thenBound : ∀ endpoint, thenAfter.cur = some endpoint → endpoint < elseAfter.blocks.size := by
          intro endpoint row
          have bounded := thenAfterGenerated.live endpoint row
          apply Nat.lt_of_lt_of_le bounded
          exact Nat.le_trans (Nat.le_of_eq (permission_generated_setCur_sizes elseStartRun).1.symm)
            (advB_lowerBlock none [] true elseBody _ _ _ _ elseRun).ext.1
        have joined := joinValue_freshWritable elseAfterGenerated.dense elseAfterGenerated.live
          elseAfterGenerated.targets thenBound elseAfterGenerated.live thenTyped elseTyped
          (by intro intTy unequal; cases unequal) beforeJoin thenEvidence elseEvidence
        rw [run] at joined
        exact (joined live).1
    · simp only [equal] at source
      change ((rej .type "the branches of `if` have different types" : Core.T Unit) >>=
        fun _ => pure thenTy) elseFinish = .ok (.ref .mutable target, finish) at source
      obtain ⟨_, _, rejected, _⟩ := (st_bind_ok _ _ _ _).mp source
      exact (rej_ok _ _ _ _).mp rejected |>.elim
  | _ => simp only [MutableReferenceExpression] at form


theorem lowerPlace_generated_binding (place : Place)
    {env : Core.TEnv} {info : PlaceInfo} {start finish : Nat}
    (source : Core.tyPlace env place start = .ok (info, finish))
    (binding : info.bindingWritable = true) (demand : BindingTarget env.mod.profile info.ty)
    {results : List Ty} {before after : LS} {value : ValueId}
    (run : lowerPlace place (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true)
    (generated : GeneratedBuilderState before := by assumption) :
    FreshWritableEvidence (lowerEnv env.mod env.vars results) before.vals.size after value := by
  cases place with
  | var index =>
    have initial := (dead_lowerPlace (.var index)).live_before run live
    cases current : before.cur with
    | none => simp [current] at initial
    | some block => exact lowerPlace_var_fresh_binding_evidence source binding generated.dense generated.live current run
  | global index =>
    have initial := (dead_lowerPlace (.global index)).live_before run live
    cases current : before.cur with
    | none => simp [current] at initial
    | some block => exact lowerPlace_global_fresh_binding_evidence source binding generated.dense generated.live current run
  | field owner index =>
    obtain ⟨ownerInfo, ownerFinish, field, fieldFinish, ownerSource, fieldSource, ownerContents, mutable⟩ :=
      source_field_binding_authority source binding
    obtain ⟨id, fields, descriptor, shape, descriptorRow, _, fieldRow⟩ := structField_descriptor fieldSource
    have ownerContainer : ContentsTarget ownerInfo.ty := by rw [shape]; trivial
    have lowering := run
    simp only [lowerPlace] at lowering
    obtain ⟨ownerValue, middle, ownerRun, emitted⟩ := bind_eq.mp lowering
    have middleLive := (dead_emitDef (.fieldAddr ownerValue index)).live_before emitted live
    have middleGenerated := generated.lowerPlace owner ownerRun
    obtain ⟨actual, ownerTyped⟩ := lowerPlace_generated_typed owner ownerSource ownerRun middleLive (generated := generated)
    rw [shape] at ownerTyped
    have evidence := lowerPlace_generated_contents owner ownerSource ownerContainer ownerContents ownerRun middleLive (generated := generated)
    cases current : middle.cur with
    | none => simp [current] at middleLive
    | some block =>
      exact evidence.fieldAddr_binding middleGenerated.dense middleGenerated.live current
        ownerTyped descriptorRow fieldRow mutable emitted
  | deref expr =>
    by_cases loadedVariable : ∃ index, expr = .read (.var index)
    · obtain ⟨index, rfl⟩ := loadedVariable
      have authority := source_deref_binding_referenceWritable source binding
      have typed := lowerPlace_generated_writable_typed (.deref (.read (.var index))) source authority run live (generated := generated)
      have lowering := run
      simp only [lowerPlace, lowerExpr] at lowering
      obtain ⟨owner, middle, slotRun, emitted⟩ := bind_eq.mp lowering
      have middleLive := (dead_emitDef (.load owner)).live_before emitted live
      have middleGenerated := generated.emitDef (.slotAddr index) slotRun
      cases current : middle.cur with
      | none => simp [current] at middleLive
      | some block =>
        exact (freshWritableEvidence_load middleGenerated.dense middleGenerated.live current emitted typed).weaken
          (advB_emitDef (.slotAddr index) _ _ _ _ slotRun).vals
    · have ordinary : Core.sliceRefTy env expr = none := by
        cases expr <;> try rfl
        case read child =>
          cases child <;> try rfl
          case var index => exact (loadedVariable ⟨index, rfl⟩).elim
      obtain ⟨childFinish, childSource⟩ := source_deref_binding_child ordinary source binding
      exact lowerExpr_generated_binding expr childSource demand run live
  | elem view index origin =>
    have contents := source_elem_binding_contents source binding
    obtain ⟨viewStart, viewFinish, indexFinish, intTy, viewSource, indexSource⟩ :=
      tyPlace_elem_contents_children source contents
    have lowering := run
    simp only [lowerPlace] at lowering
    obtain ⟨viewValue, viewAfter, viewRun, lowering⟩ := bind_eq.mp lowering
    obtain ⟨indexValue, indexAfter, indexRun, emitted⟩ := bind_eq.mp lowering
    have indexLive := (dead_emitDef (.indexChecked viewValue indexValue (some origin))).live_before emitted live
    have viewLive := (dead_lowerExpr index).live_before indexRun indexLive
    have viewGenerated := generated.lowerView view viewRun
    have indexGenerated := viewGenerated.lowerExpr index indexRun
    have evidence := lowerView_generated_contents view viewSource viewRun viewLive (generated := generated)
    have retained := evidence.of_framed_run (loop := none) indexRun (dense_lowerExpr index)
      (advB_lowerExpr index) (types_lowerExpr index) (generatedTargetFrame_lowerExpr none index)
      viewGenerated.dense viewGenerated.live trivial
    cases current : indexAfter.cur with
    | none => simp [current] at indexLive
    | some block => exact retained.indexChecked_binding indexGenerated.dense indexGenerated.live current emitted


theorem lowerBlock_generated_binding (body : Core.Block)
    {env : Core.TEnv} {target : Ty} {start finish : Nat}
    (source : Core.tyBlock env [] body start = .ok (.ref .mutable target, finish))
    (demand : BindingTarget env.mod.profile target)
    {results : List Ty} {before after : LS} {value : ValueId}
    (run : lowerBlock none [] true body (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true)
    (generated : GeneratedBuilderState before := by assumption) : FreshWritableEvidence (lowerEnv env.mod env.vars results) before.vals.size after value := by
  cases body with
  | mk scope statements expression =>
    unfold Core.tyBlock at source
    by_cases nested : scope ∈ env.scopes
    · simp [nested, chk] at source
    · simp only [List.contains_iff_mem, nested, ite_false] at source
      obtain ⟨declared, declaredFinish, declaration, source⟩ := (st_bind_ok _ _ _ _).mp source
      obtain ⟨finalEnv, valueStart, statementsTyped, source⟩ := (st_bind_ok _ _ _ _).mp source
      have declaredEnv := declarePre_lowerEnv declaration results
      have finalLower := tyStmts_lowerEnv statementsTyped results
      have sameEnv : lowerEnv finalEnv.mod finalEnv.vars results = lowerEnv env.mod env.vars results :=
        finalLower.trans declaredEnv
      simp only [lowerBlock, inScope] at run
      obtain ⟨_, entered, enterRun, run⟩ := bind_eq.mp run
      obtain ⟨_, pushed, pushRun, run⟩ := bind_eq.mp run
      obtain ⟨result, bodyAfter, bodyRun, run⟩ := bind_eq.mp run
      obtain ⟨_, popped, popRun, run⟩ := bind_eq.mp run
      obtain ⟨resultEq, stateEq⟩ := pure_eq.mp run
      subst after
      subst value
      obtain ⟨_, initialized, initRun, bodyRun⟩ := bind_eq.mp bodyRun
      obtain ⟨_, statementsAfter, statementsRun, bodyRun⟩ := bind_eq.mp bodyRun
      obtain ⟨result, valueAfter, valueRun, bodyRun⟩ := bind_eq.mp bodyRun
      obtain ⟨_, left, leaveRun, bodyRun⟩ := bind_eq.mp bodyRun
      obtain ⟨rfl, rfl⟩ := pure_eq.mp bodyRun
      have poppedLive := dead_popScope.live_before popRun live
      have valueLive := (dead_emitEffect (.leave scope)).live_before leaveRun poppedLive
      have enteredGenerated := generated.emitEffect (.enter scope) enterRun
      have pushedGenerated := permission_generated_pushScope enteredGenerated pushRun
      have initializedGenerated := pushedGenerated.initSlots [] initRun
      have statementsGenerated := initializedGenerated.lowerStmts none statements trivial statementsRun
      have resultEvidence : FreshWritableEvidence (lowerEnv env.mod env.vars results)
          statementsAfter.vals.size valueAfter result := by
        cases expression with
        | none =>
          have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
          cases shape
        | some expr =>
          simp only [lowerBlockValue] at valueRun
          rw [← sameEnv] at valueRun
          have sameProfile : finalEnv.mod.profile = env.mod.profile :=
            congrArg (fun le : LEnv => le.mod.profile) sameEnv
          have finalDemand : BindingTarget finalEnv.mod.profile target := by rw [sameProfile]; exact demand
          have evidence := lowerExpr_generated_binding expr source finalDemand valueRun valueLive
          rw [sameEnv] at evidence
          exact evidence
      have valueGenerated := statementsGenerated.lowerBlockValue true expression valueRun
      have retained := resultEvidence.of_framed_run (loop := none) leaveRun (dense_emitEffect _)
        (advB_emitEffect _) (types_emitEffect _) (generatedTargetFrame_emitEffect none _)
        valueGenerated.dense valueGenerated.live trivial
      rw [popScope_run] at popRun
      obtain ⟨_, rfl⟩ := Prod.mk.inj popRun
      have growth : before.vals.size ≤ statementsAfter.vals.size := by
        have one := (advB_emitEffect (.enter scope) _ _ _ _ enterRun).vals
        have two : entered.vals.size ≤ pushed.vals.size := by
          rw [pushScope_run] at pushRun
          obtain ⟨_, rfl⟩ := Prod.mk.inj pushRun
          exact Nat.le_refl _
        have three := (advB_initSlots [] _ _ _ _ initRun).vals
        have four := (advB_lowerStmts none statements _ _ _ _ statementsRun).vals
        omega
      exact retained.weaken growth




end

#print axioms lowerExpr_generated_binding
#print axioms lowerPlace_generated_binding
#print axioms lowerBlock_generated_binding

end Goose.Lower.Validation
