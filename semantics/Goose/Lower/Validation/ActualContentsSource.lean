import Goose.Lower.Validation.ActualContentsSourceForms
import Goose.Lower.Validation.ActualContentsJoin

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

private theorem actualContents_pushScope {before after : LS} (generated : GeneratedBuilderState before)
    {scope : ScopeId} {le : LEnv} {result : Unit}
    (run : pushScope scope le before = (result, after)) : GeneratedBuilderState after := by
  rw [pushScope_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact ⟨generated.dense, generated.live, generated.targets⟩

private theorem actualContents_setCur_sizes {before after : LS} {le : LEnv} {current : Option BlockId}
    {result : Unit} (run : setCur current le before = (result, after)) :
    after.blocks.size = before.blocks.size ∧ after.vals.size = before.vals.size := by
  rw [setCur_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact ⟨rfl, rfl⟩

private theorem actualContents_setCur_ext {before after : LS} {le : LEnv} {current : Option BlockId}
    {result : Unit} (run : setCur current le before = (result, after)) : before.Ext after := by
  rw [setCur_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact .refl before

mutual

theorem actualContents_sourceExpr (expr : Expr)
    {env : Core.TEnv} {target : Ty} {mu : Mutability} {start finish : Nat}
    (source : Core.tyExpr env expr start = .ok (.ref mu target, finish))
    {results : List Ty} {before after : LS} {value : ValueId}
    (run : lowerExpr expr (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true) (generated : GeneratedBuilderState before) :
    ActualContentsExtraction (lowerEnv env.mod env.vars results) before.vals.size after value := by
  have form := actualContents_reference_form source
  have typed := lowerExpr_generated_typed expr source run live generated
  cases expr with
  | read place =>
    obtain ⟨address, middle, placeRun, emitted⟩ := bind_eq.mp run
    have middleLive := ((dead_emitDef (.load address)).bind fun value =>
      (dead_recordReadValueRootRecipe value place).bind fun _ => DeadRun.pure value).live_before emitted live
    have middleGenerated := generated.lowerPlace place placeRun
    cases current : middle.cur with
    | none => simp [current] at middleLive
    | some block =>
      exact (actualContents_terminal_read middleGenerated current emitted typed).weaken
        (advB_lowerPlace place _ _ _ _ placeRun).vals
  | ref requested place =>
    obtain ⟨info, childFinish, placeSource, _, _⟩ := tyExpr_ref_place source
    obtain ⟨owner, middle, placeRun, borrowed⟩ := bind_eq.mp run
    have middleLive := (dead_borrowTo requested owner).live_before borrowed live
    have middleGenerated := generated.lowerPlace place placeRun
    have extract := actualContents_sourcePlace place placeSource placeRun middleLive generated
    cases current : middle.cur with
    | none => simp [current] at middleLive
    | some block =>
      exact actualContents_borrowTo middleGenerated current borrowed extract
  | pop place origin =>
    obtain ⟨owner, middle, placeRun, emitted⟩ := bind_eq.mp run
    have middleLive := (dead_emitDef (.pop owner (some origin))).live_before emitted live
    have middleGenerated := generated.lowerPlace place placeRun
    cases current : middle.cur with
    | none => simp [current] at middleLive
    | some block =>
      exact (actualContents_terminal (by trivial) middleGenerated current emitted typed).weaken
        (advB_lowerPlace place _ _ _ _ placeRun).vals
  | push place child origin =>
    obtain ⟨owner, ownerAfter, ownerRun, lowering⟩ := bind_eq.mp run
    obtain ⟨childValue, middle, childRun, emitted⟩ := bind_eq.mp lowering
    have middleLive := (dead_emitDef (.push owner childValue origin)).live_before emitted live
    have ownerGenerated := generated.lowerPlace place ownerRun
    have middleGenerated := ownerGenerated.lowerExpr child childRun
    cases current : middle.cur with
    | none => simp [current] at middleLive
    | some block =>
      exact (actualContents_terminal (by trivial) middleGenerated current emitted typed).weaken
        (Nat.le_trans (advB_lowerPlace place _ _ _ _ ownerRun).vals (advB_lowerExpr child _ _ _ _ childRun).vals)
  | call context args origin =>
    obtain ⟨arguments, middle, argsRun, lowering⟩ := bind_eq.mp run
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
      cases current : middle.cur with
      | none => simp [current] at middleLive
      | some block =>
        exact (actualContents_terminal (by trivial) middleGenerated current emitRun typed).weaken
          (advB_lowerArgs args _ _ _ _ argsRun).vals
  | blockE body => exact actualContents_sourceBlock body source run live generated
  | ifE condition thenBody elseBody =>
    simp only [Core.tyExpr] at source
    obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨thenTy, _, thenSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨elseTy, elseFinish, elseSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    by_cases equal : (thenTy == elseTy) = true
    · simp only [equal, ite_true] at source
      have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
      change Ty.ref mu target = thenTy at shape
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
          rw [← (actualContents_setCur_sizes thenStartRun).1] at elseBound
          exact Nat.lt_of_lt_of_le elseBound (advB_lowerBlock none [] true thenBody _ _ _ _ thenRun).ext.1
        have elseGenerated := thenAfterGenerated.setCur (some arms.2)
          (by intro target same; cases same; exact elseTargetBound) elseStartRun
        have thenTyped : thenAfter.cur.isSome = true → elseAfter.vals[thenValue]? = some (some (.data (.ref mu target))) := by
          intro branchLive
          have typed := lowerBlock_generated_typed thenBody thenSource thenRun branchLive thenGenerated
          have retained := types_setCur _ _ _ _ _ elseStartRun thenValue (.data (.ref mu target)) typed
          exact types_lowerBlock _ _ _ _ _ _ _ _ elseRun thenValue (.data (.ref mu target)) retained
        have elseTyped : elseAfter.cur.isSome = true → elseAfter.vals[elseValue]? = some (some (.data (.ref mu target))) := by
          intro branchLive
          exact lowerBlock_generated_typed elseBody elseSource elseRun branchLive elseGenerated
        have elseAfterGenerated := elseGenerated.lowerBlock none [] true elseBody trivial elseRun
        have beforeThen : before.vals.size ≤ thenStart.vals.size := by
          have a := (advB_lowerExpr condition _ _ _ _ conditionRun).vals
          have b := (advB_fork conditionValue _ _ _ _ forkRun).vals
          have c := (actualContents_setCur_sizes thenStartRun).2
          omega
        have beforeElse : before.vals.size ≤ elseStart.vals.size := by
          have a := (advB_lowerBlock none [] true thenBody _ _ _ _ thenRun).vals
          have b := (actualContents_setCur_sizes elseStartRun).2
          omega
        have beforeJoin : before.vals.size ≤ elseAfter.vals.size := Nat.le_trans beforeElse
          (advB_lowerBlock none [] true elseBody _ _ _ _ elseRun).vals
        have thenBound : ∀ endpoint, thenAfter.cur = some endpoint → endpoint < elseAfter.blocks.size := by
          intro endpoint row
          have bounded := thenAfterGenerated.live endpoint row
          exact Nat.lt_of_lt_of_le bounded
            (Nat.le_trans (Nat.le_of_eq (actualContents_setCur_sizes elseStartRun).1.symm)
              (advB_lowerBlock none [] true elseBody _ _ _ _ elseRun).ext.1)
        obtain ⟨joinedValue, joinedState, joinRun, recordTail⟩ := bind_eq.mp run
        obtain ⟨_, recordedState, recordRun, returned⟩ := bind_eq.mp recordTail
        obtain ⟨rfl, rfl⟩ := pure_eq.mp returned
        have joinedLive := (dead_recordValueRootRecipe joinedValue (sourceBlockScope thenBody)).live_before recordRun live
        intro ambient allowed
        let recordedAmbient := ambient.before (advB_recordValueRootRecipe joinedValue
          (sourceBlockScope thenBody) _ _ _ _ recordRun).ext
          (types_recordValueRootRecipe joinedValue (sourceBlockScope thenBody) _ _ _ _ recordRun)
        have arguments := actualContents_joinValue_arguments thenBound elseAfterGenerated.live thenTyped elseTyped
          joinRun joinedLive recordedAmbient allowed
        let joinAmbient := recordedAmbient.before (actualContents_joinValue_ext joinRun)
          (types_joinValue _ _ _ _ _ _ _ _ joinRun)
        have thenEvidence : thenAfter.cur.isSome = true →
            FreshContentsEvidence (lowerEnv env.mod env.vars results) before.vals.size elseAfter thenValue := by
          intro branchLive
          let elseAmbient := joinAmbient.before (advB_lowerBlock none [] true elseBody _ _ _ _ elseRun).ext
            (types_lowerBlock none [] true elseBody _ _ _ _ elseRun)
          let thenAmbient := elseAmbient.before (actualContents_setCur_ext elseStartRun)
            (types_setCur (some arms.2) _ _ _ _ elseStartRun)
          have evidence := (actualContents_sourceBlock thenBody thenSource thenRun branchLive thenGenerated
            thenAmbient (arguments.1 branchLive)).weaken beforeThen
          have moved := evidence.setCur elseStartRun
          exact moved.of_framed_run (loop := none) elseRun (dense_lowerBlock none [] true elseBody)
            (advB_lowerBlock none [] true elseBody) (types_lowerBlock none [] true elseBody)
            (generatedTargetFrame_lowerBlock none [] true elseBody) elseGenerated.dense elseGenerated.live trivial
        have elseEvidence : elseAfter.cur.isSome = true →
            FreshContentsEvidence (lowerEnv env.mod env.vars results) before.vals.size elseAfter elseValue := by
          intro branchLive
          exact (actualContents_sourceBlock elseBody elseSource elseRun branchLive elseGenerated
            joinAmbient (arguments.2 branchLive)).weaken beforeElse
        have joined := joinValue_record_freshContents (sourceBlockScope thenBody)
          elseAfterGenerated.dense elseAfterGenerated.live
          elseAfterGenerated.targets thenBound elseAfterGenerated.live thenTyped elseTyped
          (by intro intTy unequal; cases unequal) beforeJoin thenEvidence elseEvidence
        rw [run] at joined
        exact (joined live).1
    · simp only [equal] at source
      change ((rej .type "the branches of `if` have different types" : Core.T Unit) >>=
        fun _ => pure thenTy) elseFinish = .ok (.ref mu target, finish) at source
      obtain ⟨_, _, rejected, _⟩ := (st_bind_ok _ _ _ _).mp source
      exact (rej_ok _ _ _ _).mp rejected |>.elim
  | _ => simp only [MutableReferenceExpression] at form

theorem actualContents_sourcePlace (place : Place)
    {env : Core.TEnv} {info : PlaceInfo} {start finish : Nat}
    (source : Core.tyPlace env place start = .ok (info, finish))
    {results : List Ty} {before after : LS} {value : ValueId}
    (run : lowerPlace place (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true) (generated : GeneratedBuilderState before) :
    ActualContentsExtraction (lowerEnv env.mod env.vars results) before.vals.size after value := by
  cases place with
  | var index =>
    have initial := (dead_lowerPlace (.var index)).live_before run live
    cases current : before.cur with
    | none => simp [current] at initial
    | some block =>
      intro _ _
      exact lowerPlace_var_fresh_contents source generated.dense generated.live current run
  | global index =>
    have initial := (dead_lowerPlace (.global index)).live_before run live
    cases current : before.cur with
    | none => simp [current] at initial
    | some block =>
      intro _ _
      exact lowerPlace_global_fresh_contents source generated.dense generated.live current run
  | field owner index =>
    have children := source
    simp only [Core.tyPlace] at children
    obtain ⟨ownerInfo, ownerFinish, ownerSource, _⟩ := (st_bind_ok _ _ _ _).mp children
    obtain ⟨ownerValue, middle, ownerRun, emitted⟩ := bind_eq.mp run
    have middleLive := (dead_emitDef (.fieldAddr ownerValue index)).live_before emitted live
    have middleGenerated := generated.lowerPlace owner ownerRun
    obtain ⟨actual, ownerTyped⟩ := lowerPlace_generated_typed owner ownerSource ownerRun middleLive generated
    have extract := actualContents_sourcePlace owner ownerSource ownerRun middleLive generated
    cases current : middle.cur with
    | none => simp [current] at middleLive
    | some block =>
      intro ambient allowed
      obtain ⟨ownerAllowed, mu, id, fields, descriptor, field, typed, descriptorRow, fieldRow, writable⟩ :=
        ambient.emitted current (middleGenerated.live block current) emitted allowed
      have evidence := extract (ambient.before (advB_emitDef _ _ _ _ _ emitted).ext
        (types_emitDef _ _ _ _ _ emitted)) ownerAllowed
      have retained := types_emitDef (.fieldAddr ownerValue index) _ _ _ _ emitted ownerValue _ ownerTyped
      have agreement : after.vals[ownerValue]? = ambient.state.vals[ownerValue]? :=
        retained.trans (ambient.types ownerValue _ retained).symm
      apply evidence.emitDef_dependency middleGenerated.dense middleGenerated.live current emitted
      intro authorized permitted
      exact ⟨permitted, mu, id, fields, descriptor, field, agreement.trans typed,
        descriptorRow, fieldRow, writable⟩
  | deref expr =>
    cases special : Core.sliceRefTy env expr with
    | none =>
      obtain ⟨mu, childFinish, childSource⟩ := tyPlace_deref_child special source
      exact actualContents_sourceExpr expr childSource run live generated
    | some target =>
      have typed := lowerPlace_generated_typed (.deref expr) source run live generated
      cases expr with
      | read place =>
        cases place with
        | var index =>
          obtain ⟨address, middle, placeRun, emitted⟩ := bind_eq.mp run
          have middleLive := ((dead_emitDef (.load address)).bind fun value =>
            (dead_recordReadValueRootRecipe value (.var index)).bind fun _ => DeadRun.pure value).live_before emitted live
          have middleGenerated := generated.lowerPlace (.var index) placeRun
          cases current : middle.cur with
          | none => simp [current] at middleLive
          | some block =>
            obtain ⟨_, typed⟩ := typed
            exact (actualContents_terminal_read middleGenerated current emitted typed).weaken
              (advB_lowerPlace (.var index) _ _ _ _ placeRun).vals
        | _ => simp [Core.sliceRefTy] at special
      | _ => simp [Core.sliceRefTy] at special
  | elem view index origin =>
    obtain ⟨viewStart, viewFinish, indexFinish, writable, intTy, viewSource, indexSource⟩ := tyPlace_elem_children source
    obtain ⟨viewValue, viewAfter, viewRun, lowering⟩ := bind_eq.mp run
    obtain ⟨indexValue, indexAfter, indexRun, emitted⟩ := bind_eq.mp lowering
    have indexLive := (dead_emitDef (.indexChecked viewValue indexValue (some origin))).live_before emitted live
    have viewLive := (dead_lowerExpr index).live_before indexRun indexLive
    have viewGenerated := generated.lowerView view viewRun
    have indexGenerated := viewGenerated.lowerExpr index indexRun
    have extract := actualContents_sourceView view viewSource viewRun viewLive generated
    cases current : indexAfter.cur with
    | none => simp [current] at indexLive
    | some block =>
      intro ambient allowed
      have ownerAllowed := ambient.emitted current (indexGenerated.live block current) emitted allowed
      let indexAmbient := ambient.before (advB_emitDef _ _ _ _ _ emitted).ext
        (types_emitDef _ _ _ _ _ emitted)
      let viewAmbient := indexAmbient.before (advB_lowerExpr index _ _ _ _ indexRun).ext
        (types_lowerExpr index _ _ _ _ indexRun)
      have evidence := extract viewAmbient ownerAllowed
      exact lowerPlace_elem_fresh_contents_of_children viewRun indexRun evidence
        viewGenerated.dense viewGenerated.live current run

theorem actualContents_sourceView (view : View)
    {env : Core.TEnv} {pair : Ty × Bool} {start finish : Nat}
    (source : Core.tyView env view start = .ok (pair, finish))
    {results : List Ty} {before after : LS} {value : ValueId}
    (run : lowerView view (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true) (generated : GeneratedBuilderState before) :
    ActualContentsExtraction (lowerEnv env.mod env.vars results) before.vals.size after value := by
  cases view with
  | val expr =>
    obtain ⟨child, middle, childRun, emitted⟩ := bind_eq.mp run
    have middleLive := (dead_emitDef (.sliceView child)).live_before emitted live
    have middleGenerated := generated.lowerExpr expr childRun
    obtain ⟨mu, typed⟩ := lowerView_generated_typed (.val expr) source run live generated
    cases current : middle.cur with
    | none => simp [current] at middleLive
    | some block =>
      exact (actualContents_terminal (by trivial) middleGenerated current emitted typed).weaken
        (advB_lowerExpr expr _ _ _ _ childRun).vals
  | of place =>
    have children := source
    simp only [Core.tyView] at children
    obtain ⟨info, placeFinish, placeSource, _⟩ := (st_bind_ok _ _ _ _).mp children
    obtain ⟨ownerValue, middle, placeRun, emitted⟩ := bind_eq.mp run
    have middleLive := (dead_emitDef _).live_before emitted live
    have middleGenerated := generated.lowerPlace place placeRun
    have extract := actualContents_sourcePlace place placeSource placeRun middleLive generated
    cases current : middle.cur with
    | none => simp [current] at middleLive
    | some block =>
      intro ambient allowed
      have ownerAllowed := ambient.emitted current (middleGenerated.live block current) emitted allowed
      have evidence := extract (ambient.before (advB_emitDef _ _ _ _ _ emitted).ext
        (types_emitDef _ _ _ _ _ emitted)) ownerAllowed
      exact lowerView_of_fresh_contents_of_place placeRun evidence middleGenerated.dense middleGenerated.live current run

theorem actualContents_sourceBlock (body : Core.Block)
    {env : Core.TEnv} {target : Ty} {mu : Mutability} {start finish : Nat}
    (source : Core.tyBlock env [] body start = .ok (.ref mu target, finish))
    {results : List Ty} {before after : LS} {value : ValueId}
    (run : lowerBlock none [] true body (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true) (generated : GeneratedBuilderState before) :
    ActualContentsExtraction (lowerEnv env.mod env.vars results) before.vals.size after value := by
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
      have pushedGenerated := actualContents_pushScope enteredGenerated pushRun
      have initializedGenerated := pushedGenerated.initSlots [] initRun
      have statementsGenerated := initializedGenerated.lowerStmts none statements trivial statementsRun
      intro ambient allowed
      have popExtension : left.Ext popped := by
        rw [popScope_run] at popRun
        obtain ⟨_, rfl⟩ := Prod.mk.inj popRun
        exact .refl left
      let leftAmbient := ambient.before popExtension (types_popScope _ _ _ _ popRun)
      let valueAmbient := leftAmbient.before (advB_emitEffect _ _ _ _ _ leaveRun).ext
        (types_emitEffect _ _ _ _ _ leaveRun)
      have resultEvidence : FreshContentsEvidence (lowerEnv env.mod env.vars results)
          statementsAfter.vals.size valueAfter result := by
        cases expression with
        | none =>
          have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
          cases shape
        | some expr =>
          simp only [lowerBlockValue] at valueRun
          rw [← sameEnv] at valueRun
          have extract := actualContents_sourceExpr expr source valueRun valueLive statementsGenerated
          rw [sameEnv] at extract
          exact extract valueAmbient allowed
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

end Goose.Lower.Validation
