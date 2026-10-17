import Goose.Lower.Validation.CfgCompleteControl

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem complete_ifE (condition : ValueId) (sourceScope : ScopeId) {thenAction elseAction : B ValueId}
    (thenChild : CompletionAction thenAction) (elseChild : CompletionAction elseAction) :
    CompletionAction (whenLive 0 fun _ => do
      let (thenBlock, elseBlock) ← fork condition
      setCur (some thenBlock)
      let thenValue ← thenAction
      let endThen ← curBlock
      setCur (some elseBlock)
      let elseValue ← elseAction
      let endElse ← curBlock
      let result ← joinValue endThen thenValue endElse elseValue
      recordValueRootRecipe result sourceScope
      pure result) := by
  refine ⟨⟨advB_ifE_core condition sourceScope thenChild.openAction.advance elseChild.openAction.advance,
    opens_ifE_core condition sourceScope thenChild.openAction.advance elseChild.openAction.advance⟩, ?_⟩
  intro env before result after run openBefore shapedBefore
  cases current : before.cur with
  | none =>
    rw [whenLive_none _ _ env current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact ⟨shapedBefore, rfl⟩
  | some source =>
    rw [whenLive_some _ _ env current] at run
    simp only [bind_eq] at run
    obtain ⟨⟨thenBlock, elseBlock⟩, forked, forkRun, _, thenStart, thenStartRun,
      thenValue, thenEnd, thenRun, endThen, thenRead, thenReadRun,
      _, elseStart, elseStartRun, elseValue, elseEnd, elseRun,
      endElse, elseRead, elseReadRun, joinedValue, joinedState, joinRun,
      _, recordedState, recipeRun, finalRun⟩ := run
    obtain ⟨thenCurrent, thenSame⟩ := curBlock_eq thenReadRun
    obtain ⟨elseCurrent, elseSame⟩ := curBlock_eq elseReadRun
    subst thenRead
    subst elseRead
    have targets := fork_open_targets current (openBefore.bound source current) condition env
    rw [forkRun] at targets
    obtain ⟨thenBody, thenRow, thenOpen⟩ := targets.1
    obtain ⟨elseBody, elseRow, elseOpen⟩ := targets.2
    have openThenStart := CurrentOpen.setCur thenRow thenOpen env
    rw [thenStartRun] at openThenStart
    have distinct := fork_distinct current forkRun
    have different : thenStart.cur ≠ some elseBlock := by
      rw [setCur_current thenStartRun]
      exact fun equality => distinct (Option.some.inj equality)
    have elseRowStarted : thenStart.blocks[elseBlock]? = some elseBody := by
      simpa only [setCur_blocks thenStartRun] using elseRow
    have thenAdvance := thenChild.openAction.advance env thenStart thenValue thenEnd thenRun
    have openElseStart := restore_currentOpen elseRowStarted elseOpen different thenAdvance elseStartRun
    have openThenEnd := thenChild.openAction.paths env thenStart thenValue thenEnd thenRun
      openThenStart openThenStart.bound
    have openElseEnd := elseChild.openAction.paths env elseStart elseValue elseEnd elseRun
      openElseStart openElseStart.bound
    have elseAdvance := elseChild.openAction.advance env elseStart elseValue elseEnd elseRun
    have savedThen : ∀ block, endThen = some block →
        ∃ body, elseEnd.blocks[block]? = some body ∧ OpenBlock body := by
      intro block present
      obtain ⟨body, row, bodyOpen⟩ := openThenEnd block (thenCurrent.symm.trans present)
      have elseBound : elseBlock < thenStart.blocks.size := (Array.getElem?_eq_some_iff.mp elseRowStarted).1
      have endDifferent := adv_current_ne_old thenAdvance elseBound different
      have notSame : block ≠ elseBlock := by
        intro same
        apply endDifferent
        exact thenCurrent.symm.trans (present.trans (congrArg some same))
      have beforeDifferent : elseStart.cur ≠ some block := by
        rw [setCur_current elseStartRun]
        exact fun equality => notSame (Option.some.inj equality).symm
      have rowStarted : elseStart.blocks[block]? = some body := by
        simpa only [setCur_blocks elseStartRun] using row
      exact ⟨body, elseAdvance.keep block body beforeDifferent rowStarted, bodyOpen⟩
    have endpointsDistinct : ∀ block, endThen = some block → endElse ≠ some block := by
      intro block present
      obtain ⟨body, row, _⟩ := openThenEnd block (thenCurrent.symm.trans present)
      have elseBound : elseBlock < thenStart.blocks.size := (Array.getElem?_eq_some_iff.mp elseRowStarted).1
      have endDifferent := adv_current_ne_old thenAdvance elseBound different
      have beforeDifferent : elseStart.cur ≠ some block := by
        rw [setCur_current elseStartRun]
        intro equality
        apply endDifferent
        exact thenCurrent.symm.trans (present.trans equality.symm)
      have bound : block < elseStart.blocks.size := by
        rw [setCur_blocks elseStartRun]
        exact (Array.getElem?_eq_some_iff.mp row).1
      intro same
      exact adv_current_ne_old elseAdvance bound beforeDifferent (elseCurrent.symm.trans same)
    have unique : (((endThen.map (·, thenValue)).toList ++
        (endElse.map (·, elseValue)).toList).map Prod.fst).Nodup := by
      cases endThen with
      | none => cases endElse <;> simp
      | some block =>
        cases endElse with
        | none => simp
        | some other =>
          have unequal : other ≠ block := fun same =>
            endpointsDistinct block rfl (congrArg some same)
          simp [Ne.symm unequal]
    have incomingOpen : ∀ pair ∈ (endThen.map (·, thenValue)).toList ++
        (endElse.map (·, elseValue)).toList,
        ∃ body, elseEnd.blocks[pair.1]? = some body ∧ OpenBlock body := by
      intro pair member
      rcases List.mem_append.mp member with member | member
      · cases endThen with
        | none => simp at member
        | some block =>
          simp only [Option.map_some, Option.toList_some, List.mem_singleton] at member
          subst pair
          exact savedThen block rfl
      · cases endElse with
        | none => simp at member
        | some block =>
          simp only [Option.map_some, Option.toList_some, List.mem_singleton] at member
          subst pair
          exact openElseEnd block elseCurrent.symm
    obtain ⟨shapeFork, countFork⟩ := fork_complete current openBefore shapedBefore condition env
    rw [forkRun] at shapeFork countFork
    have shapeThenStart := shapeFork.of_blocks (setCur_blocks thenStartRun)
    obtain ⟨shapeThenEnd, countThen⟩ := thenChild.complete env thenStart thenValue thenEnd thenRun
      openThenStart shapeThenStart
    have shapeElseStart := shapeThenEnd.of_blocks (setCur_blocks elseStartRun)
    obtain ⟨shapeElseEnd, countElse⟩ := elseChild.complete env elseStart elseValue elseEnd elseRun
      openElseStart shapeElseStart
    obtain ⟨shapeJoin, countJoin⟩ := joinValue_complete endThen endElse thenValue elseValue env elseEnd
      shapeElseEnd unique incomingOpen
    rw [joinRun] at shapeJoin countJoin
    rw [recordValueRootRecipe_run] at recipeRun
    have recipeStateEq :
        { joinedState with valueRootRecipes :=
          if joinedState.cur.isSome && (match joinedState.vals[joinedValue]?.join with
            | some (.data type) => type.isRefLike
            | some (.view ..) => true
            | none => false)
          then joinedState.valueRootRecipes.push (joinedValue, sourceScope)
          else joinedState.valueRootRecipes } = recordedState := (Prod.mk.inj recipeRun).2
    have recipeBlocks : recordedState.blocks = joinedState.blocks := by
      have same := congrArg LS.blocks recipeStateEq
      simpa using same.symm
    have recipeCurrent : recordedState.cur = joinedState.cur := by
      have same := congrArg LS.cur recipeStateEq
      simpa using same.symm
    have afterStateEq : after = recordedState := (pure_eq.mp finalRun).2.symm
    have afterBlocks : after.blocks = joinedState.blocks := by
      exact (congrArg LS.blocks afterStateEq).trans recipeBlocks
    refine ⟨shapeJoin.of_blocks afterBlocks, ?_⟩
    have afterOpenCount : OpenCount after = OpenCount joinedState := by
      unfold OpenCount
      rw [afterBlocks]
    have afterLiveCount : LiveCount after = LiveCount joinedState := by
      unfold LiveCount
      rw [afterStateEq, recipeCurrent]
    have countThenStart : OpenCount thenStart = OpenCount forked := by simp only [OpenCount, setCur_blocks thenStartRun]
    have countElseStart : OpenCount elseStart = OpenCount thenEnd := by simp only [OpenCount, setCur_blocks elseStartRun]
    have liveBefore : LiveCount before = 1 := by simp [LiveCount, current]
    have liveThenStart : LiveCount thenStart = 1 := by simp [LiveCount, setCur_current thenStartRun]
    have liveElseStart : LiveCount elseStart = 1 := by simp [LiveCount, setCur_current elseStartRun]
    have liveThenEnd : LiveCount thenEnd = endThen.toList.length := by
      simp only [LiveCount, ← thenCurrent]
      cases endThen <;> rfl
    have liveElseEnd : LiveCount elseEnd = endElse.toList.length := by
      simp only [LiveCount, ← elseCurrent]
      cases endElse <;> rfl
    rw [afterOpenCount, afterLiveCount]
    dsimp only at countFork countJoin
    omega

theorem complete_ifS_some (condition : ValueId) {thenAction elseAction : B ValueId}
    (thenChild : CompletionAction thenAction) (elseChild : CompletionAction elseAction) :
    CompletionAction (whenLive () fun _ => do
      let (thenBlock, elseBlock) ← fork condition
      setCur (some thenBlock)
      let _ ← thenAction
      let endThen ← curBlock
      setCur (some elseBlock)
      let _ ← elseAction
      let endElse ← curBlock
      joinArms endThen endElse) := by
  refine ⟨⟨advB_ifS_some_core condition thenChild.openAction.advance elseChild.openAction.advance,
    opens_ifS_some_core condition thenChild.openAction.advance elseChild.openAction.advance⟩, ?_⟩
  intro env before result after run openBefore shapedBefore
  cases current : before.cur with
  | none =>
    rw [whenLive_none _ _ env current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact ⟨shapedBefore, rfl⟩
  | some source =>
    rw [whenLive_some _ _ env current] at run
    simp only [bind_eq] at run
    obtain ⟨⟨thenBlock, elseBlock⟩, forked, forkRun, _, thenStart, thenStartRun,
      thenValue, thenEnd, thenRun, endThen, thenRead, thenReadRun,
      _, elseStart, elseStartRun, elseValue, elseEnd, elseRun,
      endElse, elseRead, elseReadRun, joinRun⟩ := run
    obtain ⟨thenCurrent, thenSame⟩ := curBlock_eq thenReadRun
    obtain ⟨elseCurrent, elseSame⟩ := curBlock_eq elseReadRun
    subst thenRead
    subst elseRead
    have targets := fork_open_targets current (openBefore.bound source current) condition env
    rw [forkRun] at targets
    obtain ⟨thenBody, thenRow, thenOpen⟩ := targets.1
    obtain ⟨elseBody, elseRow, elseOpen⟩ := targets.2
    have openThenStart := CurrentOpen.setCur thenRow thenOpen env
    rw [thenStartRun] at openThenStart
    have distinct := fork_distinct current forkRun
    have different : thenStart.cur ≠ some elseBlock := by
      rw [setCur_current thenStartRun]
      exact fun equality => distinct (Option.some.inj equality)
    have elseRowStarted : thenStart.blocks[elseBlock]? = some elseBody := by
      simpa only [setCur_blocks thenStartRun] using elseRow
    have thenAdvance := thenChild.openAction.advance env thenStart thenValue thenEnd thenRun
    have openElseStart := restore_currentOpen elseRowStarted elseOpen different thenAdvance elseStartRun
    have openThenEnd := thenChild.openAction.paths env thenStart thenValue thenEnd thenRun
      openThenStart openThenStart.bound
    have openElseEnd := elseChild.openAction.paths env elseStart elseValue elseEnd elseRun
      openElseStart openElseStart.bound
    have elseAdvance := elseChild.openAction.advance env elseStart elseValue elseEnd elseRun
    have savedThen : ∀ block, endThen = some block →
        ∃ body, elseEnd.blocks[block]? = some body ∧ OpenBlock body := by
      intro block present
      obtain ⟨body, row, bodyOpen⟩ := openThenEnd block (thenCurrent.symm.trans present)
      have elseBound : elseBlock < thenStart.blocks.size := (Array.getElem?_eq_some_iff.mp elseRowStarted).1
      have endDifferent := adv_current_ne_old thenAdvance elseBound different
      have notSame : block ≠ elseBlock := by
        intro same
        apply endDifferent
        exact thenCurrent.symm.trans (present.trans (congrArg some same))
      have beforeDifferent : elseStart.cur ≠ some block := by
        rw [setCur_current elseStartRun]
        exact fun equality => notSame (Option.some.inj equality).symm
      have rowStarted : elseStart.blocks[block]? = some body := by
        simpa only [setCur_blocks elseStartRun] using row
      exact ⟨body, elseAdvance.keep block body beforeDifferent rowStarted, bodyOpen⟩
    have endpointsDistinct : ∀ block, endThen = some block → endElse ≠ some block := by
      intro block present
      obtain ⟨body, row, _⟩ := openThenEnd block (thenCurrent.symm.trans present)
      have elseBound : elseBlock < thenStart.blocks.size := (Array.getElem?_eq_some_iff.mp elseRowStarted).1
      have endDifferent := adv_current_ne_old thenAdvance elseBound different
      have beforeDifferent : elseStart.cur ≠ some block := by
        rw [setCur_current elseStartRun]
        intro equality
        apply endDifferent
        exact thenCurrent.symm.trans (present.trans equality.symm)
      have bound : block < elseStart.blocks.size := by
        rw [setCur_blocks elseStartRun]
        exact (Array.getElem?_eq_some_iff.mp row).1
      intro same
      exact adv_current_ne_old elseAdvance bound beforeDifferent (elseCurrent.symm.trans same)
    have unique : (endThen.toList ++ endElse.toList).Nodup := by
      cases endThen with
      | none => cases endElse <;> simp
      | some block =>
        cases endElse with
        | none => simp
        | some other =>
          have unequal : other ≠ block := fun same =>
            endpointsDistinct block rfl (congrArg some same)
          simp [Ne.symm unequal]
    have incomingOpen : ∀ pair ∈ endThen.toList ++ endElse.toList,
        ∃ body, elseEnd.blocks[pair]? = some body ∧ OpenBlock body := by
      intro pair member
      rcases List.mem_append.mp member with member | member
      · cases endThen with
        | none => simp at member
        | some block =>
          simp only [Option.toList_some, List.mem_singleton] at member
          subst pair
          exact savedThen block rfl
      · cases endElse with
        | none => simp at member
        | some block =>
          simp only [Option.toList_some, List.mem_singleton] at member
          subst pair
          exact openElseEnd block elseCurrent.symm
    obtain ⟨shapeFork, countFork⟩ := fork_complete current openBefore shapedBefore condition env
    rw [forkRun] at shapeFork countFork
    have shapeThenStart := shapeFork.of_blocks (setCur_blocks thenStartRun)
    obtain ⟨shapeThenEnd, countThen⟩ := thenChild.complete env thenStart thenValue thenEnd thenRun
      openThenStart shapeThenStart
    have shapeElseStart := shapeThenEnd.of_blocks (setCur_blocks elseStartRun)
    obtain ⟨shapeElseEnd, countElse⟩ := elseChild.complete env elseStart elseValue elseEnd elseRun
      openElseStart shapeElseStart
    obtain ⟨shapeJoin, countJoin⟩ := joinArms_complete endThen endElse env elseEnd
      shapeElseEnd unique incomingOpen
    rw [joinRun] at shapeJoin countJoin
    refine ⟨shapeJoin, ?_⟩
    have countThenStart : OpenCount thenStart = OpenCount forked := by simp only [OpenCount, setCur_blocks thenStartRun]
    have countElseStart : OpenCount elseStart = OpenCount thenEnd := by simp only [OpenCount, setCur_blocks elseStartRun]
    have liveBefore : LiveCount before = 1 := by simp [LiveCount, current]
    have liveThenStart : LiveCount thenStart = 1 := by simp [LiveCount, setCur_current thenStartRun]
    have liveElseStart : LiveCount elseStart = 1 := by simp [LiveCount, setCur_current elseStartRun]
    have liveThenEnd : LiveCount thenEnd = endThen.toList.length := by
      simp only [LiveCount, ← thenCurrent]
      cases endThen <;> rfl
    have liveElseEnd : LiveCount elseEnd = endElse.toList.length := by
      simp only [LiveCount, ← elseCurrent]
      cases endElse <;> rfl
    dsimp only at countFork countJoin
    omega

end Goose.Lower.Validation
