import Goose.Lower.Validation.SummaryPreservationReturnFramesActions

namespace Goose.Lower.Validation.SummaryPreservation.ReturnFrames

open Goose.Core Goose.GIR

variable {avoid : List ValueId × Option OriginId}

theorem returnAbsent_recordReadValueRootRecipe (value : ValueId) (place : Place) :
    ReturnAbsentRun (avoid := avoid) (recordReadValueRootRecipe value place) := by
  apply ReturnAbsentRun.of_blocks
  intro le before
  cases place <;> simp only [recordReadValueRootRecipe_run] <;> first
    | rfl
    | (split <;> simp only [recordValueRootSource_run] <;> rfl)

theorem returnAbsent_curBlock : ReturnAbsentRun (avoid := avoid) curBlock := by
  apply ReturnAbsentRun.unchanged
  intros
  rw [curBlock_run]

theorem returnAbsent_isLive : ReturnAbsentRun (avoid := avoid) isLive := by
  apply ReturnAbsentRun.unchanged
  intros
  rfl

theorem returnAbsent_whenLive (fallback : α) {action : BlockId → B α}
    (body : ∀ block, ReturnAbsentRun (avoid := avoid) (action block)) :
    ReturnAbsentRun (avoid := avoid) (whenLive fallback action) := by
  unfold whenLive
  refine ReturnAbsentRun.bind (returnAbsent_curBlock) fun current => ?_
  cases current with
  | none => exact returnAbsent_pure fallback
  | some block => exact body block

theorem returnAbsent_regrowOf (owner : Option ValueId) :
    ReturnAbsentRun (avoid := avoid) (regrowOf owner) := by
  cases owner with
  | none => exact returnAbsent_pure false
  | some owner => exact returnAbsent_growOwner owner

theorem returnAbsent_eachSampled (regrow : Bool) (view : ValueId) :
    ReturnAbsentRun (avoid := avoid) (eachSampled regrow view) := by
  cases regrow
  · exact returnAbsent_emitDef _
  · exact returnAbsent_pure _

theorem returnAbsent_eachLen (regrow : Bool) (owner : Option ValueId)
    (sampled : ValueId) : ReturnAbsentRun (avoid := avoid) (eachLen regrow owner sampled) := by
  cases regrow
  · exact returnAbsent_pure _
  · exact returnAbsent_emitDef _

theorem returnAbsent_eachElemValue (slot : VarId) (byRef : Bool)
    (element : ValueId) : ReturnAbsentRun (avoid := avoid) (eachElemValue slot byRef element) := by
  unfold eachElemValue
  cases byRef
  · exact returnAbsent_emitDef _
  · refine ReturnAbsentRun.bind (returnAbsent_read) fun env => ?_
    cases env.vars[slot]? with
    | none => exact returnAbsent_pure _
    | some declaration =>
      dsimp only
      cases declaration.ty <;> first
        | exact returnAbsent_pure _
        | exact returnAbsent_borrowTo _ _

theorem returnAbsent_fork (condition : ValueId) : ReturnAbsentRun (avoid := avoid) (fork condition) := by
  unfold fork
  refine ReturnAbsentRun.bind (returnAbsent_newBlock []) fun yes => ?_
  refine ReturnAbsentRun.bind (returnAbsent_newBlock []) fun no => ?_
  exact ReturnAbsentRun.bind (returnAbsent_emitTerm _ (by intro values origin h; cases h)) fun _ => returnAbsent_pure _

theorem returnAbsent_patchBrs (join : BlockId) :
    ∀ pending, ReturnAbsentRun (avoid := avoid) (patchBrs join pending)
  | [] => returnAbsent_pure _
  | (block, value) :: rest => by
    unfold patchBrs
    exact ReturnAbsentRun.bind (returnAbsent_patchTerm block _ (by intro values origin h; cases h)) fun _ =>
      returnAbsent_patchBrs join rest

theorem returnAbsent_patchBrs0 (join : BlockId) :
    ∀ pending, ReturnAbsentRun (avoid := avoid) (patchBrs0 join pending)
  | [] => returnAbsent_pure _
  | block :: rest => by
    unfold patchBrs0
    exact ReturnAbsentRun.bind (returnAbsent_patchTerm block _ (by intro values origin h; cases h)) fun _ =>
      returnAbsent_patchBrs0 join rest

theorem returnAbsent_joinValue (yes no : Option BlockId) (yesValue noValue : ValueId) :
    ReturnAbsentRun (avoid := avoid) (joinValue yes yesValue no noValue) := by
  unfold joinValue
  split
  · exact ReturnAbsentRun.bind (returnAbsent_setCur none) fun _ => returnAbsent_pure _
  · refine ReturnAbsentRun.bind (returnAbsent_valTy _) fun ty => ?_
    refine ReturnAbsentRun.bind (returnAbsent_newBlock [ty]) fun pair => ?_
    refine ReturnAbsentRun.bind (returnAbsent_patchBrs _ _) fun _ => ?_
    exact ReturnAbsentRun.bind (returnAbsent_setCur _) fun _ => returnAbsent_pure _

theorem returnAbsent_joinArms (yes no : Option BlockId) : ReturnAbsentRun (avoid := avoid) (joinArms yes no) := by
  unfold joinArms
  split
  · exact returnAbsent_setCur none
  · refine ReturnAbsentRun.bind (returnAbsent_newBlock []) fun pair => ?_
    exact ReturnAbsentRun.bind (returnAbsent_patchBrs0 _ _) fun _ => returnAbsent_setCur _

theorem returnAbsent_recordValueRootRecipe (value : ValueId) (sourceScope : ScopeId) :
    ReturnAbsentRun (avoid := avoid) (recordValueRootRecipe value sourceScope) := by
  apply ReturnAbsentRun.of_blocks
  intro env state
  rw [recordValueRootRecipe_run]

theorem returnAbsent_ifE_core (condition : ValueId)
    {yes no : B ValueId} (yesRun : ReturnAbsentRun (avoid := avoid) yes) (noRun : ReturnAbsentRun (avoid := avoid) no) :
    ReturnAbsentRun (avoid := avoid) (whenLive 0 fun _ => do
      let (yesBlock, noBlock) ← fork condition
      setCur (some yesBlock)
      let yesValue ← yes
      let yesEnd ← curBlock
      setCur (some noBlock)
      let noValue ← no
      let noEnd ← curBlock
      joinValue yesEnd yesValue noEnd noValue) := by
  refine returnAbsent_whenLive _ fun _ => ?_
  refine ReturnAbsentRun.bind (returnAbsent_fork condition) fun blocks => ?_
  refine ReturnAbsentRun.bind (returnAbsent_setCur _) fun _ => ?_
  refine ReturnAbsentRun.bind yesRun fun yesValue => ?_
  refine ReturnAbsentRun.bind (returnAbsent_curBlock) fun yesEnd => ?_
  refine ReturnAbsentRun.bind (returnAbsent_setCur _) fun _ => ?_
  refine ReturnAbsentRun.bind noRun fun noValue => ?_
  refine ReturnAbsentRun.bind (returnAbsent_curBlock) fun noEnd => ?_
  exact returnAbsent_joinValue yesEnd noEnd yesValue noValue

theorem returnAbsent_ifE_recorded_core (condition : ValueId) (sourceScope : ScopeId)
    {yes no : B ValueId} (yesRun : ReturnAbsentRun (avoid := avoid) yes) (noRun : ReturnAbsentRun (avoid := avoid) no) :
    ReturnAbsentRun (avoid := avoid) (whenLive 0 fun _ => do
      let (yesBlock, noBlock) ← fork condition
      setCur (some yesBlock)
      let yesValue ← yes
      let yesEnd ← curBlock
      setCur (some noBlock)
      let noValue ← no
      let noEnd ← curBlock
      let value ← joinValue yesEnd yesValue noEnd noValue
      recordValueRootRecipe value sourceScope
      Pure.pure value) := by
  refine returnAbsent_whenLive _ fun _ => ?_
  refine ReturnAbsentRun.bind (returnAbsent_fork condition) fun blocks => ?_
  refine ReturnAbsentRun.bind (returnAbsent_setCur _) fun _ => ?_
  refine ReturnAbsentRun.bind yesRun fun yesValue => ?_
  refine ReturnAbsentRun.bind (returnAbsent_curBlock) fun yesEnd => ?_
  refine ReturnAbsentRun.bind (returnAbsent_setCur _) fun _ => ?_
  refine ReturnAbsentRun.bind noRun fun noValue => ?_
  refine ReturnAbsentRun.bind (returnAbsent_curBlock) fun noEnd => ?_
  refine ReturnAbsentRun.bind (returnAbsent_joinValue yesEnd noEnd yesValue noValue) fun value => ?_
  exact ReturnAbsentRun.bind (returnAbsent_recordValueRootRecipe value sourceScope) fun _ => returnAbsent_pure value

theorem returnAbsent_ifS_some_core (condition : ValueId)
    {yes no : B ValueId} (yesRun : ReturnAbsentRun (avoid := avoid) yes) (noRun : ReturnAbsentRun (avoid := avoid) no) :
    ReturnAbsentRun (avoid := avoid) (whenLive () fun _ => do
      let (yesBlock, noBlock) ← fork condition
      setCur (some yesBlock)
      let _ ← yes
      let yesEnd ← curBlock
      setCur (some noBlock)
      let _ ← no
      let noEnd ← curBlock
      joinArms yesEnd noEnd) := by
  refine returnAbsent_whenLive _ fun _ => ?_
  refine ReturnAbsentRun.bind (returnAbsent_fork condition) fun blocks => ?_
  refine ReturnAbsentRun.bind (returnAbsent_setCur _) fun _ => ?_
  refine ReturnAbsentRun.bind yesRun fun yesValue => ?_
  refine ReturnAbsentRun.bind (returnAbsent_curBlock) fun yesEnd => ?_
  refine ReturnAbsentRun.bind (returnAbsent_setCur _) fun _ => ?_
  refine ReturnAbsentRun.bind noRun fun noValue => ?_
  refine ReturnAbsentRun.bind (returnAbsent_curBlock) fun noEnd => ?_
  exact returnAbsent_joinArms yesEnd noEnd

theorem returnAbsent_assert_core (condition : ValueId) (origin : OriginId) :
    ReturnAbsentRun (avoid := avoid) (whenLive () fun _ => do
      let (success, failure) ← fork condition
      setCur (some failure)
      emitTerm (.abort .assert (some origin))
      setCur (some success)) := by
  refine returnAbsent_whenLive _ fun _ => ?_
  refine ReturnAbsentRun.bind (returnAbsent_fork condition) fun blocks => ?_
  refine ReturnAbsentRun.bind (returnAbsent_setCur _) fun _ => ?_
  refine ReturnAbsentRun.bind (returnAbsent_emitTerm _ (by intro values origin h; cases h)) fun _ => ?_
  exact returnAbsent_setCur _

theorem returnAbsent_ifS_none_core (condition : ValueId) {yes : B ValueId}
    (yesRun : ReturnAbsentRun (avoid := avoid) yes) (_yesAdvance : AdvB yes) :
    ReturnAbsentRun (avoid := avoid) (whenLive () fun _ => do
      let (yesBlock, join) ← fork condition
      setCur (some yesBlock)
      let _ ← yes
      emitTerm (.br join [])
      setCur (some join)) := by
  refine returnAbsent_whenLive _ fun _ => ?_
  refine ReturnAbsentRun.bind (returnAbsent_fork condition) fun pair => ?_
  refine ReturnAbsentRun.bind (returnAbsent_setCur _) fun _ => ?_
  refine ReturnAbsentRun.bind yesRun fun _ => ?_
  exact ReturnAbsentRun.bind (returnAbsent_emitTerm _ (by intro values origin h; cases h)) fun _ => returnAbsent_setCur _

theorem returnAbsent_scFork (isAnd : Bool) (value : ValueId) : ReturnAbsentRun (avoid := avoid) (scFork isAnd value) := by
  unfold scFork
  refine ReturnAbsentRun.bind (returnAbsent_newBlock []) fun rhs => ?_
  refine ReturnAbsentRun.bind (returnAbsent_newBlock [.data .bool]) fun join => ?_
  cases isAnd <;> exact ReturnAbsentRun.bind (returnAbsent_emitTerm _ (by intro values origin h; cases h)) fun _ => returnAbsent_pure _

theorem returnAbsent_shortCircuit (isAnd : Bool) (value : ValueId) {rhs : B ValueId}
    (rhsRun : ReturnAbsentRun (avoid := avoid) rhs) (_rhsAdvance : AdvB rhs) :
    ReturnAbsentRun (avoid := avoid) (shortCircuit isAnd value rhs) := by
  unfold shortCircuit
  refine returnAbsent_whenLive _ fun _ => ?_
  refine ReturnAbsentRun.bind (returnAbsent_scFork isAnd value) fun blocks => ?_
  refine ReturnAbsentRun.bind (returnAbsent_setCur _) fun _ => ?_
  refine ReturnAbsentRun.bind rhsRun fun rhsValue => ?_
  refine ReturnAbsentRun.bind (returnAbsent_emitTerm _ (by intro values origin h; cases h)) fun _ => ?_
  exact ReturnAbsentRun.bind (returnAbsent_setCur _) fun _ => returnAbsent_pure _

end Goose.Lower.Validation.SummaryPreservation.ReturnFrames
