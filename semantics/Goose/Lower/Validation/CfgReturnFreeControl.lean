import Goose.Lower.Validation.CfgReturnFreeActions

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem returnFree_curBlock : ReturnFreeRun curBlock := by
  apply ReturnFreeRun.unchanged
  intros
  rw [curBlock_run]

theorem returnFree_isLive : ReturnFreeRun isLive := by
  apply ReturnFreeRun.unchanged
  intros
  rfl

theorem returnFree_whenLive (fallback : α) {action : BlockId → B α}
    (body : ∀ block, ReturnFreeRun (action block)) :
    ReturnFreeRun (whenLive fallback action) := by
  unfold whenLive
  refine ReturnFreeRun.bind (returnFree_curBlock) fun current => ?_
  cases current with
  | none => exact returnFree_pure fallback
  | some block => exact body block

theorem returnFree_regrowOf (owner : Option ValueId) :
    ReturnFreeRun (regrowOf owner) := by
  cases owner with
  | none => exact returnFree_pure false
  | some owner => exact returnFree_growOwner owner

theorem returnFree_eachSampled (regrow : Bool) (view : ValueId) :
    ReturnFreeRun (eachSampled regrow view) := by
  cases regrow
  · exact returnFree_emitDef _
  · exact returnFree_pure _

theorem returnFree_eachLen (regrow : Bool) (owner : Option ValueId)
    (sampled : ValueId) : ReturnFreeRun (eachLen regrow owner sampled) := by
  cases regrow
  · exact returnFree_pure _
  · exact returnFree_emitDef _

theorem returnFree_eachElemValue (slot : VarId) (byRef : Bool)
    (element : ValueId) : ReturnFreeRun (eachElemValue slot byRef element) := by
  unfold eachElemValue
  cases byRef
  · exact returnFree_emitDef _
  · refine ReturnFreeRun.bind (returnFree_read) fun env => ?_
    cases env.vars[slot]? with
    | none => exact returnFree_pure _
    | some declaration =>
      dsimp only
      cases declaration.ty <;> first
        | exact returnFree_pure _
        | exact returnFree_freezeTo _ _

theorem returnFree_fork (condition : ValueId) : ReturnFreeRun (fork condition) := by
  unfold fork
  refine ReturnFreeRun.bind (returnFree_newBlock []) fun yes => ?_
  refine ReturnFreeRun.bind (returnFree_newBlock []) fun no => ?_
  exact ReturnFreeRun.bind (returnFree_emitTerm _ (by intro values origin h; cases h)) fun _ => returnFree_pure _

theorem returnFree_patchBrs (join : BlockId) :
    ∀ pending, ReturnFreeRun (patchBrs join pending)
  | [] => returnFree_pure _
  | (block, value) :: rest => by
    unfold patchBrs
    exact ReturnFreeRun.bind (returnFree_patchTerm block _ (by intro values origin h; cases h)) fun _ =>
      returnFree_patchBrs join rest

theorem returnFree_patchBrs0 (join : BlockId) :
    ∀ pending, ReturnFreeRun (patchBrs0 join pending)
  | [] => returnFree_pure _
  | block :: rest => by
    unfold patchBrs0
    exact ReturnFreeRun.bind (returnFree_patchTerm block _ (by intro values origin h; cases h)) fun _ =>
      returnFree_patchBrs0 join rest

theorem returnFree_joinValue (yes no : Option BlockId) (yesValue noValue : ValueId) :
    ReturnFreeRun (joinValue yes yesValue no noValue) := by
  unfold joinValue
  split
  · exact ReturnFreeRun.bind (returnFree_setCur none) fun _ => returnFree_pure _
  · refine ReturnFreeRun.bind (returnFree_valTy _) fun ty => ?_
    refine ReturnFreeRun.bind (returnFree_newBlock [ty]) fun pair => ?_
    refine ReturnFreeRun.bind (returnFree_patchBrs _ _) fun _ => ?_
    exact ReturnFreeRun.bind (returnFree_setCur _) fun _ => returnFree_pure _

theorem returnFree_joinArms (yes no : Option BlockId) : ReturnFreeRun (joinArms yes no) := by
  unfold joinArms
  split
  · exact returnFree_setCur none
  · refine ReturnFreeRun.bind (returnFree_newBlock []) fun pair => ?_
    exact ReturnFreeRun.bind (returnFree_patchBrs0 _ _) fun _ => returnFree_setCur _

theorem returnFree_ifE_core (condition : ValueId)
    {yes no : B ValueId} (yesRun : ReturnFreeRun yes) (noRun : ReturnFreeRun no) :
    ReturnFreeRun (whenLive 0 fun _ => do
      let (yesBlock, noBlock) ← fork condition
      setCur (some yesBlock)
      let yesValue ← yes
      let yesEnd ← curBlock
      setCur (some noBlock)
      let noValue ← no
      let noEnd ← curBlock
      joinValue yesEnd yesValue noEnd noValue) := by
  refine returnFree_whenLive _ fun _ => ?_
  refine ReturnFreeRun.bind (returnFree_fork condition) fun blocks => ?_
  refine ReturnFreeRun.bind (returnFree_setCur _) fun _ => ?_
  refine ReturnFreeRun.bind yesRun fun yesValue => ?_
  refine ReturnFreeRun.bind (returnFree_curBlock) fun yesEnd => ?_
  refine ReturnFreeRun.bind (returnFree_setCur _) fun _ => ?_
  refine ReturnFreeRun.bind noRun fun noValue => ?_
  refine ReturnFreeRun.bind (returnFree_curBlock) fun noEnd => ?_
  exact returnFree_joinValue yesEnd noEnd yesValue noValue

theorem returnFree_ifS_some_core (condition : ValueId)
    {yes no : B ValueId} (yesRun : ReturnFreeRun yes) (noRun : ReturnFreeRun no) :
    ReturnFreeRun (whenLive () fun _ => do
      let (yesBlock, noBlock) ← fork condition
      setCur (some yesBlock)
      let _ ← yes
      let yesEnd ← curBlock
      setCur (some noBlock)
      let _ ← no
      let noEnd ← curBlock
      joinArms yesEnd noEnd) := by
  refine returnFree_whenLive _ fun _ => ?_
  refine ReturnFreeRun.bind (returnFree_fork condition) fun blocks => ?_
  refine ReturnFreeRun.bind (returnFree_setCur _) fun _ => ?_
  refine ReturnFreeRun.bind yesRun fun yesValue => ?_
  refine ReturnFreeRun.bind (returnFree_curBlock) fun yesEnd => ?_
  refine ReturnFreeRun.bind (returnFree_setCur _) fun _ => ?_
  refine ReturnFreeRun.bind noRun fun noValue => ?_
  refine ReturnFreeRun.bind (returnFree_curBlock) fun noEnd => ?_
  exact returnFree_joinArms yesEnd noEnd

theorem returnFree_assert_core (condition : ValueId) (origin : OriginId) :
    ReturnFreeRun (whenLive () fun _ => do
      let (success, failure) ← fork condition
      setCur (some failure)
      emitTerm (.abort .assert (some origin))
      setCur (some success)) := by
  refine returnFree_whenLive _ fun _ => ?_
  refine ReturnFreeRun.bind (returnFree_fork condition) fun blocks => ?_
  refine ReturnFreeRun.bind (returnFree_setCur _) fun _ => ?_
  refine ReturnFreeRun.bind (returnFree_emitTerm _ (by intro values origin h; cases h)) fun _ => ?_
  exact returnFree_setCur _

theorem returnFree_ifS_none_core (condition : ValueId) {yes : B ValueId}
    (yesRun : ReturnFreeRun yes) (_yesAdvance : AdvB yes) :
    ReturnFreeRun (whenLive () fun _ => do
      let (yesBlock, join) ← fork condition
      setCur (some yesBlock)
      let _ ← yes
      emitTerm (.br join [])
      setCur (some join)) := by
  refine returnFree_whenLive _ fun _ => ?_
  refine ReturnFreeRun.bind (returnFree_fork condition) fun pair => ?_
  refine ReturnFreeRun.bind (returnFree_setCur _) fun _ => ?_
  refine ReturnFreeRun.bind yesRun fun _ => ?_
  exact ReturnFreeRun.bind (returnFree_emitTerm _ (by intro values origin h; cases h)) fun _ => returnFree_setCur _

theorem returnFree_scFork (isAnd : Bool) (value : ValueId) : ReturnFreeRun (scFork isAnd value) := by
  unfold scFork
  refine ReturnFreeRun.bind (returnFree_newBlock []) fun rhs => ?_
  refine ReturnFreeRun.bind (returnFree_newBlock [.data .bool]) fun join => ?_
  cases isAnd <;> exact ReturnFreeRun.bind (returnFree_emitTerm _ (by intro values origin h; cases h)) fun _ => returnFree_pure _

theorem returnFree_shortCircuit (isAnd : Bool) (value : ValueId) {rhs : B ValueId}
    (rhsRun : ReturnFreeRun rhs) (_rhsAdvance : AdvB rhs) :
    ReturnFreeRun (shortCircuit isAnd value rhs) := by
  unfold shortCircuit
  refine returnFree_whenLive _ fun _ => ?_
  refine ReturnFreeRun.bind (returnFree_scFork isAnd value) fun blocks => ?_
  refine ReturnFreeRun.bind (returnFree_setCur _) fun _ => ?_
  refine ReturnFreeRun.bind rhsRun fun rhsValue => ?_
  refine ReturnFreeRun.bind (returnFree_emitTerm _ (by intro values origin h; cases h)) fun _ => ?_
  exact ReturnFreeRun.bind (returnFree_setCur _) fun _ => returnFree_pure _

end Goose.Lower.Validation
