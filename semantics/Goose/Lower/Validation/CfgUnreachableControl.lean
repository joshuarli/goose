import Goose.Lower.Validation.CfgUnreachableActions

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem unreachable_curBlock : UnreachableRun curBlock := by
  apply UnreachableRun.unchanged
  intros
  rw [curBlock_run]

theorem unreachable_isLive : UnreachableRun isLive := by
  apply UnreachableRun.unchanged
  intros
  rfl

theorem unreachable_whenLive (fallback : α) {action : BlockId → B α}
    (body : ∀ block, UnreachableRun (action block)) :
    UnreachableRun (whenLive fallback action) := by
  unfold whenLive
  refine UnreachableRun.bind (unreachable_curBlock) fun current => ?_
  cases current with
  | none => exact unreachable_pure fallback
  | some block => exact body block

theorem unreachable_regrowOf (owner : Option ValueId) :
    UnreachableRun (regrowOf owner) := by
  cases owner with
  | none => exact unreachable_pure false
  | some owner => exact unreachable_growOwner owner

theorem unreachable_eachSampled (regrow : Bool) (view : ValueId) :
    UnreachableRun (eachSampled regrow view) := by
  cases regrow
  · exact unreachable_emitDef _
  · exact unreachable_pure _

theorem unreachable_eachLen (regrow : Bool) (owner : Option ValueId)
    (sampled : ValueId) : UnreachableRun (eachLen regrow owner sampled) := by
  cases regrow
  · exact unreachable_pure _
  · exact unreachable_emitDef _

theorem unreachable_eachElemValue (slot : VarId) (byRef : Bool)
    (element : ValueId) : UnreachableRun (eachElemValue slot byRef element) := by
  unfold eachElemValue
  cases byRef
  · exact unreachable_emitDef _
  · refine UnreachableRun.bind (unreachable_read) fun env => ?_
    cases env.vars[slot]? with
    | none => exact unreachable_pure _
    | some declaration =>
      dsimp only
      cases declaration.ty <;> first
        | exact unreachable_pure _
        | exact unreachable_borrowTo _ _

theorem unreachable_recordValueRootRecipe (value : ValueId) (sourceScope : ScopeId) :
    UnreachableRun (recordValueRootRecipe value sourceScope) :=
  UnreachableRun.of_blocks (by intros; rw [recordValueRootRecipe_run])

theorem unreachable_fork (condition : ValueId) : UnreachableRun (fork condition) := by
  unfold fork
  refine UnreachableRun.bind (unreachable_newBlock []) fun yes => ?_
  refine UnreachableRun.bind (unreachable_newBlock []) fun no => ?_
  exact UnreachableRun.bind (unreachable_emitTerm _ (by intro h; cases h)) fun _ => unreachable_pure _

theorem unreachable_patchBrs (join : BlockId) :
    ∀ pending, UnreachableRun (patchBrs join pending)
  | [] => unreachable_pure _
  | (block, value) :: rest => by
    unfold patchBrs
    exact UnreachableRun.bind (unreachable_patchTerm block _ (by intro h; cases h)) fun _ =>
      unreachable_patchBrs join rest

theorem unreachable_patchBrs0 (join : BlockId) :
    ∀ pending, UnreachableRun (patchBrs0 join pending)
  | [] => unreachable_pure _
  | block :: rest => by
    unfold patchBrs0
    exact UnreachableRun.bind (unreachable_patchTerm block _ (by intro h; cases h)) fun _ =>
      unreachable_patchBrs0 join rest

theorem unreachable_joinValue (yes no : Option BlockId) (yesValue noValue : ValueId) :
    UnreachableRun (joinValue yes yesValue no noValue) := by
  unfold joinValue
  split
  · exact UnreachableRun.bind (unreachable_setCur none) fun _ => unreachable_pure _
  · refine UnreachableRun.bind (unreachable_valTy _) fun ty => ?_
    refine UnreachableRun.bind (unreachable_newBlock [ty]) fun pair => ?_
    refine UnreachableRun.bind (unreachable_patchBrs _ _) fun _ => ?_
    exact UnreachableRun.bind (unreachable_setCur _) fun _ => unreachable_pure _

theorem unreachable_joinArms (yes no : Option BlockId) : UnreachableRun (joinArms yes no) := by
  unfold joinArms
  split
  · exact unreachable_setCur none
  · refine UnreachableRun.bind (unreachable_newBlock []) fun pair => ?_
    exact UnreachableRun.bind (unreachable_patchBrs0 _ _) fun _ => unreachable_setCur _

theorem unreachable_ifE_core (condition : ValueId) (sourceScope : ScopeId)
    {yes no : B ValueId} (yesRun : UnreachableRun yes) (noRun : UnreachableRun no) :
    UnreachableRun (whenLive 0 fun _ => do
      let (yesBlock, noBlock) ← fork condition
      setCur (some yesBlock)
      let yesValue ← yes
      let yesEnd ← curBlock
      setCur (some noBlock)
      let noValue ← no
      let noEnd ← curBlock
      let value ← joinValue yesEnd yesValue noEnd noValue
      recordValueRootRecipe value sourceScope
      pure value) := by
  refine unreachable_whenLive _ fun _ => ?_
  refine UnreachableRun.bind (unreachable_fork condition) fun blocks => ?_
  refine UnreachableRun.bind (unreachable_setCur _) fun _ => ?_
  refine UnreachableRun.bind yesRun fun yesValue => ?_
  refine UnreachableRun.bind (unreachable_curBlock) fun yesEnd => ?_
  refine UnreachableRun.bind (unreachable_setCur _) fun _ => ?_
  refine UnreachableRun.bind noRun fun noValue => ?_
  refine UnreachableRun.bind (unreachable_curBlock) fun noEnd => ?_
  refine UnreachableRun.bind (unreachable_joinValue yesEnd noEnd yesValue noValue) fun value => ?_
  exact UnreachableRun.bind (unreachable_recordValueRootRecipe value sourceScope) fun _ =>
    unreachable_pure value

theorem unreachable_ifS_some_core (condition : ValueId)
    {yes no : B ValueId} (yesRun : UnreachableRun yes) (noRun : UnreachableRun no) :
    UnreachableRun (whenLive () fun _ => do
      let (yesBlock, noBlock) ← fork condition
      setCur (some yesBlock)
      let _ ← yes
      let yesEnd ← curBlock
      setCur (some noBlock)
      let _ ← no
      let noEnd ← curBlock
      joinArms yesEnd noEnd) := by
  refine unreachable_whenLive _ fun _ => ?_
  refine UnreachableRun.bind (unreachable_fork condition) fun blocks => ?_
  refine UnreachableRun.bind (unreachable_setCur _) fun _ => ?_
  refine UnreachableRun.bind yesRun fun yesValue => ?_
  refine UnreachableRun.bind (unreachable_curBlock) fun yesEnd => ?_
  refine UnreachableRun.bind (unreachable_setCur _) fun _ => ?_
  refine UnreachableRun.bind noRun fun noValue => ?_
  refine UnreachableRun.bind (unreachable_curBlock) fun noEnd => ?_
  exact unreachable_joinArms yesEnd noEnd

theorem unreachable_assert_core (condition : ValueId) (origin : OriginId) :
    UnreachableRun (whenLive () fun _ => do
      let (success, failure) ← fork condition
      setCur (some failure)
      emitTerm (.abort .assert (some origin))
      setCur (some success)) := by
  refine unreachable_whenLive _ fun _ => ?_
  refine UnreachableRun.bind (unreachable_fork condition) fun blocks => ?_
  refine UnreachableRun.bind (unreachable_setCur _) fun _ => ?_
  refine UnreachableRun.bind (unreachable_emitTerm _ (by intro h; cases h)) fun _ => ?_
  exact unreachable_setCur _

theorem unreachable_ifS_none_core (condition : ValueId) {yes : B ValueId}
    (yesRun : UnreachableRun yes) (_yesAdvance : AdvB yes) :
    UnreachableRun (whenLive () fun _ => do
      let (yesBlock, join) ← fork condition
      setCur (some yesBlock)
      let _ ← yes
      emitTerm (.br join [])
      setCur (some join)) := by
  refine unreachable_whenLive _ fun _ => ?_
  refine UnreachableRun.bind (unreachable_fork condition) fun pair => ?_
  refine UnreachableRun.bind (unreachable_setCur _) fun _ => ?_
  refine UnreachableRun.bind yesRun fun _ => ?_
  exact UnreachableRun.bind (unreachable_emitTerm _ (by intro h; cases h)) fun _ => unreachable_setCur _

theorem unreachable_scFork (isAnd : Bool) (value : ValueId) : UnreachableRun (scFork isAnd value) := by
  unfold scFork
  refine UnreachableRun.bind (unreachable_newBlock []) fun rhs => ?_
  refine UnreachableRun.bind (unreachable_newBlock [.data .bool]) fun join => ?_
  cases isAnd <;> exact UnreachableRun.bind (unreachable_emitTerm _ (by intro h; cases h)) fun _ => unreachable_pure _

theorem unreachable_shortCircuit (isAnd : Bool) (value : ValueId) {rhs : B ValueId}
    (rhsRun : UnreachableRun rhs) (_rhsAdvance : AdvB rhs) :
    UnreachableRun (shortCircuit isAnd value rhs) := by
  unfold shortCircuit
  refine unreachable_whenLive _ fun _ => ?_
  refine UnreachableRun.bind (unreachable_scFork isAnd value) fun blocks => ?_
  refine UnreachableRun.bind (unreachable_setCur _) fun _ => ?_
  refine UnreachableRun.bind rhsRun fun rhsValue => ?_
  refine UnreachableRun.bind (unreachable_emitTerm _ (by intro h; cases h)) fun _ => ?_
  exact UnreachableRun.bind (unreachable_setCur _) fun _ => unreachable_pure _

end Goose.Lower.Validation
