import Goose.Lower.Validation.CfgFinishCompletion

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem fork_complete {state : LS} {source : BlockId} (current : state.cur = some source)
    (openBefore : CurrentOpen state) (shaped : ShapedBlocks state) (condition : ValueId) (env : LEnv) :
    ShapedBlocks (fork condition env state).2 ∧
      OpenCount (fork condition env state).2 = OpenCount state + 1 := by
  let first := (newBlock [] env state).2
  let second := (newBlock [] env first).2
  let term := Term.condbr condition state.blocks.size [] (state.blocks.size + 1) []
  have secondCurrent : second.cur = some source := current
  have closed : (fork condition env state).2 = (emitTerm term env second).2 := by
    rw [fork_run condition env current, emitTerm_run term env secondCurrent]
    rfl
  have openFirst := openBefore.newBlock [] env
  have openSecond := openFirst.newBlock [] env
  have shapeFirst := shaped.newBlock [] env
  have shapeSecond := shapeFirst.newBlock [] env
  obtain ⟨shapeClosed, countClosed⟩ := (complete_emitTerm term).complete env second _ _ rfl openSecond shapeSecond
  change OpenCount (emitTerm term env second).2 + LiveCount second =
    OpenCount second + LiveCount (emitTerm term env second).2 at countClosed
  refine ⟨closed ▸ shapeClosed, ?_⟩
  rw [closed]
  have countFirst := openCount_newBlock state [] env
  have countSecond := openCount_newBlock first [] env
  have liveSecond : LiveCount second = 1 := by change LiveCount state = 1; simp [LiveCount, current]
  have liveClosed : LiveCount (emitTerm term env second).2 = 0 := by
    simp [LiveCount, emitTerm_stopped]
  change OpenCount first = OpenCount state + 1 at countFirst
  change OpenCount second = OpenCount first + 1 at countSecond
  omega

theorem scFork_complete {state : LS} {source : BlockId} (current : state.cur = some source)
    (openBefore : CurrentOpen state) (shaped : ShapedBlocks state)
    (isAnd : Bool) (value : ValueId) (env : LEnv) :
    ShapedBlocks (scFork isAnd value env state).2 ∧
      OpenCount (scFork isAnd value env state).2 = OpenCount state + 1 := by
  let first := (newBlock [] env state).2
  let second := (newBlock [.data .bool] env first).2
  let term := scTerm isAnd value state.blocks.size (state.blocks.size + 1)
  have secondCurrent : second.cur = some source := current
  have closed : (scFork isAnd value env state).2 = (emitTerm term env second).2 := by
    rw [scFork_run isAnd value env current, emitTerm_run term env secondCurrent]
    rfl
  have openFirst := openBefore.newBlock [] env
  have openSecond := openFirst.newBlock [.data .bool] env
  have shapeFirst := shaped.newBlock [] env
  have shapeSecond := shapeFirst.newBlock [.data .bool] env
  obtain ⟨shapeClosed, countClosed⟩ := (complete_emitTerm term).complete env second _ _ rfl openSecond shapeSecond
  change OpenCount (emitTerm term env second).2 + LiveCount second =
    OpenCount second + LiveCount (emitTerm term env second).2 at countClosed
  refine ⟨closed ▸ shapeClosed, ?_⟩
  rw [closed]
  have countFirst := openCount_newBlock state [] env
  have countSecond := openCount_newBlock first [.data .bool] env
  have liveSecond : LiveCount second = 1 := by change LiveCount state = 1; simp [LiveCount, current]
  have liveClosed : LiveCount (emitTerm term env second).2 = 0 := by
    simp [LiveCount, emitTerm_stopped]
  change OpenCount first = OpenCount state + 1 at countFirst
  change OpenCount second = OpenCount first + 1 at countSecond
  omega

end Goose.Lower.Validation
