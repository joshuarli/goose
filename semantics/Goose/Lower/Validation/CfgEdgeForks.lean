import Goose.Lower.Validation.CfgEdgeActions

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem edge_newBlock0_target {env : LEnv} {before after : LS} {result : BlockId × List ValueId}
    (run : newBlock [] env before = (result, after)) : EdgeArguments after result.1 [] := by
  rw [newBlock0_run] at run
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
  exact edgeArguments_newBlock0 env before

theorem edge_newBlock1_target {env : LEnv} {before after : LS} {result : BlockId × List ValueId}
    {ty : VTy} {value : ValueId} (run : newBlock [ty] env before = (result, after))
    (typed : before.vals[value]? = some (some ty)) : EdgeArguments after result.1 [value] := by
  rw [newBlock1_run] at run
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
  exact edgeArguments_newBlock1 typed env

theorem edge_fork (condition : ValueId) : EdgeRun (fork condition) := by
  intro env before result after run checked
  simp only [fork, bind_eq] at run
  obtain ⟨⟨yes, yesParams⟩, first, yesRun, ⟨no, noParams⟩, second, noRun,
    ignored, closed, termRun, finished⟩ := run
  rw [pure_run] at finished
  obtain ⟨_, rfl⟩ := Prod.mk.inj finished
  obtain ⟨firstExtension, firstChecked⟩ := edge_newBlock0 env before _ first yesRun checked
  obtain ⟨secondExtension, secondChecked⟩ := edge_newBlock0 env first _ second noRun firstChecked
  have yesEdge := (edge_newBlock0_target yesRun).extend secondExtension
  have noEdge := edge_newBlock0_target noRun
  obtain ⟨lastExtension, lastChecked⟩ := edge_emitTerm_at (.condbr condition yes [] no [])
    env second closed ignored termRun secondChecked (fun _ => ⟨yesEdge, noEdge⟩)
  exact ⟨firstExtension.trans (secondExtension.trans lastExtension), lastChecked⟩

theorem edge_scFork_at (isAnd : Bool) (value : ValueId) (env : LEnv) (before after : LS)
    (result : BlockId × BlockId × ValueId) (run : scFork isAnd value env before = (result, after))
    (checked : BuilderEdgeArguments before) (typed : before.vals[value]? = some (some (.data .bool))) :
    EdgeExtension before after ∧ BuilderEdgeArguments after := by
  have expression : scFork isAnd value = (do
      let (rhs, _) ← newBlock []
      let (join, parameters) ← newBlock [.data .bool]
      emitTerm (if isAnd then .condbr value rhs [] join [value] else .condbr value join [value] rhs [])
      pure (rhs, join, parameters.headD 0)) := by cases isAnd <;> rfl
  rw [expression] at run
  simp only [bind_eq] at run
  obtain ⟨⟨rhs, rhsParams⟩, first, rhsRun, ⟨join, joinParams⟩, second, joinRun,
    ignored, closed, termRun, finished⟩ := run
  rw [pure_run] at finished
  obtain ⟨_, rfl⟩ := Prod.mk.inj finished
  obtain ⟨firstExtension, firstChecked⟩ := edge_newBlock0 env before _ first rhsRun checked
  obtain ⟨secondExtension, secondChecked⟩ := edge_newBlock1 (.data .bool) env first _ second joinRun firstChecked
  have rhsEdge := (edge_newBlock0_target rhsRun).extend secondExtension
  have joinEdge := edge_newBlock1_target joinRun (firstExtension.types value (.data .bool) typed)
  have arguments : BuilderTermArguments second
      (if isAnd then .condbr value rhs [] join [value] else .condbr value join [value] rhs []) := by
    cases isAnd
    · exact ⟨joinEdge, rhsEdge⟩
    · exact ⟨rhsEdge, joinEdge⟩
  obtain ⟨lastExtension, lastChecked⟩ := edge_emitTerm_at _ env second closed ignored termRun secondChecked (fun _ => arguments)
  exact ⟨firstExtension.trans (secondExtension.trans lastExtension), lastChecked⟩

end Goose.Lower.Validation
