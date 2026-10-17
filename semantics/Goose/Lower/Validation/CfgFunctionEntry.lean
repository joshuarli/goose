import Goose.Lower.Validation.CfgSourceEntry
import Goose.Lower.Validation.CfgPredecessors

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem entry_finishFunction (loop : Option LoopCtx) (impl : Impl) (value : ValueId) :
    EntryRun loop (finishFunction impl value) := by
  unfold finishFunction
  apply EntryRun.bind (entry_read loop)
  intro env
  apply EntryRun.bind (entry_isLive loop)
  intro live
  cases live with
  | false => exact entry_pure loop _
  | true =>
    simp only [ite_true]
    split
    · apply entry_newBlock_then loop []
      intro sink ids env before result after run bounded targets sinkBound
      simp only [bind_eq] at run
      obtain ⟨ignored, branched, branchRun, ignored', selected, selectRun, finalRun⟩ := run
      have branchChecked := bounded.emitTerm (.br sink []) (by simpa [Term.successors]) env
      rw [branchRun] at branchChecked
      have branchBound := sinkBound
      have selectedChecked := entry_setCur loop _ env branched _ selected selectRun
        branchChecked (targets)
      have selectedBound : sink ≠ 0 := by
        exact branchBound
      have finalChecked := selectedChecked.1.emitTerm (.br sink []) (by simpa [Term.successors]) env
      rw [finalRun] at finalChecked
      exact ⟨finalChecked, selectedChecked.2⟩
    · exact entry_emitTerm loop _ (by simp [Term.successors])

theorem TargetsNonzero.initState : TargetsNonzero initState := by
  intro index body row
  simp [Goose.Lower.initState] at row

theorem entry_function_start (types : List VTy) (continuation : List ValueId → B Unit)
    (preserves : ∀ params, EntryRun none (continuation params)) (env : LEnv) :
    let action : B Unit := do
      let (entry, params) ← newBlock types
      setCur (some entry)
      continuation params
    let (_, state) := action env initState
    EntryTargets state := by
  let pair := (newBlock types env initState).1
  let initial := (newBlock types env initState).2
  let started := (setCur (some pair.1) env initial).2
  have initialTargets : EntryTargets initial :=
    ⟨by change 0 < 1; decide, TargetsNonzero.initState.newBlock types env⟩
  have startedTargets : EntryTargets started := initialTargets.setCur (some pair.1) env
  exact (preserves pair.2 env started _ _ rfl startedTargets trivial).1

theorem EntryTargets.finished {state : LS} (checked : EntryTargets state) (func : Func)
    (blocks : func.blocks = finishBlocks state.blocks) : NoEntryTargets func := by
  intro block member target successor
  rw [blocks] at member
  have mapped : ∃ body ∈ state.blocks.toList, cfgBlock body = block := by
    simpa [finishBlocks, cfgBlock] using member
  obtain ⟨body, present, same⟩ := mapped
  obtain ⟨index, row⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp present)
  apply checked.nonzero index body row target
  simpa only [same] using successor

theorem lowerImpl_noEntryTargets (module : Core.Module) (impl : Core.Impl) :
    NoEntryTargets (lowerImpl module impl) := by
  let env := lowerEnv module impl.vars impl.results.toList
  let types := impl.params.toList.map fun param => VTy.data (tyOfVar impl param.var)
  let continuation : List ValueId → B Unit := fun params => do
    let pre := (impl.params.toList.zip params).map fun (param, value) =>
      (param.var, value, (impl.vars[param.var]?.map (·.org)).getD 0)
    let value ← lowerBlock none pre false impl.body
    finishFunction impl value
  have preserves : ∀ params, EntryRun none (continuation params) := fun params =>
    EntryRun.bind (entry_lowerBlock none _ false impl.body) fun value => entry_finishFunction none impl value
  have checked := entry_function_start types continuation preserves env
  exact checked.finished (lowerImpl module impl) rfl

theorem lowerContextAt_noEntryTargets (module : Core.Module) (context : Core.Context) (impl : Core.Impl) :
    NoEntryTargets (lowerContextAt module context impl) := lowerImpl_noEntryTargets module impl

theorem lowerGlobal_noEntryTargets (module : Core.Module) (global : Core.Global) :
    NoEntryTargets (lowerGlobal module global).init := by
  let env := lowerEnv module #[] [global.ty]
  let continuation : List ValueId → B Unit := fun _ => do
    let value ← lowerExpr global.init
    emitTerm (.ret [value] (some global.org))
  have preserves : ∀ params, EntryRun none (continuation params) := fun _ =>
    EntryRun.bind (entry_lowerExpr none global.init) fun _ => entry_emitTerm none _ (by simp [Term.successors])
  have checked := entry_function_start [] continuation preserves env
  exact checked.finished (lowerGlobal module global).init rfl

theorem lowerImpl_predecessors_entry (module : Core.Module) (impl : Core.Impl) :
    (predecessors (lowerImpl module impl))[0]?.getD [] = [] :=
  predecessors_entry _ (lowerImpl_noEntryTargets module impl)

theorem lowerContextAt_predecessors_entry (module : Core.Module) (context : Core.Context) (impl : Core.Impl) :
    (predecessors (lowerContextAt module context impl))[0]?.getD [] = [] :=
  predecessors_entry _ (lowerContextAt_noEntryTargets module context impl)

theorem lowerGlobal_predecessors_entry (module : Core.Module) (global : Core.Global) :
    (predecessors (lowerGlobal module global).init)[0]?.getD [] = [] :=
  predecessors_entry _ (lowerGlobal_noEntryTargets module global)

end Goose.Lower.Validation
