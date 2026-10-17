import Goose.Lower.GeneratedTargetsSource

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Lower.Validation

theorem generatedTargets_finishFunction (loop : Option LoopCtx) (impl : Impl) (value : ValueId) :
    GeneratedTargetRun loop (finishFunction impl value) := by
  unfold finishFunction
  apply GeneratedTargetRun.bind (generatedTargets_read loop)
  intro env
  apply GeneratedTargetRun.bind (generatedTargets_isLive loop)
  intro live
  cases live with
  | false => exact generatedTargets_pure loop _
  | true =>
    simp only [ite_true]
    split
    · apply generatedTargets_newBlock_then loop []
      intro sink ids env before result after run bounded targets sinkBound
      simp only [bind_eq] at run
      obtain ⟨ignored, branched, branchRun, ignored', selected, selectRun, finalRun⟩ := run
      have branchChecked := bounded.emitTerm (.br sink []) (by simpa [Term.successors]) env
      rw [branchRun] at branchChecked
      have branchBound := Nat.lt_of_lt_of_le sinkBound (adv_emitTerm branchRun).ext.1
      have selectedChecked := generatedTargets_setCur loop _ env branched _ selected selectRun
        branchChecked (targets.mono (adv_emitTerm branchRun).ext.1)
      have selectedBound : sink < selected.blocks.size := by
        rw [setCur_blocks selectRun]
        exact branchBound
      have finalChecked := selectedChecked.1.emitTerm (.br sink []) (by simpa [Term.successors]) env
      rw [finalRun] at finalChecked
      exact ⟨finalChecked, selectedChecked.2.mono (adv_emitTerm finalRun).ext.1⟩
    · exact generatedTargets_emitTerm loop _ (by simp [Term.successors])

theorem TargetsBounded.initState : TargetsBounded initState := by
  intro index body row
  simp [Goose.Lower.initState] at row

theorem TargetsBounded.finishBlocks {state : LS} (bounded : TargetsBounded state)
    {index : BlockId} {block : GIR.Block}
    (row : (finishBlocks state.blocks)[index]? = some block) :
    ∀ target ∈ block.terms.flatMap Term.successors, target < (finishBlocks state.blocks).size := by
  simp only [Goose.Lower.finishBlocks, Array.getElem?_map, Option.map_eq_some_iff] at row
  obtain ⟨body, bodyAt, rfl⟩ := row
  simpa only [Goose.Lower.finishBlocks, Array.size_map, cfgBlock] using bounded index body bodyAt

theorem lowerImpl_targetsBounded (module : Core.Module) (impl : Impl)
    {index : BlockId} {block : GIR.Block}
    (row : (lowerImpl module impl).blocks[index]? = some block) :
    ∀ target ∈ block.terms.flatMap Term.successors,
      target < (lowerImpl module impl).blocks.size := by
  let action : B Unit := do
    let (entry, params) ← newBlock (impl.params.toList.map fun p => .data (tyOfVar impl p.var))
    setCur (some entry)
    let pre := (impl.params.toList.zip params).map fun (p, v) =>
      (p.var, v, (impl.vars[p.var]?.map (·.org)).getD 0)
    let value ← lowerBlock none pre false impl.body
    finishFunction impl value
  have checked : GeneratedTargetRun none action := by
    apply GeneratedTargetRun.bind (generatedTargets_newBlock none _)
    intro entry
    apply GeneratedTargetRun.bind (generatedTargets_setCur none _)
    intro ignored
    apply GeneratedTargetRun.bind (generatedTargets_lowerBlock none _ false impl.body)
    intro value
    exact generatedTargets_finishFunction none impl value
  have bounded := (checked (lowerEnv module impl.vars impl.results.toList) initState _ _
    (by apply Prod.ext <;> rfl) TargetsBounded.initState trivial).1
  exact TargetsBounded.finishBlocks bounded row

theorem lowerGlobal_targetsBounded (module : Core.Module) (global : Core.Global)
    {index : BlockId} {block : GIR.Block}
    (row : (lowerGlobal module global).init.blocks[index]? = some block) :
    ∀ target ∈ block.terms.flatMap Term.successors,
      target < (lowerGlobal module global).init.blocks.size := by
  let action : B Unit := do
    let (entry, _) ← newBlock []
    setCur (some entry)
    let value ← lowerExpr global.init
    emitTerm (.ret [value] (some global.org))
  have checked : GeneratedTargetRun none action := by
    apply GeneratedTargetRun.bind (generatedTargets_newBlock none _)
    intro entry
    apply GeneratedTargetRun.bind (generatedTargets_setCur none _)
    intro ignored
    apply GeneratedTargetRun.bind (generatedTargets_lowerExpr none global.init)
    intro value
    exact generatedTargets_emitTerm none _ (by simp [Term.successors])
  have bounded := (checked (lowerEnv module #[] [global.ty]) initState _ _
    (by apply Prod.ext <;> rfl) TargetsBounded.initState trivial).1
  exact TargetsBounded.finishBlocks bounded row

end Goose.Lower
