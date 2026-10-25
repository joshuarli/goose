import Goose.Lower.Validation.CfgSourceCompletion

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem completion_function_start (types : List VTy) (continuation : List ValueId → B Unit)
    (preserves : ∀ params, CompletionAction (continuation params))
    (stops : ∀ params env state, (continuation params env state).2.cur = none) (env : LEnv) :
    let action : B Unit := do
      let (entry, params) ← newBlock types
      setCur (some entry)
      continuation params
    let (_, state) := action env initState
    AllClosed state := by
  let pair := (newBlock types env initState).1
  let initial := (newBlock types env initState).2
  let started := (setCur (some pair.1) env initial).2
  have initialShape : ShapedBlocks initState := by
    intro block body row
    simp [initState] at row
  have shapeStarted := (initialShape.newBlock types env).setCur (some pair.1) env
  have fresh := newBlock_open initState env types
  obtain ⟨body, row, openBody⟩ := fresh
  have initialRow : initial.blocks[pair.1]? = some body := row
  have openStarted := CurrentOpen.setCur initialRow openBody env
  have countInitial : OpenCount initial = 1 := by
    have count := openCount_newBlock initState types env
    change OpenCount initial = OpenCount initState + 1 at count
    simpa only [show OpenCount initState = 0 from rfl, Nat.zero_add] using count
  have countStarted : OpenCount started = LiveCount started := by
    change OpenCount initial = 1
    exact countInitial
  exact (preserves pair.2).closed rfl openStarted shapeStarted countStarted (stops pair.2 env started)

theorem AllClosed.finished {state : LS} (closed : AllClosed state) (func : Func)
    (blocks : func.blocks = finishBlocks state.blocks) :
    ∀ block ∈ func.blocks.toList, block.terms.length = 1 ∧ block.lastTerm?.isSome = true := by
  intro block member
  rw [blocks] at member
  have mapped : ∃ body ∈ state.blocks.toList, cfgBlock body = block := by
    simpa [finishBlocks, cfgBlock] using member
  obtain ⟨body, present, same⟩ := mapped
  rw [← same]
  exact allClosed_blocks closed body present

theorem lowerImpl_terminators (module : Core.Module) (impl : Core.Impl) :
    ∀ block ∈ (lowerImpl module impl).blocks.toList,
      block.terms.length = 1 ∧ block.lastTerm?.isSome = true := by
  let env := lowerEnv module impl.vars impl.results.toList
  let types := impl.params.toList.map fun param => VTy.data (tyOfVar impl param.var)
  let continuation : List ValueId → B Unit := fun params => do
    let pre := (impl.params.toList.zip params).map fun (param, value) =>
      (param.var, value, (impl.vars[param.var]?.map (·.org)).getD 0)
    let value ← lowerBlock none pre false impl.body
    finishFunction impl value
  have actionComplete : ∀ params, CompletionAction (continuation params) := fun params =>
    CompletionAction.bind (complete_lowerBlock none _ false impl.body) fun value => complete_finishFunction impl value
  have actionStops : ∀ params env state, (continuation params env state).2.cur = none := by
    intro params env state
    simp only [continuation, bind_run]
    exact finishFunction_stopped _ _ _ _
  have closed := completion_function_start types continuation actionComplete actionStops env
  exact closed.finished (lowerImpl module impl) rfl

theorem lowerContextAt_terminators (module : Core.Module) (context : Core.Context) (impl : Core.Impl) :
    ∀ block ∈ (lowerContextAt module context impl).blocks.toList,
      block.terms.length = 1 ∧ block.lastTerm?.isSome = true :=
  lowerImpl_terminators module impl

theorem lowerGlobal_terminators (module : Core.Module) (global : Core.Global) :
    ∀ block ∈ (lowerGlobal module global).init.blocks.toList,
      block.terms.length = 1 ∧ block.lastTerm?.isSome = true := by
  let env := lowerEnv module #[] [global.ty]
  let continuation : List ValueId → B Unit := fun _ => do
    let value ← lowerExpr global.init
    emitTerm (.ret [value] (some global.org))
  have actionComplete : ∀ params, CompletionAction (continuation params) := fun _ =>
    CompletionAction.bind (complete_lowerExpr global.init) fun _ => complete_emitTerm _
  have actionStops : ∀ params env state, (continuation params env state).2.cur = none := by
    intro params env state
    simp only [continuation, bind_run]
    exact emitTerm_stopped _ _ _
  have closed := completion_function_start [] continuation actionComplete actionStops env
  exact closed.finished (lowerGlobal module global).init rfl

end Goose.Lower.Validation
