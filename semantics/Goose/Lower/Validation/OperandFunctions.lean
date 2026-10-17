import Goose.Lower.Validation.OperandSource
import Goose.Lower.Validation.DenseDefinitions

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem value_lowerBlock_with_tail (context : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId))
    (want : Bool) (body : Core.Block) (present : body.value.isSome = true) :
    ValueRun (lowerBlock context pre want body) := by
  cases body with
  | mk scope stmts tail =>
    cases tail with
    | none => simp [Core.Block.value] at present
    | some expr =>
      simpa only [lowerBlock, lowerBlockValue] using value_lowerBlock context pre (.mk scope stmts (some expr))

theorem operands_finishFunction (impl : Impl) (value : ValueId) {le before result after}
    (run : finishFunction impl value le before = (result, after)) (checked : OperandBounds before)
    (bounded : impl.body.value.isSome = true → before.cur.isSome = true → value < before.vals.size) :
    OperandBounds after := by
  unfold finishFunction at run
  obtain ⟨env, loaded, loading, remaining⟩ := bind_eq.mp run
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj loading
  obtain ⟨live, tested, testing, run⟩ := bind_eq.mp remaining
  have test : isLive le before = (before.cur.isSome, before) := by
    simp [isLive, bind_run, curBlock_run, pure_run]
  rw [test] at testing
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj testing
  cases live : before.cur.isSome
  · simp only [live, Bool.false_eq_true, ↓reduceIte] at run
    obtain ⟨_, rfl⟩ := pure_eq.mp run
    exact checked
  · simp only [live, ↓reduceIte] at run
    by_cases sink : (!impl.results.isEmpty && impl.body.value.isNone && impl.body.diverges le.mod.noReturn) = true
    · rw [if_pos sink] at run
      obtain ⟨⟨sink, params⟩, allocated, allocation, _, closed, close, _, selected, select, term⟩ :=
        (by simpa only [bind_eq] using run)
      exact operands_emitTerm term
        (operands_setCur _ _ _ _ _ select
          (operands_emitTerm close (operands_newBlock _ _ _ _ _ allocation checked) (by simp [Term.uses])))
        (by simp [Term.uses])
    · rw [if_neg sink] at run
      apply operands_emitTerm run checked
      intro _ used member
      cases present : impl.body.value.isSome
      · simp [Term.uses, present] at member
      · have equality : used = value := by simpa [Term.uses, present] using member
        subst used
        exact bounded present live

theorem numValues_eq_state_values {state : LS} (dense : state.DenseDefinitions) {func : Func}
    (blocks : func.blocks = finishBlocks state.blocks) : func.numValues = state.vals.size := by
  rw [Func.numValues_eq_definition_count, blocks, finishBlocks_defs]
  exact dense.length

theorem operands_finishBlocks {state : LS} (checked : OperandBounds state)
    (dense : state.DenseDefinitions) {func : Func} (blocks : func.blocks = finishBlocks state.blocks) :
    ∀ block ∈ func.blocks.toList, ∀ inst ∈ block.insts, ∀ value ∈ inst.uses, value < func.numValues := by
  have count := numValues_eq_state_values dense blocks
  intro block blockMember inst instMember value member
  rw [count]
  rw [blocks, finishBlocks, Array.toList_map] at blockMember
  obtain ⟨builder, builderMember, rfl⟩ := List.mem_map.mp blockMember
  exact checked.uses inst (List.mem_flatMap.mpr ⟨builder, builderMember, instMember⟩) value member

theorem newBlock_param_bound {types : List VTy} {le before block params after}
    (run : newBlock types le before = ((block, params), after)) :
    ∀ value ∈ params, value < after.vals.size := by
  rw [newBlock_run_general] at run
  obtain ⟨pair, rfl⟩ := Prod.mk.inj run
  obtain ⟨_, rfl⟩ := Prod.mk.inj pair
  intro value member
  change value ∈ (List.range types.length).map (before.vals.size + ·) at member
  obtain ⟨index, inRange, equal⟩ := List.mem_map.mp member
  rw [← equal]
  have bound := List.mem_range.mp inRange
  simp only [array_size_pushParamTypes]
  exact Nat.add_lt_add_left bound _

theorem ordered_finishBlocks {state : LS} (checked : OperandBounds state)
    {func : Func} (blocks : func.blocks = finishBlocks state.blocks) :
    ∀ block ∈ func.blocks.toList, ∀ result op, Inst.def result op ∈ block.insts →
      ∀ value ∈ op.uses, value < result := by
  intro block blockMember result op instMember value member
  rw [blocks, finishBlocks, Array.toList_map] at blockMember
  obtain ⟨builder, builderMember, rfl⟩ := List.mem_map.mp blockMember
  exact checked.definitions result op (List.mem_flatMap.mpr ⟨builder, builderMember, instMember⟩) value member

theorem lowerImpl_operand_bounds (module : Core.Module) (impl : Impl) :
    (∀ block ∈ (lowerImpl module impl).blocks.toList, ∀ inst ∈ block.insts,
      ∀ value ∈ inst.uses, value < (lowerImpl module impl).numValues) ∧
    (∀ block ∈ (lowerImpl module impl).blocks.toList, ∀ result op, Inst.def result op ∈ block.insts →
      ∀ value ∈ op.uses, value < result) := by
  let action : B Unit := do
    let (entry, params) ← newBlock (impl.params.toList.map fun param => .data (tyOfVar impl param.var))
    setCur (some entry)
    let pre := (impl.params.toList.zip params).map fun (param, value) =>
      (param.var, value, (impl.vars[param.var]?.map (·.org)).getD 0)
    let value ← lowerBlock none pre false impl.body
    finishFunction impl value
  have preservation : OperandRun action := by
    intro le before result after run checked
    obtain ⟨⟨entry, params⟩, allocated, allocation, _, entered, entryRun,
      value, bodyState, bodyRun, finished⟩ := (by simpa only [action, bind_eq] using run)
    have allocatedBounds := operands_newBlock _ _ _ _ _ allocation checked
    have enteredBounds := operands_setCur _ _ _ _ _ entryRun allocatedBounds
    have preBound : PreOperandBounds
        ((impl.params.toList.zip params).map fun (param, value) =>
          (param.var, value, (impl.vars[param.var]?.map (·.org)).getD 0)) entered := by
      intro binding member
      obtain ⟨⟨param, value⟩, paired, rfl⟩ := List.mem_map.mp member
      have bound := newBlock_param_bound allocation value (List.of_mem_zip paired).2
      rw [setCur_run] at entryRun
      obtain ⟨_, rfl⟩ := Prod.mk.inj entryRun
      exact bound
    have bodyBounds := operands_source_lowerBlock none impl.body _ false _ _ _ _ bodyRun enteredBounds trivial preBound
    exact operands_finishFunction impl value finished bodyBounds (by
      intro present
      exact value_lowerBlock_with_tail none _ false impl.body present _ _ _ _ bodyRun)
  have density : DenseRun action := by
    intro le before result after run checked bounded
    obtain ⟨⟨entry, params⟩, allocated, allocation, _, entered, entryRun,
      value, bodyState, bodyRun, finished⟩ := (by simpa only [action, bind_eq] using run)
    have one := dense_newBlock _ le before _ allocated allocation checked bounded
    have fresh := liveBound_newBlock (impl.params.toList.map fun param => .data (tyOfVar impl param.var)) le before
    rw [allocation] at fresh
    have two := dense_setCur_at entryRun one.1 (by intro current equal; cases equal; exact fresh)
    have three := dense_lowerBlock _ _ _ _ le entered value bodyState bodyRun two.1 two.2.1
    have four := dense_finishFunction impl value le bodyState result after finished three.1 three.2.1
    exact ⟨four.1, four.2.1, Nat.le_trans one.2.2 (Nat.le_trans two.2.2 (Nat.le_trans three.2.2 four.2.2))⟩
  let output := action (lowerEnv module impl.vars impl.results.toList) initState
  have initial : OperandBounds initState := ⟨by simp [LS.insts, initState], by simp [LS.insts, initState]⟩
  have bounds := preservation _ _ output.1 output.2 rfl initial
  have dense := density _ _ output.1 output.2 rfl LS.denseDefinitions_initState liveBound_initState
  exact ⟨operands_finishBlocks bounds dense.1 rfl, ordered_finishBlocks bounds rfl⟩

theorem lowerGlobal_operand_bounds (module : Core.Module) (global : Core.Global) :
    (∀ block ∈ (lowerGlobal module global).init.blocks.toList, ∀ inst ∈ block.insts,
      ∀ value ∈ inst.uses, value < (lowerGlobal module global).init.numValues) ∧
    (∀ block ∈ (lowerGlobal module global).init.blocks.toList, ∀ result op, Inst.def result op ∈ block.insts →
      ∀ value ∈ op.uses, value < result) := by
  let action : B Unit := do
    let (entry, _) ← newBlock []
    setCur (some entry)
    let value ← lowerExpr global.init
    emitTerm (.ret [value] (some global.org))
  have preservation : OperandRun action := by
    intro le before result after run checked
    obtain ⟨⟨entry, params⟩, allocated, allocation, _, entered, entryRun,
      value, bodyState, bodyRun, finished⟩ := (by simpa only [action, bind_eq] using run)
    have allocatedBounds := operands_newBlock _ _ _ _ _ allocation checked
    have enteredBounds := operands_setCur _ _ _ _ _ entryRun allocatedBounds
    have bodyBounds := operands_source_lowerExpr global.init _ _ _ _ bodyRun enteredBounds
    exact operands_emitTerm finished bodyBounds
      (by simpa [Term.uses] using value_lowerExpr global.init _ _ _ _ bodyRun)
  have density : DenseRun action := by
    intro le before result after run checked bounded
    obtain ⟨⟨entry, params⟩, allocated, allocation, _, entered, entryRun,
      value, bodyState, bodyRun, finished⟩ := (by simpa only [action, bind_eq] using run)
    have one := dense_newBlock [] le before _ allocated allocation checked bounded
    have fresh := liveBound_newBlock [] le before
    rw [allocation] at fresh
    have two := dense_setCur_at entryRun one.1 (by intro current equal; cases equal; exact fresh)
    have three := dense_lowerExpr global.init le entered value bodyState bodyRun two.1 two.2.1
    have four := dense_emitTerm _ le bodyState result after finished three.1 three.2.1
    exact ⟨four.1, four.2.1, Nat.le_trans one.2.2 (Nat.le_trans two.2.2 (Nat.le_trans three.2.2 four.2.2))⟩
  let output := action (lowerEnv module #[] [global.ty]) initState
  have initial : OperandBounds initState := ⟨by simp [LS.insts, initState], by simp [LS.insts, initState]⟩
  have bounds := preservation _ _ output.1 output.2 rfl initial
  have dense := density _ _ output.1 output.2 rfl LS.denseDefinitions_initState liveBound_initState
  exact ⟨operands_finishBlocks bounds dense.1 rfl, ordered_finishBlocks bounds rfl⟩

theorem lowerContextAt_operand_bounds (module : Core.Module) (ctx : Context) (impl : Impl) :
    (∀ block ∈ (lowerContextAt module ctx impl).blocks.toList, ∀ inst ∈ block.insts,
      ∀ value ∈ inst.uses, value < (lowerContextAt module ctx impl).numValues) ∧
    (∀ block ∈ (lowerContextAt module ctx impl).blocks.toList, ∀ result op, Inst.def result op ∈ block.insts →
      ∀ value ∈ op.uses, value < result) := by
  exact lowerImpl_operand_bounds module impl

end Goose.Lower.Validation
