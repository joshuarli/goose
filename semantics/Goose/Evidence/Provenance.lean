import Goose.Evidence.Execution

namespace Goose.Evidence

open Goose.Core Goose.GIR

theorem findDefIn_member {value : ValueId} {insts : List Inst} {op : Op}
    (found : findDefIn value insts = some op) : Inst.def value op ∈ insts := by
  induction insts with
  | nil => simp [findDefIn] at found
  | cons instruction rest ih =>
    cases instruction with
    | «def» result operation =>
      simp only [findDefIn] at found
      split at found
      · rename_i equal
        have : result = value := by simpa using equal
        subst result
        cases found
        simp
      · exact List.mem_cons_of_mem _ (ih found)
    | eff effect => exact List.mem_cons_of_mem _ (ih found)
    | term terminator => exact List.mem_cons_of_mem _ (ih found)

theorem defOp_member {fn : Func} {value : ValueId} {op : Op}
    (found : fn.defOp? value = some op) :
    ∃ block ∈ fn.blocks, Inst.def value op ∈ block.insts := by
  have scan : ∀ blocks : List Goose.GIR.Block, Func.defOp?.blocks value blocks = some op →
      ∃ block ∈ blocks, Inst.def value op ∈ block.insts := by
    intro blocks
    induction blocks with
    | nil => simp [Func.defOp?.blocks]
    | cons block blocks ih =>
      intro found
      simp only [Func.defOp?.blocks] at found
      cases localFound : findDefIn value block.insts with
      | some operation =>
        simp only [localFound, Option.orElse_some] at found
        cases found
        exact ⟨block, by simp, findDefIn_member localFound⟩
      | none =>
        simp only [localFound, Option.orElse_none] at found
        obtain ⟨other, member, definition⟩ := ih found
        exact ⟨other, List.mem_cons_of_mem _ member, definition⟩
  obtain ⟨block, member, definition⟩ := scan fn.blocks.toList found
  exact ⟨block, Array.mem_toList_iff.mp member, definition⟩

theorem cmp_operand_types {env : TyEnv} {comparison : CmpOp} {type : IntTy}
    {left right : ValueId} {result : VTy}
    (typed : (Op.cmp comparison type left right).resultTy env = .ok result) :
    env.vals[left]? = some (some (.data (.int type))) ∧
    env.vals[right]? = some (some (.data (.int type))) := by
  unfold Op.resultTy at typed
  obtain ⟨leftType, leftTyped, typed⟩ := bind_ok typed
  obtain ⟨rightType, rightTyped, typed⟩ := bind_ok typed
  have equal : (decide (leftType = type) && decide (rightType = type)) = true := by
    by_cases equal : (decide (leftType = type) && decide (rightType = type)) = true
    · exact equal
    · simp [equal, tyErr, bind, Except.bind] at typed
  simp only [Bool.and_eq_true, decide_eq_true_eq] at equal
  obtain ⟨rfl, rfl⟩ := equal
  exact ⟨intTy_of leftTyped, intTy_of rightTyped⟩

theorem validated_cmp_operand_types {cfg : GCfg} {fn : Func} {pt : Pt}
    {fr : Frame} {st : St} {condition left right : ValueId}
    (validated : validate cfg.mod = .ok ())
    (point : RuntimePoint cfg fn pt fr st)
    (comparison : fn.defOp? condition = some (.cmp .lt .i64 left right)) :
    (fn.valueTypes cfg.mod)[left]? = some (some (.data (.int .i64))) ∧
    (fn.valueTypes cfg.mod)[right]? = some (some (.data (.int .i64))) := by
  obtain ⟨block, member, instruction⟩ := defOp_member comparison
  obtain ⟨_, definitions, _⟩ := (validate_sound cfg.mod validated).1 fn point.function_mem
  obtain ⟨result, typed, _⟩ := definitions block member condition _ instruction
  exact cmp_operand_types typed

theorem bindParams_preserves {params : List (ValueId × VTy)} {args : List RVal}
    {fr result : Frame} {st final : St} {id : ValueId}
    (unbound : id ∉ params.map Prod.fst)
    (success : bindParams fr params args st = .ok result final) :
    result.vals[id]? = fr.vals[id]? := by
  induction params generalizing args fr with
  | nil =>
    simp only [bindParams, pure_apply, Res.ok.injEq] at success
    exact success.1 ▸ rfl
  | cons param params ih =>
    cases args with
    | nil =>
      simp only [bindParams, pure_apply, Res.ok.injEq] at success
      exact success.1 ▸ rfl
    | cons arg args =>
      simp only [List.map_cons, List.mem_cons, not_or] at unbound
      simp only [bindParams, setCell_eq, pure_bind] at success
      rw [ih unbound.2 success]
      simp only [Frame.set, Std.HashMap.getElem?_insert]
      have distinct : (param.1 == id) = false := by
        apply Bool.eq_false_iff.mpr
        intro equal
        exact unbound.1 (eq_of_beq equal).symm
      simp [distinct]

theorem enterBlock_preserves {fn : Func} {fr result : Frame} {st final : St}
    {target : BlockId} {args : List RVal} {insts : List Inst} {id : ValueId}
    (unbound : ∀ block, fn.blocks[target]? = some block → id ∉ block.params.map Prod.fst)
    (success : enterBlock fn fr target args st = .ok (insts, result) final) :
    result.vals[id]? = fr.vals[id]? := by
  unfold enterBlock at success
  cases lookup : fn.blocks[target]? with
  | none => simp [lookup, fault, M.stop] at success
  | some block =>
    simp only [lookup] at success
    split at success
    · obtain ⟨bound, middle, binding, finished⟩ := m_bind_ok success
      simp only [pure_apply, Res.ok.injEq, Prod.mk.injEq] at finished
      rw [← finished.1.2]
      exact bindParams_preserves (unbound block lookup) binding
    · simp [fault, M.stop] at success

theorem execEff_preserves_cells {fn : Func} {fr result : Frame} {st final : St}
    {effect : Effect}
    (success : execEff fn fr effect st = .ok result final) : result.vals = fr.vals := by
  cases effect <;> simp only [execEff] at success
  case leave scope =>
    cases scopes : fr.scopes with
    | nil => simp [scopes, fault, M.stop] at success
    | cons top rest =>
      obtain ⟨enteredScope, scopeInstance⟩ := top
      simp only [scopes] at success
      split at success
      · obtain ⟨_, _, _, success⟩ := m_bind_ok success
        simp only [pure_apply, Res.ok.injEq] at success
        cases success.1
        rfl
      · simp [fault, M.stop] at success
  all_goals
    repeat' first
      | solve | simp [fault, M.stop, abortAtOrg, abortAt] at success
      | obtain ⟨intermediate, middle, evaluated, success⟩ := m_bind_ok success
      | split at success
      | unfold abortAtOrg at success
  all_goals
    simp only [pure_apply, Res.ok.injEq] at success
    cases success.1
    rfl

def stepWrites (fn : Func) (before after : Pt) : List ValueId :=
  match instAt fn before with
  | some (.def result _) => [result]
  | some (.term _) => ((fn.blocks[after.1]?).map fun block => block.params.map Prod.fst).getD []
  | _ => []

theorem RuntimeStep.preserves_cell {cfg : GCfg} {fn : Func} {pt pt' : Pt}
    {fr fr' : Frame} {st st' : St} {id : ValueId}
    (transition : RuntimeStep cfg fn pt fr st pt' fr' st')
    (unwritten : id ∉ stepWrites fn pt pt') : fr'.vals[id]? = fr.vals[id]? := by
  cases transition with
  | @define result op fuel value st' instruction evaluated =>
    simp only [stepWrites, instruction, List.mem_singleton] at unwritten
    simp only [Frame.set, Std.HashMap.getElem?_insert]
    have distinct : (result == id) = false := by
      apply Bool.eq_false_iff.mpr
      intro equal
      exact unwritten (eq_of_beq equal).symm
    simp [distinct]
  | effect instruction evaluated =>
    rw [execEff_preserves_cells evaluated]
  | branch instruction read entered =>
    apply enterBlock_preserves (success := entered)
    intro block lookup
    simpa [stepWrites, instruction, lookup] using unwritten
  | branchTrue instruction tested read entered =>
    apply enterBlock_preserves (success := entered)
    intro block lookup
    simpa [stepWrites, instruction, lookup] using unwritten
  | branchFalse instruction tested read entered =>
    apply enterBlock_preserves (success := entered)
    intro block lookup
    simpa [stepWrites, instruction, lookup] using unwritten

inductive RuntimeStepsAvoid (cfg : GCfg) (fn : Func) (ids : List ValueId) :
    Pt → Frame → St → Pt → Frame → St → Prop
  | refl {pt fr st} : RuntimeStepsAvoid cfg fn ids pt fr st pt fr st
  | next {pt fr st middlePt middleFrame middleState lastPt lastFrame lastState}
      (transition : RuntimeStep cfg fn pt fr st middlePt middleFrame middleState)
      (unwritten : ∀ id ∈ ids, id ∉ stepWrites fn pt middlePt)
      (rest : RuntimeStepsAvoid cfg fn ids middlePt middleFrame middleState lastPt lastFrame lastState) :
      RuntimeStepsAvoid cfg fn ids pt fr st lastPt lastFrame lastState

theorem RuntimeStepsAvoid.preserves_cell {cfg : GCfg} {fn : Func} {ids : List ValueId}
    {pt pt' : Pt} {fr fr' : Frame} {st st' : St} {id : ValueId}
    (history : RuntimeStepsAvoid cfg fn ids pt fr st pt' fr' st') (member : id ∈ ids) :
    fr'.vals[id]? = fr.vals[id]? := by
  induction history with
  | refl => rfl
  | next transition unwritten rest ih =>
    rw [ih, transition.preserves_cell (unwritten id member)]

theorem RuntimeStepsAvoid.trans {cfg : GCfg} {fn : Func} {ids : List ValueId}
    {first middle last : Pt} {firstFrame middleFrame lastFrame : Frame}
    {firstState middleState lastState : St}
    (left : RuntimeStepsAvoid cfg fn ids first firstFrame firstState middle middleFrame middleState)
    (right : RuntimeStepsAvoid cfg fn ids middle middleFrame middleState last lastFrame lastState) :
    RuntimeStepsAvoid cfg fn ids first firstFrame firstState last lastFrame lastState := by
  induction left with
  | refl => exact right
  | next transition unwritten rest ih =>
    exact .next transition unwritten (ih right)

theorem bindParams_cell_source {params : List (ValueId × VTy)} {args : List RVal}
    {fr result : Frame} {st final : St} {id : ValueId} {value : RVal}
    (success : bindParams fr params args st = .ok result final)
    (cell : result.vals[id]? = some value) :
    id ∈ params.map Prod.fst ∨ fr.vals[id]? = some value := by
  induction params generalizing args fr with
  | nil =>
    simp only [bindParams, pure_apply, Res.ok.injEq] at success
    cases success.1
    exact .inr cell
  | cons param params ih =>
    cases args with
    | nil =>
      simp only [bindParams, pure_apply, Res.ok.injEq] at success
      cases success.1
      exact .inr cell
    | cons arg args =>
      simp only [bindParams, setCell_eq, pure_bind] at success
      rcases ih success with member | previous
      · exact .inl (by simp [member])
      · by_cases equal : param.1 = id
        · exact .inl (by simp [equal])
        · right
          simpa [Frame.set, Std.HashMap.getElem?_insert, equal] using previous

theorem enterBlock_cell_source {fn : Func} {fr result : Frame} {st final : St}
    {target : BlockId} {args : List RVal} {insts : List Inst} {id : ValueId} {value : RVal}
    (success : enterBlock fn fr target args st = .ok (insts, result) final)
    (cell : result.vals[id]? = some value) :
    ∃ block, fn.blocks[target]? = some block ∧
      (id ∈ block.params.map Prod.fst ∨ fr.vals[id]? = some value) := by
  unfold enterBlock at success
  cases lookup : fn.blocks[target]? with
  | none => simp [lookup, fault, M.stop] at success
  | some block =>
    simp only [lookup] at success
    split at success
    · obtain ⟨bound, middle, binding, finished⟩ := m_bind_ok success
      simp only [pure_apply, Res.ok.injEq, Prod.mk.injEq] at finished
      rw [← finished.1.2] at cell
      exact ⟨block, rfl, bindParams_cell_source binding cell⟩
    · simp [fault, M.stop] at success

theorem FunctionEntry.cell_parameter {fn : Func} {depth : Nat} {args : List Val}
    {before : St} {fr : Frame} {after : St} {id : ValueId} {value : RVal}
    (entry : FunctionEntry fn depth args before fr after)
    (cell : fr.vals[id]? = some value) :
    ∃ block ∈ fn.blocks, id ∈ block.params.map Prod.fst := by
  obtain ⟨_, act, fresh, _, entered⟩ := entry
  obtain ⟨block, lookup, source⟩ := enterBlock_cell_source entered cell
  refine ⟨block, Array.mem_of_getElem? lookup, ?_⟩
  rcases source with parameter | impossible
  · exact parameter
  · simp only [Std.HashMap.getElem?_empty] at impossible
    cases impossible

def CellSample (cfg : GCfg) (fn : Func) (id : ValueId) (value : RVal)
    (pt : Pt) (fr : Frame) (st : St) : Prop :=
  ∃ sourcePt sourceFrame sourceState operation fuel writtenState,
    RuntimePoint cfg fn sourcePt sourceFrame sourceState ∧
    instAt fn sourcePt = some (.def id operation) ∧
    execOp fuel ⟨cfg, fn⟩ sourceFrame operation sourceState = .ok value writtenState ∧
    RuntimeStepsAvoid cfg fn [id] (sourcePt.1, sourcePt.2 + 1)
      (sourceFrame.set id value) writtenState pt fr st

theorem CellSample.extend {cfg : GCfg} {fn : Func} {id : ValueId} {value : RVal}
    {pt pt' : Pt} {fr fr' : Frame} {st st' : St}
    (sample : CellSample cfg fn id value pt fr st)
    (transition : RuntimeStep cfg fn pt fr st pt' fr' st')
    (unwritten : id ∉ stepWrites fn pt pt') : CellSample cfg fn id value pt' fr' st' := by
  obtain ⟨sourcePt, sourceFrame, sourceState, operation, fuel, writtenState,
    point, instruction, evaluated, history⟩ := sample
  refine ⟨sourcePt, sourceFrame, sourceState, operation, fuel, writtenState,
    point, instruction, evaluated, history.trans ?_⟩
  exact .next transition (by simpa using unwritten) .refl

theorem RuntimePoint.cell_source {cfg : GCfg} {fn : Func} {pt : Pt} {fr : Frame} {st : St}
    {id : ValueId} {value : RVal}
    (point : RuntimePoint cfg fn pt fr st) (cell : fr.vals[id]? = some value) :
    (∃ block ∈ fn.blocks, id ∈ block.params.map Prod.fst) ∨
      CellSample cfg fn id value pt fr st := by
  induction point generalizing id value with
  | initializer _ _ _ _ entry => exact .inl (entry.cell_parameter cell)
  | entry _ _ _ enter => exact .inl (enter.cell_parameter cell)
  | call _ _ _ _ _ enter _ => exact .inl (enter.cell_parameter cell)
  | @step fn pt fr st pt' fr' st' before transition ih =>
    cases transition with
    | @define result operation fuel computed writtenState instruction evaluated =>
      by_cases equal : result = id
      · subst result
        simp only [Frame.set, Std.HashMap.getElem?_insert, beq_self_eq_true, ↓reduceIte,
          Option.some.injEq] at cell
        subst computed
        right
        exact ⟨pt, fr, st, operation, fuel, st',
          before, instruction, evaluated, .refl⟩
      · have oldCell : fr.vals[id]? = some value := by
          simpa [Frame.set, Std.HashMap.getElem?_insert, equal] using cell
        rcases ih oldCell with parameter | sample
        · exact .inl parameter
        · right
          apply sample.extend (.define instruction evaluated)
          simpa [stepWrites, instruction] using Ne.symm equal
    | effect instruction evaluated =>
      rw [execEff_preserves_cells evaluated] at cell
      rcases ih cell with parameter | sample
      · exact .inl parameter
      · exact .inr (sample.extend (.effect instruction evaluated) (by simp [stepWrites, instruction]))
    | branch instruction read entered =>
      obtain ⟨block, lookup, source⟩ := enterBlock_cell_source entered cell
      by_cases parameter : id ∈ block.params.map Prod.fst
      · exact .inl ⟨block, Array.mem_of_getElem? lookup, parameter⟩
      · have oldCell := source.resolve_left parameter
        rcases ih oldCell with parameterSource | sample
        · exact .inl parameterSource
        · right
          apply sample.extend (.branch instruction read entered)
          simpa [stepWrites, instruction, lookup] using parameter
    | branchTrue instruction tested read entered =>
      obtain ⟨block, lookup, source⟩ := enterBlock_cell_source entered cell
      by_cases parameter : id ∈ block.params.map Prod.fst
      · exact .inl ⟨block, Array.mem_of_getElem? lookup, parameter⟩
      · have oldCell := source.resolve_left parameter
        rcases ih oldCell with parameterSource | sample
        · exact .inl parameterSource
        · right
          apply sample.extend (.branchTrue instruction tested read entered)
          simpa [stepWrites, instruction, lookup] using parameter
    | branchFalse instruction tested read entered =>
      obtain ⟨block, lookup, source⟩ := enterBlock_cell_source entered cell
      by_cases parameter : id ∈ block.params.map Prod.fst
      · exact .inl ⟨block, Array.mem_of_getElem? lookup, parameter⟩
      · have oldCell := source.resolve_left parameter
        rcases ih oldCell with parameterSource | sample
        · exact .inl parameterSource
        · right
          apply sample.extend (.branchFalse instruction tested read entered)
          simpa [stepWrites, instruction, lookup] using parameter

theorem cmp_true_cells {cfg : GCfg} {fn : Func} {fr : Frame} {st final : St}
    {left right : ValueId} {fuel : Nat}
    (evaluated : execOp fuel ⟨cfg, fn⟩ fr (.cmp .lt .i64 left right) st =
      .ok (.val (.bool true)) final) :
    ∃ leftValue rightValue comparable,
      fr.vals[left]? = some (.val leftValue) ∧
      fr.vals[right]? = some (.val rightValue) ∧
      expectComparable leftValue rightValue st = .ok comparable final ∧
      comparable.1 < comparable.2 := by
  simp only [execOp, execPure] at evaluated
  obtain ⟨leftValue, firstState, leftRead, afterLeft⟩ := m_bind_ok evaluated
  obtain ⟨rightValue, secondState, rightRead, afterRight⟩ := m_bind_ok afterLeft
  obtain ⟨comparable, middle, compared, finished⟩ := m_bind_ok afterRight
  obtain ⟨leftCell, firstStateEq⟩ := getVal_success leftRead
  obtain ⟨rightCell, secondStateEq⟩ := getVal_success rightRead
  simp only [pure_apply, Res.ok.injEq, RVal.val.injEq, Val.bool.injEq, evalCmp,
    decide_eq_true_eq] at finished
  rw [secondStateEq, firstStateEq, finished.2] at compared
  exact ⟨leftValue, rightValue, comparable, leftCell, rightCell, compared, finished.1⟩

theorem cmp_true_i64 {cfg : GCfg} {fn : Func} {fr : Frame} {st final : St}
    {left right : ValueId} {fuel : Nat} {a b : Int}
    (evaluated : execOp fuel ⟨cfg, fn⟩ fr (.cmp .lt .i64 left right) st =
      .ok (.val (.bool true)) final)
    (leftCell : fr.vals[left]? = some (.val (.int .i64 a)))
    (rightCell : fr.vals[right]? = some (.val (.int .i64 b))) : a < b := by
  obtain ⟨leftValue, rightValue, comparable, leftRead, rightRead, compared, less⟩ :=
    cmp_true_cells evaluated
  rw [leftCell] at leftRead
  rw [rightCell] at rightRead
  cases leftRead
  cases rightRead
  simp only [expectComparable, expectSameTy, ↓reduceIte, pure_bind,
    pure_apply, Res.ok.injEq] at compared
  cases compared.1
  exact less

theorem cmp_result_type {env : TyEnv} {comparison : CmpOp} {type : IntTy}
    {left right : ValueId} {result : VTy}
    (typed : (Op.cmp comparison type left right).resultTy env = .ok result) :
    result = .data .bool := by
  unfold Op.resultTy at typed
  obtain ⟨leftType, leftTyped, afterLeft⟩ := bind_ok typed
  obtain ⟨rightType, rightTyped, afterRight⟩ := bind_ok afterLeft
  split at afterRight
  · simp only [pure, Except.pure, Except.ok.injEq] at afterRight
    exact afterRight.symm
  · simp [tyErr, bind, Except.bind] at afterRight

theorem validated_cmp_distinct {cfg : GCfg} {fn : Func} {pt : Pt}
    {fr : Frame} {st : St} {condition left right : ValueId}
    (validated : validate cfg.mod = .ok ())
    (point : RuntimePoint cfg fn pt fr st)
    (comparison : fn.defOp? condition = some (.cmp .lt .i64 left right)) :
    condition ≠ left ∧ condition ≠ right := by
  obtain ⟨block, member, instruction⟩ := defOp_member comparison
  obtain ⟨_, definitions, _⟩ := (validate_sound cfg.mod validated).1 fn point.function_mem
  obtain ⟨result, typed, resultType⟩ := definitions block member condition _ instruction
  obtain ⟨leftType, rightType⟩ := cmp_operand_types typed
  rw [cmp_result_type typed] at resultType
  constructor
  · intro equal
    subst left
    rw [resultType] at leftType
    cases leftType
  · intro equal
    subst right
    rw [resultType] at rightType
    cases rightType

end Goose.Evidence
