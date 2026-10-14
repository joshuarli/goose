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

theorem m_bind_ok {first : M α} {next : α → M β} {st final : St} {value : β}
    (success : (first >>= next) st = .ok value final) :
    ∃ intermediate middle, first st = .ok intermediate middle ∧
      next intermediate middle = .ok value final := by
  rw [bind_apply] at success
  cases evaluated : first st with
  | stop reason middle => rw [evaluated] at success; cases success
  | ok intermediate middle =>
    rw [evaluated] at success
    exact ⟨intermediate, middle, rfl, success⟩

theorem getCell_success {fr : Frame} {id : ValueId} {st final : St} {value : RVal}
    (success : getCell fr id st = .ok value final) :
    fr.vals[id]? = some value ∧ final = st := by
  unfold getCell at success
  cases cell : fr.vals[id]? with
  | none => simp [cell, fault, M.stop] at success
  | some stored =>
    simp only [cell, pure_apply, Res.ok.injEq] at success
    exact ⟨by simp [success.1], success.2.symm⟩

theorem getVal_success {fr : Frame} {id : ValueId} {st final : St} {value : Val}
    (success : getVal fr id st = .ok value final) :
    fr.vals[id]? = some (.val value) ∧ final = st := by
  unfold getVal at success
  obtain ⟨stored, middle, read, success⟩ := m_bind_ok success
  obtain ⟨cell, rfl⟩ := getCell_success read
  cases stored with
  | view view => simp [fault, M.stop] at success
  | val stored =>
    simp only [pure_apply, Res.ok.injEq] at success
    exact ⟨success.1 ▸ cell, success.2.symm⟩

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

end Goose.Evidence
