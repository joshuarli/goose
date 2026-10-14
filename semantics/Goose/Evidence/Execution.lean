import Goose.GIR.Step
import Goose.GIR.Sound

namespace Goose.Evidence

open Goose.Core Goose.GIR

def FunctionEntry (fn : Func) (depth : Nat) (args : List Val)
    (before : St) (fr : Frame) (after : St) : Prop :=
  fn.params.length = args.length ∧
  ∃ act fresh,
    freshAct before = .ok act fresh ∧
    enterBlock fn ⟨act, [], {}, depth⟩ 0 (args.map RVal.val) fresh =
      .ok (instsAt fn (0, 0), fr) after

inductive RuntimeStep (cfg : GCfg) (fn : Func) : Pt → Frame → St → Pt → Frame → St → Prop
  | define {pt fr st result op fuel value st'}
      (instruction : instAt fn pt = some (.def result op))
      (eval : execOp fuel ⟨cfg, fn⟩ fr op st = .ok value st') :
      RuntimeStep cfg fn pt fr st (pt.1, pt.2 + 1) (fr.set result value) st'
  | effect {pt fr st effect fr' st'}
      (instruction : instAt fn pt = some (.eff effect))
      (eval : execEff fn fr effect st = .ok fr' st') :
      RuntimeStep cfg fn pt fr st (pt.1, pt.2 + 1) fr' st'
  | branch {pt fr st target args values readState fr' st'}
      (instruction : instAt fn pt = some (.term (.br target args)))
      (read : mapList (getCell fr) args st = .ok values readState)
      (enter : enterBlock fn fr target values readState =
        .ok (instsAt fn (target, 0), fr') st') :
      RuntimeStep cfg fn pt fr st (target, 0) fr' st'
  | branchTrue {pt fr st condition target args other otherArgs tested values readState fr' st'}
      (instruction : instAt fn pt = some (.term (.condbr condition target args other otherArgs)))
      (test : (getVal fr condition >>= expectBool) st = .ok true tested)
      (read : mapList (getCell fr) args tested = .ok values readState)
      (enter : enterBlock fn fr target values readState =
        .ok (instsAt fn (target, 0), fr') st') :
      RuntimeStep cfg fn pt fr st (target, 0) fr' st'
  | branchFalse {pt fr st condition other otherArgs target args tested values readState fr' st'}
      (instruction : instAt fn pt = some (.term (.condbr condition other otherArgs target args)))
      (test : (getVal fr condition >>= expectBool) st = .ok false tested)
      (read : mapList (getCell fr) args tested = .ok values readState)
      (enter : enterBlock fn fr target values readState =
        .ok (instsAt fn (target, 0), fr') st') :
      RuntimeStep cfg fn pt fr st (target, 0) fr' st'

inductive RuntimePoint (cfg : GCfg) : Func → Pt → Frame → St → Prop
  | initializer {fuel index before global fr after}
      (fuelPositive : 0 < fuel)
      (indexValid : index < cfg.mod.globals.size)
      (initialized : initGlobals fuel cfg (List.range index) St.initial = .ok () before)
      (lookup : cfg.mod.globals[index]? = some global)
      (entry : FunctionEntry global.init 0 [] before fr after) :
      RuntimePoint cfg global.init (0, 0) fr after
  | entry {fuel before fn fr after}
      (fuelPositive : 1 < fuel)
      (globals : initGlobals fuel cfg (List.range cfg.mod.globals.size) St.initial = .ok () before)
      (lookup : cfg.mod.funcs[cfg.mod.entry]? = some fn)
      (enter : FunctionEntry fn 1 [] before fr after) :
      RuntimePoint cfg fn (0, 0) fr after
  | call {caller pt fr st result callee args origin values readState fn fr' st'}
      (callerPoint : RuntimePoint cfg caller pt fr st)
      (instruction : instAt caller pt = some (.def result (.call callee args origin)))
      (depth : fr.depth < maxCallDepth)
      (read : mapList (getVal fr) args st = .ok values readState)
      (lookup : cfg.mod.funcs[callee]? = some fn)
      (enter : FunctionEntry fn (fr.depth + 1) values readState fr' st') :
      RuntimePoint cfg fn (0, 0) fr' st'
  | step {fn pt fr st pt' fr' st'}
      (before : RuntimePoint cfg fn pt fr st)
      (transition : RuntimeStep cfg fn pt fr st pt' fr' st') :
      RuntimePoint cfg fn pt' fr' st'

theorem FunctionEntry.enterFn {cfg : GCfg} {fn : Func} {depth : Nat} {args : List Val}
    {before : St} {fr : Frame} {after : St}
    (entry : FunctionEntry fn depth args before fr after) (fuel : Nat) :
    Goose.GIR.enterFn (fuel + 1) cfg depth fn args before =
      exec fuel ⟨cfg, fn⟩ fr (instsAt fn (0, 0)) after := by
  obtain ⟨arity, act, fresh, allocated, entered⟩ := entry
  simp only [Goose.GIR.enterFn, arity, ↓reduceIte, bind_apply, allocated, entered]

theorem RuntimePoint.function_mem {cfg : GCfg} {fn : Func} {pt : Pt} {fr : Frame} {st : St}
    (point : RuntimePoint cfg fn pt fr st) : fn ∈ cfg.mod.allFuncs := by
  induction point with
  | initializer _ _ _ lookup _ =>
    simp only [Module.allFuncs, List.mem_append, List.mem_map]
    right
    exact ⟨_, Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup), rfl⟩
  | entry _ _ lookup _ =>
    apply List.mem_append_left
    exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup)
  | call _ _ _ _ lookup _ _ =>
    apply List.mem_append_left
    exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup)
  | step _ _ ih => exact ih

theorem FunctionEntry.activation {fn : Func} {depth : Nat} {args : List Val}
    {before : St} {fr : Frame} {after : St}
    (entry : FunctionEntry fn depth args before fr after) :
    ∃ act fresh,
      act = before.nextAct ∧
      fresh = { before with nextAct := before.nextAct + 1 } ∧
      enterBlock fn ⟨act, [], {}, depth⟩ 0 (args.map RVal.val) fresh =
        .ok (instsAt fn (0, 0), fr) after := by
  obtain ⟨_, act, fresh, allocated, entered⟩ := entry
  simp only [freshAct, Res.ok.injEq] at allocated
  exact ⟨act, fresh, allocated.1.symm, allocated.2.symm, entered⟩

theorem RuntimeStep.runAt {cfg : GCfg} {fn : Func} {pt pt' : Pt}
    {fr fr' : Frame} {st st' : St}
    (transition : RuntimeStep cfg fn pt fr st pt' fr' st') :
    ∃ fuel, runAt ⟨cfg, fn⟩ pt fr (fuel + 1) st =
      runAt ⟨cfg, fn⟩ pt' fr' fuel st' := by
  cases transition with
  | @define result op fuel value st' instruction eval =>
    refine ⟨fuel, ?_⟩
    unfold Goose.GIR.runAt
    rw [instsAt_cons instruction]
    simp only [Goose.GIR.exec, bind_apply, eval]
    rfl
  | effect instruction eval =>
    refine ⟨0, ?_⟩
    unfold Goose.GIR.runAt
    rw [instsAt_cons instruction]
    simp only [Goose.GIR.exec, bind_apply, eval]
  | branch instruction read enter =>
    refine ⟨0, ?_⟩
    unfold Goose.GIR.runAt
    rw [instsAt_cons instruction]
    simp only [Goose.GIR.exec, bind_apply, read, enter]
  | branchTrue instruction test read enter =>
    refine ⟨0, ?_⟩
    unfold Goose.GIR.runAt
    rw [instsAt_cons instruction]
    simp only [Goose.GIR.exec]
    rw [← bind_assoc, bind_apply, test]
    simp only [↓reduceIte]
    simp only [bind_apply, read, enter]
  | branchFalse instruction test read enter =>
    refine ⟨0, ?_⟩
    unfold Goose.GIR.runAt
    rw [instsAt_cons instruction]
    simp only [Goose.GIR.exec]
    rw [← bind_assoc, bind_apply, test]
    simp only [Bool.false_eq_true, ↓reduceIte]
    simp only [bind_apply, read, enter]

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

theorem bindParams_frame_fields {params : List (ValueId × VTy)} {args : List RVal}
    {fr result : Frame} {st final : St}
    (success : bindParams fr params args st = .ok result final) :
    result.act = fr.act ∧ result.scopes = fr.scopes ∧ result.depth = fr.depth ∧ final = st := by
  induction params generalizing args fr with
  | nil =>
    simp only [bindParams, pure_apply, Res.ok.injEq] at success
    cases success.1
    exact ⟨rfl, rfl, rfl, success.2.symm⟩
  | cons param params ih =>
    cases args with
    | nil =>
      simp only [bindParams, pure_apply, Res.ok.injEq] at success
      cases success.1
      exact ⟨rfl, rfl, rfl, success.2.symm⟩
    | cons arg args =>
      simp only [bindParams, setCell_eq, pure_bind] at success
      simpa only [Frame.set] using (ih (fr := fr.set param.1 arg) success)

theorem enterBlock_frame_fields {fn : Func} {fr result : Frame} {st final : St}
    {target : BlockId} {args : List RVal} {insts : List Inst}
    (success : enterBlock fn fr target args st = .ok (insts, result) final) :
    result.act = fr.act ∧ result.scopes = fr.scopes ∧ result.depth = fr.depth ∧ final = st := by
  unfold enterBlock at success
  cases lookup : fn.blocks[target]? with
  | none => simp [lookup, fault, M.stop] at success
  | some block =>
    simp only [lookup] at success
    split at success
    · obtain ⟨bound, middle, binding, finished⟩ := m_bind_ok success
      simp only [pure_apply, Res.ok.injEq, Prod.mk.injEq] at finished
      rw [← finished.1.2, ← finished.2]
      exact bindParams_frame_fields binding
    · simp [fault, M.stop] at success

theorem FunctionEntry.frame_origin {fn : Func} {depth : Nat} {args : List Val}
    {before : St} {fr : Frame} {after : St}
    (entry : FunctionEntry fn depth args before fr after) :
    fr.act = before.nextAct ∧ fr.scopes = [] ∧ fr.depth = depth ∧
      after = { before with nextAct := before.nextAct + 1 } := by
  obtain ⟨act, fresh, activation, state, entered⟩ := entry.activation
  obtain ⟨frameActivation, scopes, frameDepth, afterEq⟩ := enterBlock_frame_fields entered
  exact ⟨frameActivation.trans activation, scopes, frameDepth, afterEq.trans state⟩

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

def stepWrites (fn : Func) (before after : Pt) : List ValueId :=
  match instAt fn before with
  | some (.def result _) => [result]
  | some (.term _) => ((fn.blocks[after.1]?).map fun block => block.params.map Prod.fst).getD []
  | _ => []

inductive RuntimeStepsAvoid (cfg : GCfg) (fn : Func) (ids : List ValueId) :
    Pt → Frame → St → Pt → Frame → St → Prop
  | refl {pt fr st} : RuntimeStepsAvoid cfg fn ids pt fr st pt fr st
  | next {pt fr st middlePt middleFrame middleState lastPt lastFrame lastState}
      (transition : RuntimeStep cfg fn pt fr st middlePt middleFrame middleState)
      (unwritten : ∀ id ∈ ids, id ∉ stepWrites fn pt middlePt)
      (rest : RuntimeStepsAvoid cfg fn ids middlePt middleFrame middleState lastPt lastFrame lastState) :
      RuntimeStepsAvoid cfg fn ids pt fr st lastPt lastFrame lastState

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

theorem instAt_member {fn : Func} {pt : Pt} {instruction : Inst}
    (atPoint : instAt fn pt = some instruction) :
    ∃ block ∈ fn.blocks, instruction ∈ block.insts := by
  unfold instAt at atPoint
  cases lookup : fn.blocks[pt.1]? with
  | none => simp [lookup] at atPoint
  | some block =>
    simp only [lookup, Option.bind_some] at atPoint
    exact ⟨block, Array.mem_of_getElem? lookup, List.mem_of_getElem? atPoint⟩

inductive ControlStep (fn : Func) : Pt → Pt → Prop
  | definition {pt result operation}
      (instruction : instAt fn pt = some (.def result operation)) :
      ControlStep fn pt (pt.1, pt.2 + 1)
  | effect {pt effect}
      (instruction : instAt fn pt = some (.eff effect)) :
      ControlStep fn pt (pt.1, pt.2 + 1)
  | branch {pt term target}
      (instruction : instAt fn pt = some (.term term))
      (successor : target ∈ term.successors) : ControlStep fn pt (target, 0)

theorem RuntimeStep.control {cfg : GCfg} {fn : Func} {pt pt' : Pt}
    {fr fr' : Frame} {st st' : St}
    (transition : RuntimeStep cfg fn pt fr st pt' fr' st') : ControlStep fn pt pt' := by
  cases transition with
  | define instruction _ => exact .definition instruction
  | effect instruction _ => exact .effect instruction
  | branch instruction _ _ => exact .branch instruction (by simp [Term.successors])
  | branchTrue instruction _ _ _ => exact .branch instruction (by simp [Term.successors])
  | branchFalse instruction _ _ _ => exact .branch instruction (by simp [Term.successors])

inductive ControlPath (fn : Func) (ids : List ValueId) : Pt → Pt → Prop
  | refl {pt} : ControlPath fn ids pt pt
  | next {pt middle last}
      (transition : ControlStep fn pt middle)
      (unwritten : ∀ id ∈ ids, id ∉ stepWrites fn pt middle)
      (rest : ControlPath fn ids middle last) : ControlPath fn ids pt last

theorem RuntimeStepsAvoid.control_path {cfg : GCfg} {fn : Func} {ids : List ValueId}
    {pt pt' : Pt} {fr fr' : Frame} {st st' : St}
    (history : RuntimeStepsAvoid cfg fn ids pt fr st pt' fr' st') : ControlPath fn ids pt pt' := by
  induction history with
  | refl => exact .refl
  | next transition unwritten rest ih => exact .next transition.control unwritten ih

theorem ControlPath.trans {fn : Func} {ids : List ValueId} {first middle last : Pt}
    (left : ControlPath fn ids first middle) (right : ControlPath fn ids middle last) :
    ControlPath fn ids first last := by
  induction left with
  | refl => exact right
  | next transition unwritten rest ih => exact .next transition unwritten (ih right)

theorem RuntimeStepsAvoid.protect {cfg : GCfg} {fn : Func} {ids guarded : List ValueId}
    {first last : Pt} {firstFrame lastFrame : Frame} {firstState lastState : St}
    (history : RuntimeStepsAvoid cfg fn ids first firstFrame firstState last lastFrame lastState)
    (edgeProtected : ∀ {before after}, ControlPath fn ids first before →
      ControlStep fn before after → (∀ id ∈ ids, id ∉ stepWrites fn before after) →
      ControlPath fn ids after last → ∀ id ∈ guarded, id ∉ stepWrites fn before after) :
    RuntimeStepsAvoid cfg fn guarded first firstFrame firstState last lastFrame lastState := by
  have lift : ∀ {middle frame state}, ControlPath fn ids first middle →
      RuntimeStepsAvoid cfg fn ids middle frame state last lastFrame lastState →
      RuntimeStepsAvoid cfg fn guarded middle frame state last lastFrame lastState := by
    intro middle frame state path rest
    induction rest with
    | refl => exact .refl
    | next transition unwritten remaining ih =>
      exact .next transition
        (edgeProtected path transition.control unwritten remaining.control_path)
        (ih history edgeProtected (path.trans (.next transition.control unwritten .refl)))
  exact lift .refl history

theorem enterBlock_instructions {fn : Func} {fr result : Frame} {st final : St}
    {target : BlockId} {args : List RVal} {insts : List Inst}
    (success : enterBlock fn fr target args st = .ok (insts, result) final) :
    insts = instsAt fn (target, 0) := by
  unfold enterBlock at success
  cases lookup : fn.blocks[target]? with
  | none => simp [lookup, fault, M.stop] at success
  | some block =>
    simp only [lookup] at success
    split at success
    · obtain ⟨bound, middle, binding, finished⟩ := m_bind_ok success
      simp only [pure_apply, Res.ok.injEq, Prod.mk.injEq] at finished
      simpa [instsAt, lookup] using finished.1.1.symm
    · simp [fault, M.stop] at success

theorem enterFn_success_entry {cfg : GCfg} {fn : Func} {depth fuel : Nat} {args : List Val}
    {before final : St} {value : Val}
    (success : Goose.GIR.enterFn fuel cfg depth fn args before = .ok value final) :
    ∃ remaining fr entered,
      fuel = remaining + 1 ∧ FunctionEntry fn depth args before fr entered ∧
      exec remaining ⟨cfg, fn⟩ fr (instsAt fn (0, 0)) entered = .ok value final := by
  cases fuel with
  | zero => simp [Goose.GIR.enterFn, timeout, M.stop] at success
  | succ remaining =>
    simp only [Goose.GIR.enterFn] at success
    split at success
    · rename_i arity
      obtain ⟨act, fresh, allocated, afterAllocation⟩ := m_bind_ok success
      obtain ⟨pair, entered, enteredBlock, executed⟩ := m_bind_ok afterAllocation
      obtain ⟨insts, fr⟩ := pair
      have instructions := enterBlock_instructions enteredBlock
      rw [instructions] at enteredBlock executed
      exact ⟨remaining, fr, entered, rfl, ⟨arity, act, fresh, allocated, enteredBlock⟩, executed⟩
    · simp [fault, M.stop] at success

theorem lookupFn_success {cfg : GCfg} {id : FnId} {before final : St} {fn : Func}
    (success : lookupFn cfg id before = .ok fn final) :
    cfg.mod.funcs[id]? = some fn ∧ final = before := by
  unfold lookupFn at success
  cases lookup : cfg.mod.funcs[id]? with
  | none => simp [lookup, fault, M.stop] at success
  | some found =>
    simp only [lookup, pure_apply, Res.ok.injEq] at success
    exact ⟨by simp [success.1], success.2.symm⟩

theorem callFn_success_entry {cfg : GCfg} {id : FnId} {depth fuel : Nat} {args : List Val}
    {before final : St} {value : Val}
    (success : callFn fuel cfg depth id args before = .ok value final) :
    ∃ remaining fn,
      fuel = remaining + 1 ∧ depth < maxCallDepth ∧ cfg.mod.funcs[id]? = some fn ∧
      Goose.GIR.enterFn remaining cfg (depth + 1) fn args before = .ok value final := by
  cases fuel with
  | zero => simp [callFn, timeout, M.stop] at success
  | succ remaining =>
    by_cases cap : depth ≥ maxCallDepth
    · simp [callFn, cap, timeout, M.stop, bind_apply] at success
    · simp only [callFn, cap, ↓reduceIte] at success
      obtain ⟨fn, middle, lookedUp, entered⟩ := m_bind_ok success
      obtain ⟨lookup, unchanged⟩ := lookupFn_success lookedUp
      rw [unchanged] at entered
      exact ⟨remaining, fn, rfl, Nat.lt_of_not_ge cap, lookup, entered⟩

theorem runModule_success_entry {cfg : GCfg} {fuel : Nat} {final : St}
    (success : Goose.GIR.runModule fuel cfg St.initial = .ok () final) :
    ∃ fn fr entered, RuntimePoint cfg fn (0, 0) fr entered := by
  unfold Goose.GIR.runModule at success
  obtain ⟨initializedValue, before, initialized, afterGlobals⟩ := m_bind_ok success
  cases initializedValue
  obtain ⟨result, returned, called, finished⟩ := m_bind_ok afterGlobals
  obtain ⟨remaining, fn, fuelEq, depth, lookup, entered⟩ := callFn_success_entry called
  obtain ⟨bodyFuel, fr, afterEntry, remainingEq, entry, executed⟩ := enterFn_success_entry entered
  refine ⟨fn, fr, afterEntry, .entry ?_ initialized lookup entry⟩
  omega

theorem execEff_frame_fields {fn : Func} {fr result : Frame} {st final : St}
    {effect : Effect}
    (success : execEff fn fr effect st = .ok result final) : result.act = fr.act ∧ result.depth = fr.depth ∧ result.vals = fr.vals := by
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
        exact ⟨rfl, rfl, rfl⟩
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
    exact ⟨rfl, rfl, rfl⟩

theorem execEff_preserves_cells {fn : Func} {fr result : Frame} {st final : St}
    {effect : Effect}
    (success : execEff fn fr effect st = .ok result final) : result.vals = fr.vals :=
  (execEff_frame_fields success).2.2

theorem RuntimeStep.frame_identity {cfg : GCfg} {fn : Func} {pt pt' : Pt}
    {fr fr' : Frame} {st st' : St}
    (transition : RuntimeStep cfg fn pt fr st pt' fr' st') :
    fr'.act = fr.act ∧ fr'.depth = fr.depth := by
  cases transition with
  | define _ _ => exact ⟨rfl, rfl⟩
  | effect _ evaluated =>
    have fields := execEff_frame_fields evaluated
    exact ⟨fields.1, fields.2.1⟩
  | branch _ _ entered =>
    have fields := enterBlock_frame_fields entered
    exact ⟨fields.1, fields.2.2.1⟩
  | branchTrue _ _ _ entered =>
    have fields := enterBlock_frame_fields entered
    exact ⟨fields.1, fields.2.2.1⟩
  | branchFalse _ _ _ entered =>
    have fields := enterBlock_frame_fields entered
    exact ⟨fields.1, fields.2.2.1⟩

theorem ControlPath.definition_barrier {fn : Func} {id : ValueId} {operation : Op}
    {definitionPt first last : Pt}
    (definition : instAt fn definitionPt = some (.def id operation))
    (noEarlierTerm : ∀ index < definitionPt.2, ∀ term,
      instAt fn (definitionPt.1, index) ≠ some (.term term))
    (path : ControlPath fn [id] first last)
    (beforeDefinition : first.1 = definitionPt.1 ∧ first.2 ≤ definitionPt.2) :
    last.1 = definitionPt.1 ∧ last.2 ≤ definitionPt.2 := by
  induction path with
  | refl => exact beforeDefinition
  | @next first middle last transition unwritten rest ih =>
    cases transition with
    | @definition result writtenOperation instruction =>
      by_cases equal : first.2 = definitionPt.2
      · have pointEq : first = definitionPt := Prod.ext beforeDefinition.1 equal
        rw [pointEq, definition] at instruction
        cases instruction
        have excluded := unwritten id (by simp)
        simp [stepWrites, pointEq, definition] at excluded
      · apply ih
        exact ⟨beforeDefinition.1, by omega⟩
    | @effect effect instruction =>
      by_cases equal : first.2 = definitionPt.2
      · have pointEq : first = definitionPt := Prod.ext beforeDefinition.1 equal
        rw [pointEq, definition] at instruction
        cases instruction
      · apply ih
        exact ⟨beforeDefinition.1, by omega⟩
    | @branch term target instruction successor =>
      have pointEq : first = (definitionPt.1, first.2) := Prod.ext beforeDefinition.1 rfl
      by_cases equal : first.2 = definitionPt.2
      · have exactPoint : first = definitionPt := Prod.ext beforeDefinition.1 equal
        rw [exactPoint, definition] at instruction
        cases instruction
      · have earlier : first.2 < definitionPt.2 := by omega
        rw [pointEq] at instruction
        exact False.elim (noEarlierTerm first.2 earlier term instruction)

theorem RuntimePoint.control_path {cfg : GCfg} {fn : Func} {pt : Pt} {fr : Frame} {st : St}
    (point : RuntimePoint cfg fn pt fr st) : ControlPath fn [] (0, 0) pt := by
  induction point with
  | initializer _ _ _ _ _ => exact .refl
  | entry _ _ _ _ => exact .refl
  | call _ _ _ _ _ _ _ => exact .refl
  | step _ transition ih =>
    exact ih.trans (.next transition.control (by simp) .refl)

theorem terminated_no_term_before_def {fn : Func} {pt : Pt} {id : ValueId} {operation : Op}
    (terminated : TerminatedBlocks fn)
    (definition : instAt fn pt = some (.def id operation)) :
    ∀ index < pt.2, ∀ term, instAt fn (pt.1, index) ≠ some (.term term) := by
  unfold instAt at definition
  cases lookup : fn.blocks[pt.1]? with
  | none => simp [lookup] at definition
  | some block =>
    simp only [lookup, Option.bind_some] at definition
    obtain ⟨oneTerm, lastTerm⟩ := terminated block (Array.mem_of_getElem? lookup)
    cases lastElement : block.insts.getLast? with
    | none => simp [Block.lastTerm?, lastElement] at lastTerm
    | some instruction =>
      cases instruction with
      | «def» _ _ => simp [Block.lastTerm?, lastElement] at lastTerm
      | eff _ => simp [Block.lastTerm?, lastElement] at lastTerm
      | term terminator =>
        obtain ⟨prefixInsts, shape⟩ := List.getLast?_eq_some_iff.mp lastElement
        have noPrefixTerms : prefixInsts.filterMap Inst.term? = [] := by
          have lengthZero : (prefixInsts.filterMap Inst.term?).length = 0 := by
            simpa [Block.terms, shape, List.filterMap_append, Inst.term?] using oneTerm
          exact List.length_eq_zero_iff.mp lengthZero
        have defBeforeLast : pt.2 < prefixInsts.length := by
          have bound := (List.getElem?_eq_some_iff.mp definition).1
          rw [shape, List.length_append] at bound
          simp only [List.length_cons, List.length_nil] at bound
          by_cases before : pt.2 < prefixInsts.length
          · exact before
          · have equal : pt.2 = prefixInsts.length := by omega
            simp [shape, equal] at definition
        intro index before term earlier
        have prefixIndex : index < prefixInsts.length := by omega
        simp only [instAt, lookup, Option.bind_some] at earlier
        rw [shape] at earlier
        simp only [List.getElem?_append, prefixIndex, ↓reduceIte] at earlier
        have present : term ∈ prefixInsts.filterMap Inst.term? :=
          List.mem_filterMap.mpr ⟨.term term, List.mem_of_getElem? earlier, rfl⟩
        rw [noPrefixTerms] at present
        cases present

theorem validated_definition_barrier {m : Goose.GIR.Module} {fn : Func} {id : ValueId} {operation : Op}
    {definitionPt first last : Pt}
    (validated : validate m = .ok ()) (member : fn ∈ m.allFuncs)
    (definition : instAt fn definitionPt = some (.def id operation))
    (path : ControlPath fn [id] first last)
    (beforeDefinition : first.1 = definitionPt.1 ∧ first.2 ≤ definitionPt.2) :
    last.1 = definitionPt.1 ∧ last.2 ≤ definitionPt.2 := by
  have terminated := ((validate_sound m validated).1 fn member).1
  exact ControlPath.definition_barrier definition
    (terminated_no_term_before_def terminated definition) path beforeDefinition

theorem validated_no_definition_avoiding_path_to_term {m : Goose.GIR.Module} {fn : Func}
    {id : ValueId} {operation : Op} {term : Term} {definitionPt first last : Pt}
    (validated : validate m = .ok ()) (member : fn ∈ m.allFuncs)
    (definition : instAt fn definitionPt = some (.def id operation))
    (path : ControlPath fn [id] first last)
    (beforeDefinition : first.1 = definitionPt.1 ∧ first.2 ≤ definitionPt.2)
    (atTerm : instAt fn last = some (.term term)) : False := by
  obtain ⟨sameBlock, beforeIndex⟩ :=
    validated_definition_barrier validated member definition path beforeDefinition
  have terminated := ((validate_sound m validated).1 fn member).1
  by_cases equal : last.2 = definitionPt.2
  · have samePoint : last = definitionPt := Prod.ext sameBlock equal
    rw [samePoint, definition] at atTerm
    cases atTerm
  · have earlier : last.2 < definitionPt.2 := by omega
    have samePoint : last = (definitionPt.1, last.2) := Prod.ext sameBlock rfl
    rw [samePoint] at atTerm
    exact terminated_no_term_before_def terminated definition last.2 earlier term atTerm

theorem RuntimeStepsAvoid.frame_identity {cfg : GCfg} {fn : Func} {ids : List ValueId}
    {pt pt' : Pt} {fr fr' : Frame} {st st' : St}
    (history : RuntimeStepsAvoid cfg fn ids pt fr st pt' fr' st') :
    fr'.act = fr.act ∧ fr'.depth = fr.depth := by
  induction history with
  | refl => exact ⟨rfl, rfl⟩
  | next transition unwritten rest ih =>
    have identity := transition.frame_identity
    exact ⟨ih.1.trans identity.1, ih.2.trans identity.2⟩

theorem RuntimePoint.call_of_execOp_success {cfg : GCfg} {caller : Func} {pt : Pt}
    {fr : Frame} {st final : St} {result callee : ValueId} {args : List ValueId}
    {origin : Option OriginId} {fuel : Nat} {value : RVal}
    (point : RuntimePoint cfg caller pt fr st)
    (instruction : instAt caller pt = some (.def result (.call callee args origin)))
    (success : execOp fuel ⟨cfg, caller⟩ fr (.call callee args origin) st = .ok value final) :
    ∃ fn enteredFrame enteredState, RuntimePoint cfg fn (0, 0) enteredFrame enteredState := by
  cases fuel with
  | zero => simp [execOp, timeout, M.stop] at success
  | succ remaining =>
    simp only [execOp] at success
    obtain ⟨values, readState, read, afterRead⟩ := m_bind_ok success
    obtain ⟨returnedValue, returnedState, called, finished⟩ := m_bind_ok afterRead
    obtain ⟨callFuel, fn, _, depth, lookup, entered⟩ := callFn_success_entry called
    obtain ⟨bodyFuel, enteredFrame, enteredState, _, entry, executed⟩ := enterFn_success_entry entered
    exact ⟨fn, enteredFrame, enteredState, .call point instruction depth read lookup entry⟩

theorem RuntimePoint.initializer_of_enterFn_success {cfg : GCfg} {fuel index : Nat}
    {before final : St} {global : Goose.GIR.Global} {value : Val}
    (initialized : initGlobals fuel cfg (List.range index) St.initial = .ok () before)
    (lookup : cfg.mod.globals[index]? = some global)
    (success : Goose.GIR.enterFn fuel cfg 0 global.init [] before = .ok value final) :
    ∃ fr entered, RuntimePoint cfg global.init (0, 0) fr entered := by
  obtain ⟨remaining, fr, entered, fuelEq, entry, executed⟩ := enterFn_success_entry success
  have positive : 0 < fuel := by omega
  have validIndex := (Array.getElem?_eq_some_iff.mp lookup).1
  exact ⟨fr, entered, .initializer positive validIndex initialized lookup entry⟩

end Goose.Evidence
