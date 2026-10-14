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

end Goose.Evidence
