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

end Goose.Evidence
