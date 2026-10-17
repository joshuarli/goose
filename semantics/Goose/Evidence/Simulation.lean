import Goose.Evidence.Checked
import Goose.Evidence.Reachable

namespace Goose.Proofs.Bounds

open Goose.Core Goose.GIR Goose.Evidence

def EntryPoints (cfg : GCfg) (fn : Func) (depth : Nat) (args : List Val) (state : St) : Prop :=
  ∀ fr after, FunctionEntry fn depth args state fr after → RuntimePoint cfg fn (0, 0) fr after

def CallPoints (cfg : GCfg) (depth : Nat) (callee : FnId) (args : List Val) (state : St) : Prop :=
  ∀ fn fr after, depth < maxCallDepth → cfg.mod.funcs[callee]? = some fn →
    FunctionEntry fn (depth + 1) args state fr after → RuntimePoint cfg fn (0, 0) fr after

def ExecAgreement (cfg : GCfg) (fuel : Nat) : Prop :=
  ∀ fn point fr state, RuntimePoint cfg fn point fr state →
    exec fuel ⟨checkedConfig cfg, checkedFunction fn⟩ fr ((instsAt fn point).map checkedInst) state =
      exec fuel ⟨cfg, fn⟩ fr (instsAt fn point) state

def EntryAgreement (cfg : GCfg) (fuel : Nat) : Prop :=
  ∀ fn depth args state, (0 < fuel → EntryPoints cfg fn depth args state) →
    Goose.GIR.enterFn fuel (checkedConfig cfg) depth (checkedFunction fn) args state =
      Goose.GIR.enterFn fuel cfg depth fn args state

def CallAgreement (cfg : GCfg) (fuel : Nat) : Prop :=
  ∀ depth callee args state, (1 < fuel → CallPoints cfg depth callee args state) →
    callFn fuel (checkedConfig cfg) depth callee args state = callFn fuel cfg depth callee args state

def OpAgreement (cfg : GCfg) (fuel : Nat) : Prop :=
  ∀ fn point fr state result op, RuntimePoint cfg fn point fr state →
    instAt fn point = some (.def result op) →
    execOp fuel ⟨checkedConfig cfg, checkedFunction fn⟩ fr (checkedOp op) state =
      execOp fuel ⟨cfg, fn⟩ fr op state

private theorem enterBlock_insts {fn : Func} {fr next : Frame} {block : BlockId}
    {args : List RVal} {state after : St} {insts : List Inst}
    (entered : Goose.GIR.enterBlock fn fr block args state = .ok (insts, next) after) :
    insts = instsAt fn (block, 0) := by
  unfold Goose.GIR.enterBlock at entered
  cases blockAt : fn.blocks[block]? with
  | none => simp [blockAt, fault, M.stop] at entered
  | some body =>
    simp only [blockAt] at entered
    split at entered
    · simp only [bind_apply] at entered
      cases bound : Goose.GIR.bindParams fr body.params args state with
      | stop reason stopped => simp [bound] at entered
      | ok frame middle =>
        simp only [bound, pure_apply, Res.ok.injEq, Prod.mk.injEq] at entered
        simp [instsAt, blockAt, ← entered.1.1]
    · simp [fault, M.stop] at entered

private theorem instAt_of_insts {fn : Func} {point : Pt} {inst : Inst} {rest : List Inst}
    (layout : instsAt fn point = inst :: rest) : instAt fn point = some inst := by
  unfold instsAt at layout
  unfold instAt
  cases blockAt : fn.blocks[point.1]? with
  | none => simp [blockAt] at layout
  | some body =>
    simp only [blockAt, Option.map_some, Option.getD_some] at layout
    simp only [Option.bind_some]
    have first : (body.insts.drop point.2)[0]? = some inst := by rw [layout]; rfl
    simpa only [List.getElem?_drop, Nat.add_zero] using first

private theorem checked_op_pure {cfg : GCfg} {fn : Func} {point : Pt} {fr : Frame} {state : St}
    {result : ValueId} {op : Op} (accepted : validate cfg.mod = .ok ())
    (reachable : RuntimePoint cfg fn point fr state)
    (instruction : instAt fn point = some (.def result op)) :
    execPure ⟨checkedConfig cfg, checkedFunction fn⟩ fr (checkedOp op) = execPure ⟨cfg, fn⟩ fr op := by
  apply checked_execPure (cx := ⟨cfg, fn⟩) (op := op)
  intro view index same
  subst op
  exact reachable_index accepted reachable instruction

private theorem checked_fuel_zero {cfg : GCfg} (accepted : validate cfg.mod = .ok ()) :
    ExecAgreement cfg 0 ∧ EntryAgreement cfg 0 ∧ CallAgreement cfg 0 ∧ OpAgreement cfg 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro fn point fr state reachable; rfl
  · intro fn depth args state points; rfl
  · intro depth callee args state points; rfl
  · intro fn point fr state result op reachable instruction
    cases op <;> first
      | rfl
      | exact congrFun (checked_op_pure accepted reachable instruction) state

private theorem lookupFn_success {cfg : GCfg} {callee : FnId} {state after : St} {fn : Func}
    (success : lookupFn cfg callee state = .ok fn after) :
    cfg.mod.funcs[callee]? = some fn ∧ after = state := by
  unfold lookupFn at success
  cases found : cfg.mod.funcs[callee]? with
  | none => simp [found, fault, M.stop] at success
  | some body =>
    simp only [found, pure_apply, Res.ok.injEq] at success
    exact ⟨by simp [← success.1], success.2.symm⟩

private theorem checked_entry_step {cfg : GCfg} {fuel : Nat}
    (agreement : ExecAgreement cfg fuel) : EntryAgreement cfg (fuel + 1) := by
  intro fn depth args state points
  simp only [Goose.GIR.enterFn]
  have parameters : (checkedFunction fn).params.length = fn.params.length := rfl
  rw [parameters]
  by_cases arity : fn.params.length = args.length
  · simp only [arity, ↓reduceIte, checked_enterBlock, bind_assoc, pure_bind, bind_apply]
    cases allocated : freshAct state with
    | stop reason stopped => rfl
    | ok act fresh =>
      simp only []
      cases entered : Goose.GIR.enterBlock fn ⟨act, [], {}, depth⟩ 0 (args.map RVal.val) fresh with
      | stop reason stopped => rfl
      | ok pair after =>
        rcases pair with ⟨insts, fr⟩
        simp only []
        have body := enterBlock_insts entered
        have entry : FunctionEntry fn depth args state fr after :=
          ⟨arity, act, fresh, allocated, by simpa [body] using entered⟩
        have reached := points (by omega) fr after entry
        simpa only [body] using agreement fn (0, 0) fr after reached
  · simp [arity]

private theorem checked_call_step {cfg : GCfg} {fuel : Nat}
    (agreement : EntryAgreement cfg fuel) : CallAgreement cfg (fuel + 1) := by
  intro depth callee args state points
  simp only [callFn]
  by_cases tooDeep : depth ≥ maxCallDepth
  · simp [tooDeep, Goose.Core.timeout, M.stop, bind, M.bind']
  · simp only [tooDeep, ↓reduceIte, checked_lookupFn, bind_apply]
    cases looked : lookupFn cfg callee state with
    | stop reason stopped => rfl
    | ok fn after =>
      obtain ⟨functionAt, same⟩ := lookupFn_success looked
      subst after
      apply agreement
      intro positive fr after entry
      exact points (by omega) fn fr after (by omega) functionAt entry

private theorem checked_op_step {cfg : GCfg} {fuel : Nat} (accepted : validate cfg.mod = .ok ())
    (agreement : CallAgreement cfg fuel) :
    OpAgreement cfg (fuel + 1) := by
  intro fn point fr state result op reachable instruction
  cases op with
  | call callee args origin =>
    simp only [execOp, checkedOp, bind_apply]
    cases read : mapList (getVal fr) args state with
    | stop reason stopped => rfl
    | ok values after =>
      simp only []
      have calls : callFn fuel (checkedConfig cfg) fr.depth callee values after =
          callFn fuel cfg fr.depth callee values after := by
        apply agreement
        intro enough body frame endState depth lookup entry
        exact RuntimePoint.call reachable instruction depth read lookup entry
      rw [calls]
  | _ =>
    simpa only [execOp, checkedOp] using congrFun (checked_op_pure accepted reachable instruction) state

private theorem checked_edge_exec {cfg : GCfg} {fn : Func} {fuel : Nat}
    (agreement : ExecAgreement cfg fuel) (fr : Frame) (target : BlockId) (args : List RVal) (state : St)
    (points : ∀ insts next after,
      Goose.GIR.enterBlock fn fr target args state = .ok (insts, next) after →
        RuntimePoint cfg fn (target, 0) next after) :
    (do
      let (insts, next) ← Goose.GIR.enterBlock (checkedFunction fn) fr target args
      exec fuel ⟨checkedConfig cfg, checkedFunction fn⟩ next insts) state =
    (do
      let (insts, next) ← Goose.GIR.enterBlock fn fr target args
      exec fuel ⟨cfg, fn⟩ next insts) state := by
  rw [checked_enterBlock]
  simp only [bind_apply]
  cases entered : Goose.GIR.enterBlock fn fr target args state with
  | stop reason stopped => rfl
  | ok pair after =>
    rcases pair with ⟨insts, next⟩
    have body := enterBlock_insts entered
    have reachable := points insts next after entered
    simpa only [body, pure_apply] using agreement fn (target, 0) next after reachable

private theorem checked_exec_step {cfg : GCfg} {fuel : Nat}
    (agreement : ExecAgreement cfg fuel) (operations : OpAgreement cfg fuel) :
    ExecAgreement cfg (fuel + 1) := by
  intro fn point fr state reachable
  cases layout : instsAt fn point with
  | nil => rfl
  | cons inst rest =>
    have instruction := instAt_of_insts layout
    have restAt : rest = instsAt fn (point.1, point.2 + 1) := by
      have layout' := instsAt_cons instruction
      rw [layout] at layout'
      exact (List.cons.inj layout').2
    cases inst with
    | «def» result op =>
      simp only [List.map_cons, checkedInst, exec, bind_apply]
      rw [operations fn point fr state result op reachable instruction]
      cases evaluated : execOp fuel ⟨cfg, fn⟩ fr op state with
      | stop reason stopped => rfl
      | ok cell after =>
        simp only [setCell, pure_apply]
        have next := RuntimePoint.step reachable (RuntimeStep.define instruction evaluated)
        simpa only [restAt, Frame.set] using agreement fn (point.1, point.2 + 1) (fr.set result cell) after next
    | eff effect =>
      simp only [List.map_cons, checkedInst, exec, checked_execEff, bind_apply]
      cases evaluated : execEff fn fr effect state with
      | stop reason stopped => rfl
      | ok next after =>
        have reached := RuntimePoint.step reachable (RuntimeStep.effect instruction evaluated)
        simpa only [restAt] using agreement fn (point.1, point.2 + 1) next after reached
    | term term =>
      cases term with
      | ret | abort | exit | unreachable => rfl
      | br target args =>
        simp only [List.map_cons, checkedInst, exec, bind_apply]
        cases read : mapList (getCell fr) args state with
        | stop reason stopped => rfl
        | ok values readState =>
          simp only []
          apply checked_edge_exec agreement
          intro insts next after entered
          have body := enterBlock_insts entered
          exact RuntimePoint.step reachable (RuntimeStep.branch instruction read (by simpa [body] using entered))
      | condbr condition yes yesArgs no noArgs =>
        simp only [List.map_cons, checkedInst, exec, bind_apply]
        cases conditionValue : getVal fr condition state with
        | stop reason stopped => rfl
        | ok value first =>
          simp only []
          cases tested : expectBool value first with
          | stop reason stopped => rfl
          | ok bit testedState =>
            simp only []
            have test : (getVal fr condition >>= expectBool) state = .ok bit testedState := by
              simp only [bind_apply, conditionValue, tested]
            cases bit with
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte, bind_apply]
              cases read : mapList (getCell fr) noArgs testedState with
              | stop reason stopped => rfl
              | ok values readState =>
                simp only []
                apply checked_edge_exec agreement
                intro insts next after entered
                have body := enterBlock_insts entered
                exact RuntimePoint.step reachable
                  (RuntimeStep.branchFalse instruction test read (by simpa [body] using entered))
            | true =>
              simp only [↓reduceIte, bind_apply]
              cases read : mapList (getCell fr) yesArgs testedState with
              | stop reason stopped => rfl
              | ok values readState =>
                simp only []
                apply checked_edge_exec agreement
                intro insts next after entered
                have body := enterBlock_insts entered
                exact RuntimePoint.step reachable
                  (RuntimeStep.branchTrue instruction test read (by simpa [body] using entered))

theorem checked_fuel {cfg : GCfg} (accepted : validate cfg.mod = .ok ())
    (fuel : Nat) :
    ExecAgreement cfg fuel ∧ EntryAgreement cfg fuel ∧ CallAgreement cfg fuel ∧ OpAgreement cfg fuel := by
  induction fuel with
  | zero => exact checked_fuel_zero accepted
  | succ fuel ih =>
    exact ⟨checked_exec_step ih.1 ih.2.2.2, checked_entry_step ih.1,
      checked_call_step ih.2.1, checked_op_step accepted ih.2.2.1⟩

private theorem initGlobals_append (fuel : Nat) (cfg : GCfg) (before rest : List GlobalId) :
    GIR.initGlobals fuel cfg (before ++ rest) = (do
      GIR.initGlobals fuel cfg before
      GIR.initGlobals fuel cfg rest) := by
  induction before with
  | nil => simp only [List.nil_append, GIR.initGlobals, pure_bind]
  | cons global before ih =>
    simp only [List.cons_append, GIR.initGlobals, ih, bind_assoc]

private theorem range_prefix {before rest : List Nat} {index size : Nat}
    (layout : before ++ index :: rest = List.range size) : before = List.range index ∧ index < size := by
  have indexed : (List.range size)[before.length]? = some index := by
    rw [← layout]
    simp
  have bound : before.length < size := by
    simpa using (List.getElem?_eq_some_iff.mp indexed).1
  have same : before.length = index := by
    rw [List.getElem?_range bound] at indexed
    exact Option.some.inj indexed
  constructor
  · have taken := congrArg (List.take before.length) layout
    simpa [same, List.take_range, Nat.min_eq_left (by omega : index ≤ size)] using taken
  · omega

private theorem lookupInit_success {cfg : GCfg} {index : GlobalId} {state after : St} {fn : Func}
    (success : lookupInit cfg index state = .ok fn after) :
    ∃ global, cfg.mod.globals[index]? = some global ∧ fn = global.init ∧ after = state := by
  unfold lookupInit at success
  cases found : cfg.mod.globals[index]? with
  | none => simp [found, fault, M.stop] at success
  | some global =>
    simp only [found, pure_apply, Res.ok.injEq] at success
    exact ⟨global, rfl, success.1.symm, success.2.symm⟩

private theorem checked_initGlobals_suffix {cfg : GCfg} (accepted : validate cfg.mod = .ok ())
    (fuel : Nat) :
    ∀ before rest state, before ++ rest = List.range cfg.mod.globals.size →
      GIR.initGlobals fuel cfg before St.initial = .ok () state →
      GIR.initGlobals fuel (checkedConfig cfg) rest state = GIR.initGlobals fuel cfg rest state := by
  intro before rest
  induction rest generalizing before with
  | nil => intro state layout initialized; rfl
  | cons index rest ih =>
    intro state layout initialized
    obtain ⟨beforeRange, indexValid⟩ := range_prefix layout
    simp only [GIR.initGlobals, checked_lookupInit, bind_apply]
    cases looked : lookupInit cfg index state with
    | stop reason stopped => rfl
    | ok fn after =>
      obtain ⟨global, globalAt, rfl, same⟩ := lookupInit_success looked
      subst after
      simp only []
      have entryAgreement : Goose.GIR.enterFn fuel (checkedConfig cfg) 0 (checkedFunction global.init) [] state =
          Goose.GIR.enterFn fuel cfg 0 global.init [] state := by
        apply (checked_fuel accepted fuel).2.1
        intro positive fr after entry
        exact RuntimePoint.initializer positive indexValid (by simpa [beforeRange] using initialized) globalAt entry
      simp only [pure_apply]
      rw [entryAgreement]
      cases entered : Goose.GIR.enterFn fuel cfg 0 global.init [] state with
      | stop reason stopped => rfl
      | ok value enteredState =>
        simp only []
        cases bound : bindRoot (.global index) value enteredState with
        | stop reason stopped => rfl
        | ok ignored boundState =>
          cases ignored
          simp only []
          apply ih (before ++ [index]) boundState
          · simpa only [List.append_assoc, List.singleton_append] using layout
          · rw [initGlobals_append]
            simp only [bind_apply, initialized, GIR.initGlobals, looked, entered, bound, pure_apply]

theorem checked_initGlobals {cfg : GCfg} (accepted : validate cfg.mod = .ok ())
    (fuel : Nat) :
    GIR.initGlobals fuel (checkedConfig cfg) (List.range cfg.mod.globals.size) St.initial =
      GIR.initGlobals fuel cfg (List.range cfg.mod.globals.size) St.initial :=
  checked_initGlobals_suffix accepted fuel [] (List.range cfg.mod.globals.size)
    St.initial rfl rfl

theorem checked_runModule {cfg : GCfg} (accepted : validate cfg.mod = .ok ())
    (fuel : Nat) :
    GIR.runModule fuel (checkedConfig cfg) St.initial = GIR.runModule fuel cfg St.initial := by
  have sizes : (checkedConfig cfg).mod.globals.size = cfg.mod.globals.size := by
    simp [checkedConfig, checkedModule]
  have entry : (checkedConfig cfg).mod.entry = cfg.mod.entry := rfl
  simp only [GIR.runModule, sizes, entry, bind_apply]
  rw [checked_initGlobals accepted fuel]
  cases globals : GIR.initGlobals fuel cfg (List.range cfg.mod.globals.size) St.initial with
  | stop reason stopped => rfl
  | ok ignored state =>
    cases ignored
    simp only []
    have calls : callFn fuel (checkedConfig cfg) 0 cfg.mod.entry [] state =
        callFn fuel cfg 0 cfg.mod.entry [] state := by
      apply (checked_fuel accepted fuel).2.2.1
      intro enough fn fr after depth lookup entered
      exact RuntimePoint.entry enough globals lookup entered
    rw [calls]

theorem checked_run {m : GIR.Module} (accepted : validate m = .ok ())
    (profile : NumProfile) (fuel : Nat) :
    run fuel profile (checkedModule m) = run fuel profile m := by
  unfold run
  have same := checked_runModule (cfg := ⟨profile, m⟩) accepted fuel
  change GIR.runModule fuel ⟨profile, checkedModule m⟩ St.initial = GIR.runModule fuel ⟨profile, m⟩ St.initial at same
  rw [same]

end Goose.Proofs.Bounds
