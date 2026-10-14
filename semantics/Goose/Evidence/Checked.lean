import Goose.Evidence.Replay

namespace Goose.Proofs.Bounds

open Goose.Core Goose.GIR

def checkedOp : Op → Op
  | .indexProven view index => .indexChecked view index none
  | op => op

def checkedInst : Inst → Inst
  | .def result op => .def result (checkedOp op)
  | inst => inst

def checkedBlock (block : GIR.Block) : GIR.Block :=
  { block with insts := block.insts.map checkedInst }

def checkedFunction (function : Func) : Func :=
  { function with blocks := function.blocks.map checkedBlock }

def checkedModule (m : GIR.Module) : GIR.Module :=
  { m with funcs := m.funcs.map checkedFunction,
           globals := m.globals.map fun global => { global with init := checkedFunction global.init } }

def checkedConfig (cfg : GCfg) : GCfg := { cfg with mod := checkedModule cfg.mod }

def checkedContext (cx : FnCtx) : FnCtx :=
  ⟨checkedConfig cx.cfg, checkedFunction cx.fn⟩

theorem checked_blocks (function : Func) (block : BlockId) :
    (checkedFunction function).blocks[block]? = (function.blocks[block]?).map checkedBlock := by
  simp [checkedFunction]

theorem checked_funcs (m : GIR.Module) (function : FnId) :
    (checkedModule m).funcs[function]? = (m.funcs[function]?).map checkedFunction := by
  simp [checkedModule]

theorem checked_instAt (function : Func) (point : Pt) :
    instAt (checkedFunction function) point = (instAt function point).map checkedInst := by
  simp only [instAt, checked_blocks]
  cases blockAt : function.blocks[point.1]? <;> simp [checkedBlock]

theorem checked_instsAt (function : Func) (point : Pt) :
    instsAt (checkedFunction function) point = (instsAt function point).map checkedInst := by
  simp only [instsAt, checked_blocks]
  cases blockAt : function.blocks[point.1]? <;> simp [checkedBlock, List.map_drop]

theorem checked_enterBlock (function : Func) (fr : Frame) (block : BlockId) (args : List RVal) :
    Goose.GIR.enterBlock (checkedFunction function) fr block args = (do
      let (insts, next) ← Goose.GIR.enterBlock function fr block args
      pure (insts.map checkedInst, next)) := by
  funext state
  simp only [Goose.GIR.enterBlock, checked_blocks]
  cases blockAt : function.blocks[block]? with
  | none => simp [fault, M.stop, bind, M.bind']
  | some body =>
    simp only [Option.map_some, checkedBlock]
    by_cases arity : body.params.length = args.length
    · simp only [arity, ↓reduceIte, bind_apply]
      cases Goose.GIR.bindParams fr body.params args state <;> rfl
    · simp [arity, fault, M.stop, bind, M.bind']

theorem checked_lookupFn (cfg : GCfg) (function : FnId) :
    lookupFn (checkedConfig cfg) function = (do
      let fn ← lookupFn cfg function
      pure (checkedFunction fn)) := by
  funext state
  simp only [lookupFn, checkedConfig, checked_funcs]
  cases cfg.mod.funcs[function]? <;> rfl

theorem checked_lookupInit (cfg : GCfg) (global : GlobalId) :
    lookupInit (checkedConfig cfg) global = (do
      let fn ← lookupInit cfg global
      pure (checkedFunction fn)) := by
  funext state
  simp only [lookupInit, checkedConfig, checkedModule, Array.getElem?_map]
  cases cfg.mod.globals[global]? <;> rfl

theorem checked_slots (function : Func) : (checkedFunction function).slots = function.slots := rfl

theorem checked_releaseSlots (function : Func) (act : ActId) (scope : ScopeId) (scopeInstance : ScopeInst)
    (count : Nat) (store : Store) :
    releaseSlots (checkedFunction function) act scope scopeInstance count store =
      releaseSlots function act scope scopeInstance count store := by
  induction count generalizing store with
  | zero => rfl
  | succ count ih =>
    simp only [releaseSlots, checked_slots]
    cases function.slots[count]? <;> exact ih _

theorem checked_releaseScope (function : Func) (act : ActId) (scope : ScopeId) (scopeInstance : ScopeInst) :
    Goose.GIR.releaseScope (checkedFunction function) act scope scopeInstance =
      Goose.GIR.releaseScope function act scope scopeInstance := by
  funext state
  unfold Goose.GIR.releaseScope
  change Res.ok () { state with store := releaseSlots (checkedFunction function) act scope scopeInstance function.slots.size state.store } =
    Res.ok () { state with store := releaseSlots function act scope scopeInstance function.slots.size state.store }
  rw [checked_releaseSlots]

theorem checked_execEff (function : Func) (fr : Frame) (effect : Effect) :
    execEff (checkedFunction function) fr effect = execEff function fr effect := by
  cases effect <;> try rfl
  case leave scope =>
    simp only [execEff]
    cases fr.scopes with
    | nil => rfl
    | cons top rest =>
      rcases top with ⟨entered, scopeInstance⟩
      by_cases matching : entered = scope
      · simp only [matching, ↓reduceIte, checked_releaseScope]
      · simp only [matching, ↓reduceIte]

theorem checked_execPure {cx : FnCtx} {fr : Frame} {op : Op}
    (index : ∀ view offset, op = .indexProven view offset →
      execPure cx fr (.indexProven view offset) = execPure cx fr (.indexChecked view offset none)) :
    execPure (checkedContext cx) fr (checkedOp op) = execPure cx fr op := by
  cases op <;> try rfl
  case indexProven view offset => exact (index view offset rfl).symm

end Goose.Proofs.Bounds
