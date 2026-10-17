import Goose.Lower.Validation.ScopeFinish
import Goose.Lower.Validation.CfgCurrentOpen
import Goose.Lower.Validation.CfgTargetBounds

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def ScopeEdges (entry exit : BlockId → List ScopeId) (state : LS) : Prop :=
  ∀ block body, state.blocks[block]? = some body →
    ∀ target ∈ (cfgBlock body).terms.flatMap Term.successors, entry target = exit block

def ScopeTermTargets (entry : BlockId → List ScopeId) (stack : List ScopeId) (term : Term) : Prop :=
  ∀ target ∈ term.successors, entry target = stack

theorem ScopeEdges.of_blocks {entry exit : BlockId → List ScopeId} {before after : LS}
    (edges : ScopeEdges entry exit before) (blocks : after.blocks = before.blocks) :
    ScopeEdges entry exit after := by
  intro block body lookup
  rw [blocks] at lookup
  exact edges block body lookup

theorem ScopeEdges.modify {entry exit : BlockId → List ScopeId} {before : LS}
    (edges : ScopeEdges entry exit before) (block : BlockId) (update : BlockB → BlockB)
    (newTargets : ∀ body, before.blocks[block]? = some body →
      ∀ target ∈ (cfgBlock (update body)).terms.flatMap Term.successors, entry target = exit block) :
    ScopeEdges entry exit { before with blocks := before.blocks.modify block update } := by
  intro other body lookup target member
  simp only [Array.getElem?_modify] at lookup
  by_cases same : block = other
  · subst other
    simp only [ite_true] at lookup
    cases oldLookup : before.blocks[block]? with
    | none => simp [oldLookup] at lookup
    | some oldBody =>
      simp only [oldLookup, Option.map_some, Option.some.injEq] at lookup
      subst body
      exact newTargets oldBody oldLookup target member
  · simp only [same, ite_false] at lookup
    exact edges other body lookup target member

theorem ScopeEdges.pushInst {entry exit : BlockId → List ScopeId} {before : LS}
    (edges : ScopeEdges entry exit before) (block : BlockId) (inst : Inst) (env : LEnv)
    (newTargets : ∀ term, inst = .term term → ScopeTermTargets entry (exit block) term) :
    ScopeEdges entry exit (pushInst block inst env before).2 := by
  apply edges.modify block (fun body => { body with insts := body.insts.push inst })
  intro body lookup target member
  simp only [cfgBlock, Array.toList_push, GIR.Block.terms, List.filterMap_append,
    List.flatMap_append, List.mem_append] at member
  rcases member with old | fresh
  · exact edges block body lookup target old
  · cases inst with
    | «def» value op => simp [Inst.term?] at fresh
    | eff effect => simp [Inst.term?] at fresh
    | term term =>
      simp only [List.filterMap_cons, List.filterMap_nil, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, Inst.term?] at fresh
      exact newTargets term rfl target fresh

theorem ScopeEdges.emitDef {entry exit : BlockId → List ScopeId} {before : LS}
    (edges : ScopeEdges entry exit before) (op : Op) (env : LEnv) :
    ScopeEdges entry exit (emitDef op env before).2 := by
  cases live : before.cur with
  | none => simpa only [emitDef_none _ _ live] using edges
  | some block =>
    rw [emitDef_run _ _ live]
    exact edges.pushInst block (.def before.vals.size op) env (by intro term impossible; cases impossible)

theorem ScopeEdges.emitEffect {entry exit : BlockId → List ScopeId} {before : LS}
    (edges : ScopeEdges entry exit before) (effect : Effect) (env : LEnv) :
    ScopeEdges entry exit (emitEffect effect env before).2 := by
  cases live : before.cur with
  | none => simpa only [emitEffect_none _ _ live] using edges
  | some block =>
    rw [emitEffect_run _ _ live]
    exact edges.pushInst block (.eff effect) env (by intro term impossible; cases impossible)

theorem ScopeEdges.emitTerm {entry exit : BlockId → List ScopeId} {before : LS}
    (edges : ScopeEdges entry exit before) (term : Term) (env : LEnv)
    (newTargets : ∀ block, before.cur = some block → ScopeTermTargets entry (exit block) term) :
    ScopeEdges entry exit (emitTerm term env before).2 := by
  cases live : before.cur with
  | none => simpa only [emitTerm_none _ _ live] using edges
  | some block =>
    rw [emitTerm_run _ _ live]
    exact edges.pushInst block (.term term) env (by intro other same; cases same; exact newTargets block live)

theorem ScopeEdges.patchTerm {entry exit : BlockId → List ScopeId} {before : LS}
    (edges : ScopeEdges entry exit before) (block : BlockId) (term : Term) (env : LEnv)
    (newTargets : ScopeTermTargets entry (exit block) term) :
    ScopeEdges entry exit (patchTerm block term env before).2 :=
  edges.pushInst block (.term term) env (by intro other same; cases same; exact newTargets)

theorem ScopeEdges.changeCurrentExit {entry exit : BlockId → List ScopeId} {before : LS}
    (edges : ScopeEdges entry exit before) (openCurrent : CurrentOpen before) (stack : List ScopeId) :
    ScopeEdges entry (scopeExitUpdate before.cur stack exit) before := by
  intro block body lookup target member
  by_cases current : before.cur = some block
  · have empty := openCurrent.row current lookup
    change (cfgBlock body).terms = [] at empty
    rw [empty] at member
    cases member
  · simpa only [scopeExitUpdate, current, ite_false] using edges block body lookup target member

theorem ScopeEdges.newBlock {entry exit : BlockId → List ScopeId} {before : LS}
    (edges : ScopeEdges entry exit before) (bounded : TargetsBounded before)
    (env : LEnv) (types : List VTy) :
    ScopeEdges
      (fun block => if block = before.blocks.size then before.stack else entry block)
      (fun block => if block = before.blocks.size then before.stack else exit block)
      (newBlock types env before).2 := by
  rw [scope_newBlock_run]
  intro block body lookup target member
  simp only [Array.getElem?_push] at lookup
  by_cases fresh : block = before.blocks.size
  · simp only [fresh, ite_true, Option.some.injEq] at lookup
    subst body
    simp [cfgBlock, GIR.Block.terms] at member
  · simp only [fresh, ite_false] at lookup
    have targetBound := bounded block body lookup target member
    have targetOld : target ≠ before.blocks.size := Nat.ne_of_lt targetBound
    simpa only [fresh, targetOld, ite_false] using edges block body lookup target member

structure ScopeLoopTargets (loop : LoopCtx) (entry : BlockId → List ScopeId)
    (stack : List ScopeId) (blocks : Nat) : Prop where
  depth : loop.depth ≤ stack.length
  breakBound : loop.breakTo < blocks
  breakStack : entry loop.breakTo = stack.drop (stack.length - loop.depth)
  continueBound : (match loop.cont with | .jump header | .next header _ _ => header) < blocks
  continueStack : entry (match loop.cont with | .jump header | .next header _ _ => header) =
    stack.drop (stack.length - loop.depth)

theorem ScopeLoopTargets.enter {loop : LoopCtx} {entry : BlockId → List ScopeId}
    {stack : List ScopeId} {blocks : Nat} (targets : ScopeLoopTargets loop entry stack blocks)
    (scope : ScopeId) : ScopeLoopTargets loop entry (scope :: stack) blocks := by
  have drop : (scope :: stack).drop ((scope :: stack).length - loop.depth) =
      stack.drop (stack.length - loop.depth) := by
    have subtraction : (scope :: stack).length - loop.depth = (stack.length - loop.depth) + 1 := by
      have depth := targets.depth
      simp only [List.length_cons]
      omega
    rw [subtraction, List.drop_succ_cons]
  exact ⟨by have depth := targets.depth; simp only [List.length_cons]; omega,
    targets.breakBound, by rw [drop]; exact targets.breakStack,
    targets.continueBound, by rw [drop]; exact targets.continueStack⟩

theorem ScopeLoopTargets.advance {loop : LoopCtx} {entry exit nextEntry nextExit : BlockId → List ScopeId}
    {before after : LS} (targets : ScopeLoopTargets loop entry before.stack before.blocks.size)
    (advance : before.Adv after) (maps : ScopeMapAdvance before entry exit nextEntry nextExit) :
    ScopeLoopTargets loop nextEntry after.stack after.blocks.size := by
  rw [advance.stack]
  refine ⟨targets.depth, Nat.lt_of_lt_of_le targets.breakBound advance.ext.1, ?_,
    Nat.lt_of_lt_of_le targets.continueBound advance.ext.1, ?_⟩
  · rw [(maps _ targets.breakBound).1]
    exact targets.breakStack
  · rw [(maps _ targets.continueBound).1]
    exact targets.continueStack

theorem ScopeEdges.enterScope {entry exit : BlockId → List ScopeId} {before : LS}
    (edges : ScopeEdges entry exit before) (openCurrent : CurrentOpen before)
    (scope : ScopeId) (env : LEnv) :
    ScopeEdges entry (scopeExitUpdate before.cur (scope :: before.stack) exit)
      (Goose.Lower.Validation.enterScope scope env before).2 := by
  have entered := (edges.changeCurrentExit openCurrent (scope :: before.stack)).emitEffect (.enter scope) env
  simp only [Goose.Lower.Validation.enterScope, bind_run, pushScope_run]
  exact entered.of_blocks rfl

theorem ScopeEdges.leaveScope {entry exit : BlockId → List ScopeId} {before : LS}
    (edges : ScopeEdges entry exit before) (openCurrent : CurrentOpen before)
    (scope : ScopeId) (rest : List ScopeId) (env : LEnv) :
    ScopeEdges entry (scopeExitUpdate before.cur rest exit)
      (Goose.Lower.Validation.leaveScope scope env before).2 := by
  have left := (edges.changeCurrentExit openCurrent rest).emitEffect (.leave scope) env
  simp only [Goose.Lower.Validation.leaveScope, bind_run, popScope_run]
  exact left.of_blocks rfl

theorem ScopeEdges.leaveAll {entry exit : BlockId → List ScopeId}
    (scopes : List ScopeId) (env : LEnv) (before : LS) (edges : ScopeEdges entry exit before) :
    ScopeEdges entry exit (Goose.Lower.leaveAll scopes env before).2 := by
  induction scopes generalizing before with
  | nil => exact edges
  | cons scope scopes ih =>
    simp only [Goose.Lower.leaveAll, bind_run]
    exact ih _ (edges.emitEffect (.leave scope) env)

theorem ScopeEdges.leaveTo {entry exit : BlockId → List ScopeId}
    (depth : Nat) (env : LEnv) (before : LS) (edges : ScopeEdges entry exit before) :
    ScopeEdges entry exit (Goose.Lower.leaveTo depth env before).2 := by
  simpa only [Goose.Lower.leaveTo, bind_run, get_apply] using
    edges.leaveAll (before.stack.take (before.stack.length - depth)) env before

theorem ScopeEdges.unwindTerm {entry exit : BlockId → List ScopeId} {before : LS}
    (edges : ScopeEdges entry exit before) (openCurrent : CurrentOpen before)
    (depth : Nat) (term : Term) (env : LEnv)
    (targets : ScopeTermTargets entry (before.stack.drop (before.stack.length - depth)) term) :
    ScopeEdges entry (scopeExitUpdate before.cur (before.stack.drop (before.stack.length - depth)) exit)
      ((Goose.Lower.leaveTo depth >>= fun _ => Goose.Lower.emitTerm term) env before).2 := by
  have left := (edges.changeCurrentExit openCurrent
    (before.stack.drop (before.stack.length - depth))).leaveTo depth env before
  have closed := left.emitTerm term env (by
    intro block current
    have same : before.cur = some block := by
      have unchanged := leaveAll_cur (before.stack.take (before.stack.length - depth)) env before
      change (Goose.Lower.leaveTo depth env before).2.cur = before.cur at unchanged
      exact unchanged.symm.trans current
    simpa only [scopeExitUpdate, same, ite_true] using targets)
  exact closed

theorem ScopeEdges.unwindNext {entry exit : BlockId → List ScopeId} {before : LS}
    (edges : ScopeEdges entry exit before) (openCurrent : CurrentOpen before)
    (depth : Nat) (type : IntTy) (counter : ValueId) (header : BlockId) (env : LEnv)
    (target : entry header = before.stack.drop (before.stack.length - depth)) :
    ScopeEdges entry (scopeExitUpdate before.cur (before.stack.drop (before.stack.length - depth)) exit)
      (Goose.Lower.Validation.unwindNext depth type counter header env before).2 := by
  have left := (edges.changeCurrentExit openCurrent
    (before.stack.drop (before.stack.length - depth))).leaveTo depth env before
  have defined := left.emitDef (.next type counter) env
  have closed := defined.emitTerm
    (.br header [(Goose.Lower.emitDef (.next type counter) env (Goose.Lower.leaveTo depth env before).2).1]) env (by
      intro block current
      have first : (Goose.Lower.leaveTo depth env before).2.cur = before.cur :=
        leaveAll_cur _ env before
      have second : (Goose.Lower.emitDef (.next type counter) env
          (Goose.Lower.leaveTo depth env before).2).2.cur = (Goose.Lower.leaveTo depth env before).2.cur := by
        cases live : (Goose.Lower.leaveTo depth env before).2.cur with
        | none => rw [emitDef_none _ _ live]; exact live
        | some currentBlock => rw [emitDef_run _ _ live]; exact live
      have same : before.cur = some block := first.symm.trans (second.symm.trans current)
      intro destination member
      have destinationId : destination = header := by simpa [Term.successors] using member
      subst destination
      simpa only [scopeExitUpdate, same, ite_true] using target)
  exact closed

theorem ScopeAction.preservesLoopTargets {parents : Array (Option ScopeId)} {parent : Option ScopeId}
    {action : B α} (actionProof : ScopeAction parents parent action)
    (env : LEnv) (before : LS) (entry exit : BlockId → List ScopeId)
    (valid : ScopeBuilder parents entry exit before) (bound : ScopeLiveBound before)
    (head : before.stack.head? = parent) (loop : LoopCtx)
    (targets : ScopeLoopTargets loop entry before.stack before.blocks.size) :
    ∃ nextEntry nextExit, ScopeBuilder parents nextEntry nextExit (action env before).2 ∧
      ScopeMapAdvance before entry exit nextEntry nextExit ∧
      ScopeLoopTargets loop nextEntry (action env before).2.stack (action env before).2.blocks.size := by
  obtain ⟨nextEntry, nextExit, afterValid, maps⟩ := actionProof.preserves env before entry exit valid bound head
  exact ⟨nextEntry, nextExit, afterValid, maps, targets.advance (actionProof.advance env before _ _ rfl) maps⟩

theorem ScopeLoopTargets.breakTerm {loop : LoopCtx} {entry : BlockId → List ScopeId}
    {stack : List ScopeId} {blocks : Nat} (targets : ScopeLoopTargets loop entry stack blocks) :
    ScopeTermTargets entry (stack.drop (stack.length - loop.depth)) (.br loop.breakTo []) := by
  intro destination member
  have same : destination = loop.breakTo := by simpa [Term.successors] using member
  subst destination
  exact targets.breakStack

theorem ScopeEdges.lowerStmt_break {entry exit : BlockId → List ScopeId} {before : LS}
    (edges : ScopeEdges entry exit before) (openCurrent : CurrentOpen before)
    (loop : LoopCtx) (env : LEnv) (origin : OriginId)
    (targets : ScopeLoopTargets loop entry before.stack before.blocks.size) :
    ScopeEdges entry (scopeExitUpdate before.cur (before.stack.drop (before.stack.length - loop.depth)) exit)
      (lowerStmt (some loop) (.brk origin) env before).2 :=
  edges.unwindTerm openCurrent loop.depth (.br loop.breakTo []) env targets.breakTerm

theorem ScopeEdges.lowerStmt_continue {entry exit : BlockId → List ScopeId} {before : LS}
    (edges : ScopeEdges entry exit before) (openCurrent : CurrentOpen before)
    (loop : LoopCtx) (env : LEnv) (origin : OriginId)
    (targets : ScopeLoopTargets loop entry before.stack before.blocks.size) :
    ScopeEdges entry (scopeExitUpdate before.cur (before.stack.drop (before.stack.length - loop.depth)) exit)
      (lowerStmt (some loop) (.cont origin) env before).2 := by
  cases continued : loop.cont with
  | jump header =>
    have stack : entry header = before.stack.drop (before.stack.length - loop.depth) := by
      simpa only [continued] using targets.continueStack
    have result := edges.unwindTerm openCurrent loop.depth (.br header []) env (by
      intro destination member
      have same : destination = header := by simpa [Term.successors] using member
      subst destination
      exact stack)
    simpa only [lowerStmt, continued] using result
  | next header type counter =>
    have stack : entry header = before.stack.drop (before.stack.length - loop.depth) := by
      simpa only [continued] using targets.continueStack
    simpa only [lowerStmt, continued, Goose.Lower.Validation.unwindNext] using
      edges.unwindNext openCurrent loop.depth type counter header env stack

end Goose.Lower.Validation
