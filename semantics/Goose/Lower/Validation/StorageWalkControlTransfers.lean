import Goose.Lower.Validation.StorageWalkControlTransfersEmission

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem StorageWalkConfiguration.unwindTerm {slots : Array Slot}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (config : StorageWalkConfiguration slots entry exit before) (depth : Nat) (term : Term) (env : LEnv)
    (trace : StorageWalkTrace slots (before.stack.drop (before.stack.length - depth)) [.term term]
      (before.stack.drop (before.stack.length - depth)))
    (targets : ScopeTermTargets entry (before.stack.drop (before.stack.length - depth)) term)
    (bounds : ∀ target ∈ term.successors, target < before.blocks.size) :
    StorageWalkConfiguration slots entry (scopeExitUpdate before.cur (before.stack.drop (before.stack.length - depth)) exit)
      ((Goose.Lower.leaveTo depth >>= fun _ => Goose.Lower.emitTerm term) env before).2 := by
  refine ⟨?_, currentOpen_emitTerm _ term env, ?_, config.edges.unwindTerm config.openCurrent depth term env targets⟩
  · cases live : before.cur with
    | none =>
      have same : scopeExitUpdate none (before.stack.drop (before.stack.length - depth)) exit = exit := by
        funext block
        simp [scopeExitUpdate]
      rw [same]
      simpa only [bind_run, leaveTo_none _ _ _ live, emitTerm_none _ _ live] using config.builder
    | some block =>
      have bound := config.openCurrent.bound block live
      let body := before.blocks[block]
      have row : before.blocks[block]? = some body := Array.getElem?_eq_some_iff.mpr ⟨bound, rfl⟩
      have result := config.builder.unwindTerm depth term trace env block body live row
      have same : (fun other => if other = block then before.stack.drop (before.stack.length - depth) else exit other) =
          scopeExitUpdate before.cur (before.stack.drop (before.stack.length - depth)) exit := by
        funext other
        simp [scopeExitUpdate, live, eq_comm]
      simpa only [same, live] using result
  · apply (config.bounded.leaveTo depth env before).emitTerm term _ env
    intro target member
    rw [leaveTo_size]
    exact bounds target member

theorem StorageWalkConfiguration.unwindNext {slots : Array Slot}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (config : StorageWalkConfiguration slots entry exit before) (depth : Nat) (type : IntTy)
    (counter : ValueId) (header : BlockId) (env : LEnv)
    (target : entry header = before.stack.drop (before.stack.length - depth))
    (bound : header < before.blocks.size) :
    StorageWalkConfiguration slots entry (scopeExitUpdate before.cur (before.stack.drop (before.stack.length - depth)) exit)
      (Goose.Lower.Validation.unwindNext depth type counter header env before).2 := by
  refine ⟨config.builder.unwindNext depth type counter header env, currentOpen_emitTerm _ _ env, ?_,
    config.edges.unwindNext config.openCurrent depth type counter header env target⟩
  apply ((config.bounded.leaveTo depth env before).emitDef (.next type counter) env).emitTerm _ _ env
  intro destination member
  have same : destination = header := by simpa [Term.successors] using member
  subst destination
  rw [emitDef_size, leaveTo_size]
  exact bound

theorem StorageWalkAction.unwindReturn (slots : Array Slot) (stack : List ScopeId)
    (loop : Option LoopCtx) (values : List ValueId) (origin : Option OriginId) :
    StorageWalkAction slots stack loop (do Goose.Lower.leaveTo 0; Goose.Lower.emitTerm (.ret values origin)) := by
  refine ⟨AdvB.bind (advB_leaveTo 0) (fun _ => advB_emitTerm (.ret values origin)), ?_⟩
  intro env before entry exit config context stackEq
  have trace : StorageWalkTrace slots (before.stack.drop (before.stack.length - 0)) [.term (.ret values origin)]
      (before.stack.drop (before.stack.length - 0)) := by
    simp only [Nat.sub_zero, List.drop_length]
    exact .ret (.nil [])
  have afterConfig := config.unwindTerm 0 (.ret values origin) env trace
    (by intro target member; simp [Term.successors] at member)
    (by intro target member; simp [Term.successors] at member)
  exact ⟨entry, _, afterConfig, scopeCurrent_mapAdvance before entry exit _⟩

theorem StorageWalkAction.break (slots : Array Slot) (stack : List ScopeId)
    (loop : LoopCtx) (origin : OriginId) :
    StorageWalkAction slots stack (some loop) (lowerStmt (some loop) (.brk origin)) := by
  refine ⟨AdvB.bind (advB_leaveTo loop.depth) (fun _ => advB_emitTerm (.br loop.breakTo [])), ?_⟩
  intro env before entry exit config context stackEq
  have targets : ScopeLoopTargets loop entry before.stack before.blocks.size := context
  have afterConfig := config.unwindTerm loop.depth (.br loop.breakTo []) env (.neutral rfl trivial (.nil _))
    targets.breakTerm (by
      intro target member
      have same : target = loop.breakTo := by simpa [Term.successors] using member
      subst target
      exact targets.breakBound)
  exact ⟨entry, _, afterConfig, scopeCurrent_mapAdvance before entry exit _⟩

theorem StorageWalkAction.continue (slots : Array Slot) (stack : List ScopeId)
    (loop : LoopCtx) (origin : OriginId) :
    StorageWalkAction slots stack (some loop) (lowerStmt (some loop) (.cont origin)) := by
  cases continued : loop.cont with
  | jump header =>
    refine ⟨?_, ?_⟩
    · simpa only [lowerStmt, continued] using (AdvB.bind (advB_leaveTo loop.depth) (fun _ => advB_emitTerm (.br header [])))
    · intro env before entry exit config context stackEq
      have targets : ScopeLoopTargets loop entry before.stack before.blocks.size := context
      have stack : entry header = before.stack.drop (before.stack.length - loop.depth) := by
        simpa only [continued] using targets.continueStack
      have bound : header < before.blocks.size := by simpa only [continued] using targets.continueBound
      have afterConfig := config.unwindTerm loop.depth (.br header []) env (.neutral rfl trivial (.nil _))
        (by
          intro target member
          have same : target = header := by simpa [Term.successors] using member
          subst target
          exact stack)
        (by
          intro target member
          have same : target = header := by simpa [Term.successors] using member
          subst target
          exact bound)
      refine ⟨entry, scopeExitUpdate before.cur (before.stack.drop (before.stack.length - loop.depth)) exit,
        ?_, scopeCurrent_mapAdvance before entry exit _⟩
      simpa only [lowerStmt, continued] using afterConfig
  | next header type counter =>
    refine ⟨?_, ?_⟩
    · simpa only [lowerStmt, continued, Goose.Lower.Validation.unwindNext] using
        (AdvB.bind (advB_leaveTo loop.depth) (fun _ => AdvB.bind (advB_emitDef (.next type counter)) (fun next => advB_emitTerm (.br header [next]))))
    · intro env before entry exit config context stackEq
      have targets : ScopeLoopTargets loop entry before.stack before.blocks.size := context
      have stack : entry header = before.stack.drop (before.stack.length - loop.depth) := by
        simpa only [continued] using targets.continueStack
      have bound : header < before.blocks.size := by simpa only [continued] using targets.continueBound
      have afterConfig := config.unwindNext loop.depth type counter header env stack bound
      refine ⟨entry, scopeExitUpdate before.cur (before.stack.drop (before.stack.length - loop.depth)) exit,
        ?_, scopeCurrent_mapAdvance before entry exit _⟩
      simpa only [lowerStmt, continued, Goose.Lower.Validation.unwindNext] using afterConfig


theorem StorageWalkAction.emitReturn (slots : Array Slot)
    (loop : Option LoopCtx) (values : List ValueId) (origin : Option OriginId) :
    StorageWalkAction slots [] loop (Goose.Lower.emitTerm (.ret values origin)) := by
  refine ⟨advB_emitTerm _, ?_⟩
  intro env before entry exit config context stackEq
  have unwound := (StorageWalkAction.unwindReturn slots [] loop values origin).preserves
    env before entry exit config context stackEq
  simpa only [bind_run, leaveTo, get_apply, stackEq, List.length_nil, Nat.sub_self,
    List.take_zero, leaveAll, pure_run] using unwound

#print axioms StorageWalkConfiguration.unwindTerm
#print axioms StorageWalkConfiguration.unwindNext
#print axioms StorageWalkAction.unwindReturn
#print axioms StorageWalkAction.break
#print axioms StorageWalkAction.continue
#print axioms StorageWalkAction.emitReturn

end Goose.Lower.Validation
