import Goose.Lower.Validation.StorageWalkControlLoops

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem StorageWalkAction.eachHeader {slots : Array Slot} {stack : List ScopeId}
    {loop : Option LoopCtx} (regrow : Bool) (owner : Option ValueId) (sampled start : ValueId)
    (body : BlockId → ValueId → Nat → BlockId → B ValueId)
    (bodyAction : ∀ header counter depth target, StorageWalkAction slots stack
      (some ⟨depth, target, .next header .i64 counter⟩) (body header counter depth target)) :
    StorageWalkAction slots stack loop (do
      let (header, params) ← Goose.Lower.newBlock [.data (.int .i64)]
      let counter := params.headD 0
      Goose.Lower.emitTerm (.br header [start])
      Goose.Lower.setCur (some header)
      Goose.Lower.lowerEach regrow owner sampled header counter (body header counter)) := by
  apply StorageWalkAction.header [.data (.int .i64)] [start] (advB_newBlock1 _)
    (fun header params => Goose.Lower.lowerEach regrow owner sampled header (params.headD 0) (body header (params.headD 0)))
    (fun header params => advB_lowerEach regrow owner sampled header (params.headD 0)
      (fun depth target => (bodyAction header (params.headD 0) depth target).advance))
  intro header params env before entry exit config context stackEq live target bound result after run
  let counter := params.headD 0
  let condition : B ValueId := do
    let length ← Goose.Lower.eachLen regrow owner sampled
    Goose.Lower.emitDef (.cmp .lt .i64 counter length)
  have sampledCurrent : (Goose.Lower.eachLen regrow owner sampled env before).2.cur = before.cur := by
    cases regrow
    · rfl
    · exact emitDef_current _ _ _
  have current : (condition env before).2.cur = some header := by
    simp only [condition, bind_run]
    exact (emitDef_current _ _ _).trans (sampledCurrent.trans live)
  have equality := scope_loopCondition_live (.next header .i64 counter) condition (body header counter)
    env before header current
  have conditionAction : StorageWalkAction slots stack none condition :=
    (StorageWalkAction.eachLen slots stack none regrow owner sampled).bind fun length =>
      StorageWalkAction.emitDef slots stack none (.cmp .lt .i64 counter length) (fun _ => trivial)
  apply storageWalk_loopCondition_flow (.next header .i64 counter) conditionAction (body header counter)
    (bodyAction header counter) env before entry exit config stackEq target bound
  apply equality.trans
  simpa only [condition, Goose.Lower.lowerEach, scopeLoopBack, scope_bind_assoc] using run


#print axioms StorageWalkAction.eachLen
#print axioms StorageWalkAction.eachHeader

end Goose.Lower.Validation
