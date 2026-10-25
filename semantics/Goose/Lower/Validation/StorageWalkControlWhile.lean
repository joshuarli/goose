import Goose.Lower.Validation.StorageWalkControlLoops

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem StorageWalkAction.whileHeader {slots : Array Slot} {stack : List ScopeId}
    {loop : Option LoopCtx} {condition : B ValueId}
    (conditionAction : StorageWalkAction slots stack none condition)
    (body : BlockId → Nat → BlockId → B ValueId)
    (bodyAction : ∀ header depth target, StorageWalkAction slots stack
      (some ⟨depth, target, .jump header⟩) (body header depth target)) :
    StorageWalkAction slots stack loop (do
      let (header, _) ← Goose.Lower.newBlock []
      Goose.Lower.emitTerm (.br header [])
      Goose.Lower.setCur (some header)
      Goose.Lower.lowerWhile header condition (body header)) := by
  apply StorageWalkAction.header [] [] advB_newBlock0 (fun header _ => Goose.Lower.lowerWhile header condition (body header))
    (fun header _ => advB_lowerWhile header conditionAction.advance (fun depth target => (bodyAction header depth target).advance))
  intro header params env before entry exit config context stackEq live target bound result after run
  apply storageWalk_loopCondition_flow (.jump header) conditionAction (body header) (bodyAction header)
    env before entry exit config stackEq target bound
  exact run


#print axioms StorageWalkAction.whileHeader

end Goose.Lower.Validation
