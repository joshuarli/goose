import Goose.Lower.Validation.StorageWalkControlLoops

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem StorageWalkAction.rangeHeader {slots : Array Slot} {stack : List ScopeId}
    {loop : Option LoopCtx} (type : IntTy) (lower upper : ValueId)
    (body : BlockId → ValueId → Nat → BlockId → B ValueId)
    (bodyAction : ∀ header counter depth target, StorageWalkAction slots stack
      (some ⟨depth, target, .next header type counter⟩) (body header counter depth target)) :
    StorageWalkAction slots stack loop (do
      let (header, params) ← Goose.Lower.newBlock [.data (.int type)]
      let counter := params.headD 0
      Goose.Lower.emitTerm (.br header [lower])
      Goose.Lower.setCur (some header)
      Goose.Lower.lowerRange type counter upper header (body header counter)) := by
  apply StorageWalkAction.header [.data (.int type)] [lower] (advB_newBlock1 _)
    (fun header params => Goose.Lower.lowerRange type (params.headD 0) upper header (body header (params.headD 0)))
    (fun header params => advB_lowerRange type (params.headD 0) upper header
      (fun depth target => (bodyAction header (params.headD 0) depth target).advance))
  intro header params env before entry exit config context stackEq live target bound result after run
  let counter := params.headD 0
  have current : (Goose.Lower.emitDef (.cmp .lt type counter upper) env before).2.cur = some header :=
    (emitDef_current _ _ _).trans live
  have equality := scope_loopCondition_live (.next header type counter)
    (Goose.Lower.emitDef (.cmp .lt type counter upper)) (body header counter) env before header current
  apply storageWalk_loopCondition_flow (.next header type counter) (StorageWalkAction.emitDef slots stack none (.cmp .lt type counter upper) (fun _ => trivial))
    (body header counter) (bodyAction header counter) env before entry exit config stackEq target bound
  exact equality.trans run


#print axioms StorageWalkAction.rangeHeader

end Goose.Lower.Validation
