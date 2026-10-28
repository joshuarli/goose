import Goose.Lower.DemandCallReferenceBorrow

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem generated_call_reference_borrow_demand {cfg : Cfg} {env : Env} {cx : FnCtx}
    {before middle : LS} {initial frame : GIR.Frame} {point : Pt} {state : St} {location : Loc} {id : ValueId}
    (post : Post cfg env cx before initial middle frame point [(id, .val (.ref location))])
    (mutability : Mutability) (le : LEnv)
    (extended : ExtT (borrowTo mutability id le middle).2 cx.fn.blocks)
    {world : World} {typing : TEnv} {roots : PEnv} {future : List VarId} {map : RetainedSsaMap}
    (sourceFrame : Frame cfg.mod world typing roots env state future)
    (bounded : map.Bounded before.vals.size)
    (realized : map.Realizes cfg.mod world env ⟨point, initial, state⟩) :
    ∃ length finalPoint finalFrame,
      DemandUniformTraversal cx
        (fun runtime => DemandFrameAt cfg env cx world typing roots future map.values map.runs runtime ∧
          Same before.vals.size initial runtime.frame) length
        ⟨point, frame, state⟩ ⟨finalPoint, finalFrame, state⟩ ∧
      Post cfg env cx before initial (borrowTo mutability id le middle).2 finalFrame finalPoint
        [((borrowTo mutability id le middle).1, .val (.ref location))] := by
  apply generated_call_reference_borrow_traversal post mutability le extended
    (fun runtime => DemandFrameAt cfg env cx world typing roots future map.values map.runs runtime ∧
      Same before.vals.size initial runtime.frame)
  intro built current currentPoint cells currentPost
  exact ⟨⟨⟨_, currentPost.pp, currentPost.rel⟩, sourceFrame,
    realized.retained currentPost.same bounded.1 bounded.2 RetainsAliases.refl⟩, currentPost.same⟩

#print axioms generated_call_reference_borrow_demand
end Goose.Lower
