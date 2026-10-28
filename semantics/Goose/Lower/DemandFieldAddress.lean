import Goose.Lower.DemandScalarPlaceAddress

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem generated_global_field_address {cfg : Cfg} {env : Env} {state : St} {cx : FnCtx} {results : List Ty}
    {before : LS} {initial : GIR.Frame} {start : Pt} (global : GlobalId) (field : Nat)
    (atPoint : before.pp = some start) (related : Rel cfg env cx initial before)
    (extended : ExtT (lowerPlace (.field (.global global) field) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks) :
    ∃ middle final : DemandRuntimePoint,
      evalPlace 2 cfg env (.field (.global global) field) state = .ok ⟨.global global, [field]⟩ state ∧
      (∀ fuel, DemandInstructionStep cx fuel ⟨start, initial, state⟩ middle) ∧
      (∀ fuel, DemandInstructionStep cx fuel middle final) ∧
      Post cfg env cx before initial (lowerPlace (.field (.global global) field) (lowerEnv cfg.mod env.vars results) before).2
        final.frame final.point [((lowerPlace (.field (.global global) field) (lowerEnv cfg.mod env.vars results) before).1,
          .val (.ref ⟨.global global, [field]⟩))] := by
  let le := lowerEnv cfg.mod env.vars results
  let owner := lowerPlace (.global global) le before
  let built := lowerPlace (.field (.global global) field) le before
  have emitted : emitDef (.fieldAddr owner.1 field) le owner.2 = built := by rfl
  have ownerExtended : ExtT owner.2 cx.fn.blocks := extended.of_adv (adv_emitDef emitted)
  obtain ⟨ownerPost, ownerInst⟩ := Post.def_leaf (Post.init related atPoint)
    (show emitDef (.globalAddr global) le before = owner from rfl) ownerExtended (.val (.ref ⟨.global global, []⟩))
  change Post cfg env cx before initial owner.2 (initial.set owner.1 (.val (.ref ⟨.global global, []⟩)))
    (start.1, start.2 + 1) [(owner.1, .val (.ref ⟨.global global, []⟩))] at ownerPost
  obtain ⟨fieldPost, fieldInst⟩ := Post.def_leaf ownerPost emitted extended (.val (.ref ⟨.global global, [field]⟩))
  let middle : DemandRuntimePoint := ⟨(start.1, start.2 + 1), initial.set owner.1 (.val (.ref ⟨.global global, []⟩)), state⟩
  let final : DemandRuntimePoint := ⟨((start.1, start.2 + 1).1, (start.1, start.2 + 1).2 + 1),
    middle.frame.set built.1 (.val (.ref ⟨.global global, [field]⟩)), state⟩
  refine ⟨middle, final, ?_, ?_, ?_, fieldPost⟩
  · simp [evalPlace, bind_apply, pure_apply]
  · intro fuel
    apply DemandInstructionStep.definition ownerInst
    simp only [execOp, execPure, pure_apply]
  · intro fuel
    apply DemandInstructionStep.definition fieldInst
    have cell := ownerPost.has (owner.1, .val (.ref ⟨.global global, []⟩)) (by simp)
    have read := getVal_of cell
    simp only [execOp, execPure, read, expectRef, bind_apply, pure_apply, List.nil_append]

#print axioms generated_global_field_address
end Goose.Lower
