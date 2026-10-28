import Goose.Lower.DemandScalarPlaceAddress

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_field_scalar_address {cfg : Cfg} {env : Env} {state : St} {place : Place} {index : Nat}
    (source : PlaceSource cfg env (.field place index) state) (form : ScalarReadPlace place)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root source.path
      (.place (.field place index)) before)
    {required : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    {initial : GIR.Frame} {start : Pt} (atPoint : before.pp = some start) (related : Rel cfg env cx initial before)
    (extended : ExtT (lowerPlace (.field place index) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks) :
    ∃ (location : Loc) (middle final : DemandRuntimePoint),
      evalPlace 2 cfg env (.field place index) state = .ok { location with path := location.path ++ [index] } state ∧
      middle.state = state ∧ final.state = state ∧
      Post cfg env cx before initial (lowerPlace place (lowerEnv cfg.mod env.vars results) before).2
        middle.frame middle.point [((lowerPlace place (lowerEnv cfg.mod env.vars results) before).1, .val (.ref location))] ∧
      (∀ fuel, DemandInstructionStep cx fuel ⟨start, initial, state⟩ middle) ∧
      (∀ fuel, DemandInstructionStep cx fuel middle final) ∧
      Post cfg env cx before initial (lowerPlace (.field place index) (lowerEnv cfg.mod env.vars results) before).2
        final.frame final.point [((lowerPlace (.field place index) (lowerEnv cfg.mod env.vars results) before).1,
          .val (.ref { location with path := location.path ++ [index] }))] := by
  let le := lowerEnv cfg.mod env.vars results
  let owner := lowerPlace place le before
  let built := lowerPlace (.field place index) le before
  have emitted : emitDef (.fieldAddr owner.1 index) le owner.2 = built := by rfl
  have ownerExtended : ExtT owner.2 cx.fn.blocks := extended.of_adv (adv_emitDef emitted)
  obtain ⟨child, typing, roots, path, world⟩ := source.fieldChild index
  have childOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn le root child.path (.place place) before := by
    rw [path]
    exact .first occurrence (.place rfl)
  have childRows : GeneratedDemandRows cfg.mod child.rootsEnv.access childOccurrence required := by
    have inherited : GeneratedDemandRows cfg.mod source.rootsEnv.access (.first occurrence (.place rfl)) required := .first (first := .place rfl) rows
    simpa only [roots, path] using inherited
  obtain ⟨location, placed, ownerPost, ownerStep⟩ := accepted_generated_scalar_place_address child form
    childOccurrence childRows atPoint related ownerExtended
  change Post cfg env cx before initial owner.2 (initial.set owner.1 (.val (.ref location)))
    (start.1, start.2 + 1) [(owner.1, .val (.ref location))] at ownerPost
  obtain ⟨fieldPost, fieldInst⟩ := Post.def_leaf ownerPost emitted extended
    (.val (.ref { location with path := location.path ++ [index] }))
  let middle : DemandRuntimePoint := ⟨(start.1, start.2 + 1), initial.set owner.1 (.val (.ref location)), state⟩
  let final : DemandRuntimePoint := ⟨((start.1, start.2 + 1).1, (start.1, start.2 + 1).2 + 1),
    middle.frame.set built.1 (.val (.ref { location with path := location.path ++ [index] })), state⟩
  refine ⟨location, middle, final, ?_, rfl, rfl, ownerPost, ownerStep, ?_, fieldPost⟩
  · simp only [evalPlace, bind_apply, placed, pure_apply]
  · intro fuel
    apply DemandInstructionStep.definition fieldInst
    have cell := ownerPost.has (owner.1, .val (.ref location)) (by simp)
    have read := getVal_of cell
    simp only [execOp, execPure, read, expectRef, bind_apply, pure_apply]

#print axioms PlaceSource.fieldChild
#print axioms accepted_generated_field_scalar_address
end Goose.Lower
