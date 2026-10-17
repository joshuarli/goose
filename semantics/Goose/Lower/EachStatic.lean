import Goose.Lower.EachTypedStatement

namespace Goose.Lower

open Goose.Core Goose.Core.Sound

def PlaceOwnerShape (cfg : Cfg) (results : List Ty) (place : Place) : Prop :=
  ∀ env state (source : PlaceSource cfg env place state) input output address block,
    lowerPlace place (lowerEnv cfg.mod env.vars results) input = (address, output) →
    GeneratedBuilderState input → output.cur = some block →
    ∃ mutability, output.vals[address]? = some (some (.data (.ref mutability source.ty)))

theorem eachSourceMode_of_live_place {cfg : Cfg} {env : Env} {state : St} {results : List Ty}
    {place : Place} (source : PlaceSource cfg env place state)
    (shape : PlaceOwnerShape cfg results place) {input output : LS}
    {owner : Option GIR.ValueId} {view : GIR.ValueId} {point : GIR.Pt}
    (lowered : lowerEachSource (.of place) (lowerEnv cfg.mod env.vars results) input = ((owner, view), output))
    (generated : GeneratedBuilderState input) (live : output.pp = some point) :
    (regrowOf owner (lowerEnv cfg.mod env.vars results) output).1 =
      eachSourceRegrows source.rootsEnv.access (.of place) := by
  have complete := lowered
  simp only [lowerEachSource, bind_eq] at complete
  obtain ⟨address, withOwner, placeAt, irView, withView, viewAt, resultAt⟩ := complete
  rw [pure_run] at resultAt
  obtain ⟨_, outputAt⟩ := Prod.mk.inj resultAt
  have ownerLive : ∃ block, withOwner.cur = some block := by
    cases curAt : withOwner.cur with
    | none =>
      rw [emitDef_none _ _ curAt] at viewAt
      obtain ⟨_, withViewAt⟩ := Prod.mk.inj viewAt
      have dead : output.cur = none := by rw [← outputAt, ← withViewAt]; exact curAt
      simp [LS.pp, dead] at live
    | some block => exact ⟨block, rfl⟩
  obtain ⟨block, liveOwner⟩ := ownerLive
  apply eachSourceMode_of_placeType source.rootsEnv.access
    (tyPlace_accessType (source.frame.mod_t.trans source.frame.mod_p.symm)
      (source.frame.vars_t.trans source.frame.vars_p.symm) source.typed) ?_ lowered
  intro result intermediate run
  have equal := Prod.mk.inj (run.symm.trans placeAt)
  obtain ⟨mutability, typed⟩ := shape env state source input withOwner address block placeAt generated liveOwner
  rw [equal.1, equal.2]
  exact ⟨mutability, block, typed, liveOwner⟩

theorem typedStatementLoopSimulation_each_place {n : Nat} {cfg : Cfg} {results : List Ty}
    {x : VarId} {idx : Option VarId} {place : Place} {byRef : Bool} {body : Block} {origin : OriginId}
    (childSimulation : TypedPlaceClaim n cfg results place)
    (shape : PlaceOwnerShape cfg results place)
    (blocks : ∀ fuel, fuel < n + 1 → ∀ loop pre pre',
      TypedBlockLoopSimulation fuel cfg results (some loop) pre pre' false body)
    (loop : Option LoopCtx) :
    TypedStatementLoopSimulation (n + 2) cfg results loop
      (.forEach x idx (.of place) byRef body origin) := by
  apply typedStatementLoopSimulation_each_of_mode (view := .of place) childSimulation blocks
  intro env state source input point owner irView middle finalPoint atPoint generated lowered finalAt
  obtain ⟨plan⟩ := source.eachPlan
  obtain ⟨child, typing, roots⟩ := plan.viewSource.ofChild
  have mode := eachSourceMode_of_live_place child shape lowered generated finalAt
  simpa only [roots, plan.viewRoots] using mode

end Goose.Lower
