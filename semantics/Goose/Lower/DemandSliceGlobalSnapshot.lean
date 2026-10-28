import Goose.Lower.DemandGeneratedSlice
import Goose.Lower.DemandGeneratedSnapshotStop
import Goose.Lower.DemandScalarPlaceAddress

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem ExprSource.sliceGlobalViewAlias {cfg : Cfg} {env : Env} {state : St}
    {mutability : Mutability} {global : GlobalId} {lower upper : Bound} {origin : OriginId}
    (source : ExprSource cfg env (.slice mutability (.of (.global global)) lower upper origin) state) :
    ∃ aliases, source.rootsEnv.access.aliasView (source.path ++ [0]) (.of (.global global)) = .ok aliases := by
  obtain ⟨view, typing, roots, canonical, next⟩ := source.sliceChildren mutability origin
  have element := tyView_accessElement (view.frame.mod_t.trans view.frame.mod_p.symm)
    (view.frame.vars_t.trans view.frame.vars_p.symm) view.typed
  rw [roots] at element
  refine ⟨[⟨.slice .readOnly view.element, [.global global], .operand (source.path ++ [0])⟩], ?_⟩
  simp only [AccessEnv.aliasView, element, AccessEnv.viewRoots, AccessEnv.placeRoots, bind, pure]
  rfl

#print axioms ExprSource.sliceGlobalViewAlias

theorem accepted_generated_slice_global_address {cfg : Cfg} {env : Env} {state : St}
    {mutability : Mutability} {global : GlobalId} {lower upper : Bound} {origin : OriginId}
    (source : ExprSource cfg env (.slice mutability (.of (.global global)) lower upper origin) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.slice mutability (.of (.global global)) lower upper origin)) before)
    {required : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    {initial : GIR.Frame} {point : Pt} (atPoint : before.pp = some point) (related : Rel cfg env cx initial before)
    (extended : ExtT (lowerExpr (.slice mutability (.of (.global global)) lower upper origin)
      (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks) :
    ∃ (view : ViewSource cfg env (.of (.global global)) state), source.ViewChildAt view 0 rfl ∧
      ∃ viewOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
          root view.path (.view (.of (.global global))) before,
      GeneratedDemandRows cfg.mod view.rootsEnv.access viewOccurrence required ∧
      evalPlace 1 cfg env (.global global) state = .ok ⟨.global global, []⟩ state ∧
      Post cfg env cx before initial (lowerPlace (.global global) (lowerEnv cfg.mod env.vars results) before).2
        (initial.set (lowerPlace (.global global) (lowerEnv cfg.mod env.vars results) before).1 (.val (.ref ⟨.global global, []⟩)))
        (point.1, point.2 + 1) [((lowerPlace (.global global) (lowerEnv cfg.mod env.vars results) before).1, .val (.ref ⟨.global global, []⟩))] ∧
      (∀ fuel, DemandInstructionStep cx fuel ⟨point, initial, state⟩
        ⟨(point.1, point.2 + 1), initial.set (lowerPlace (.global global) (lowerEnv cfg.mod env.vars results) before).1
          (.val (.ref ⟨.global global, []⟩)), state⟩) := by
  obtain ⟨view, viewTyping, viewRoots, viewCanonical, nextBound⟩ := source.sliceChildren mutability origin
  obtain ⟨place, placeTyping, placeRoots, placeCanonical⟩ := view.ofChild
  have viewOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root view.path (.view (.of (.global global))) before := by
    rw [viewCanonical.path]
    exact .first occurrence (.expressionView rfl)
  have viewRows : GeneratedDemandRows cfg.mod view.rootsEnv.access viewOccurrence required := by
    have inherited : GeneratedDemandRows cfg.mod source.rootsEnv.access
        (.first occurrence (.expressionView rfl)) required := .first (first := .expressionView rfl) rows
    simpa only [viewRoots, viewCanonical.path] using inherited
  have placeOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root place.path (.place (.global global)) before := by
    rw [placeCanonical.path]
    exact .first viewOccurrence (.viewPlace rfl)
  have placeRows : GeneratedDemandRows cfg.mod place.rootsEnv.access placeOccurrence required := by
    have inherited : GeneratedDemandRows cfg.mod view.rootsEnv.access
        (.first viewOccurrence (.viewPlace rfl)) required := .first (first := .viewPlace rfl) viewRows
    simpa only [placeRoots, placeCanonical.path] using inherited
  have viewExtended := generated_slice_view_extended extended
  obtain ⟨location, placed, addressPost, firstStep⟩ := accepted_generated_scalar_place_address place (.global global)
    placeOccurrence placeRows atPoint related (generated_view_place_extended viewExtended)
  have locationEq : location = ⟨.global global, []⟩ := by
    simpa [evalPlace, pure_apply] using placed.symm
  subst location
  exact ⟨view, viewCanonical, viewOccurrence, viewRows, placed, addressPost, firstStep⟩

#print axioms accepted_generated_slice_global_address

theorem accepted_generated_slice_global_snapshot {cfg : Cfg} {env : Env} {state after : St}
    {mutability : Mutability} {global : GlobalId} {lower upper : Bound} {origin : OriginId}
    (source : ExprSource cfg env (.slice mutability (.of (.global global)) lower upper origin) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.slice mutability (.of (.global global)) lower upper origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (bounded : map.Bounded before.vals.size)
    {initial : GIR.Frame} {point : Pt} (atPoint : before.pp = some point) (related : Rel cfg env cx initial before)
    (realized : map.Realizes cfg.mod source.world env ⟨point, initial, state⟩)
    (extended : ExtT (lowerExpr (.slice mutability (.of (.global global)) lower upper origin)
      (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {next : Pt} {frame : GIR.Frame}
    (snapshot : RuntimeStep cx.cfg cx.fn (point.1, point.2 + 1)
      (initial.set (lowerPlace (.global global) (lowerEnv cfg.mod env.vars results) before).1
        (.val (.ref ⟨.global global, []⟩))) state next frame after) :
    ∃ (sample : ViewVal) (view : ViewSource cfg env (.of (.global global)) state),
      source.ViewChildAt view 0 rfl ∧
      (∀ fuel, DemandInstructionStep cx fuel ⟨point, initial, state⟩
        ⟨(point.1, point.2 + 1), initial.set (lowerPlace (.global global) (lowerEnv cfg.mod env.vars results) before).1
          (.val (.ref ⟨.global global, []⟩)), state⟩) ∧
      evalView 2 cfg env (.of (.global global)) state = .ok sample after ∧
      Post cfg env cx before initial (lowerView (.of (.global global)) (lowerEnv cfg.mod env.vars results) before).2
        frame next [((lowerView (.of (.global global)) (lowerEnv cfg.mod env.vars results) before).1, .view sample)] ∧
      DemandFrameAt cfg env cx view.world view.typingEnv view.rootsEnv view.context.outputFuture map.values map.runs
        ⟨next, frame, after⟩ ∧
      (∀ aliases, view.rootsEnv.access.aliasView view.path (.of (.global global)) = .ok aliases →
        (map.addRuns (lowerView (.of (.global global)) (lowerEnv cfg.mod env.vars results) before).1 aliases).Realizes
          cfg.mod view.world env ⟨next, frame, after⟩) := by
  obtain ⟨view, viewCanonical, viewOccurrence, viewRows, placed, addressPost, firstStep⟩ :=
    accepted_generated_slice_global_address source occurrence rows atPoint related extended
  have viewExtended := generated_slice_view_extended extended
  have beforeView : map.Realizes cfg.mod view.world env
      ⟨(point.1, point.2 + 1), initial.set (lowerPlace (.global global) (lowerEnv cfg.mod env.vars results) before).1
        (.val (.ref ⟨.global global, []⟩)), state⟩ := by
    have carried := realized.retained addressPost.same bounded.1 bounded.2 RetainsAliases.refl
    simpa only [RetainedSsaMap.Realizes, viewCanonical.world] using carried
  obtain ⟨sample, _, _, viewed, post, demanded, retained⟩ := accepted_generated_snapshot_runtime_step view viewOccurrence viewRows
    coverage placed addressPost (bounded.mono addressPost.mono) beforeView viewExtended snapshot
  exact ⟨sample, view, viewCanonical, firstStep, viewed, post, demanded, retained⟩


theorem accepted_generated_slice_global_snapshot_stop {cfg : Cfg} {env : Env} {state after : St}
    {mutability : Mutability} {global : GlobalId} {lower upper : Bound} {origin : OriginId}
    (source : ExprSource cfg env (.slice mutability (.of (.global global)) lower upper origin) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.slice mutability (.of (.global global)) lower upper origin)) before)
    {required : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    {initial : GIR.Frame} {point : Pt} (atPoint : before.pp = some point) (related : Rel cfg env cx initial before)
    (extended : ExtT (lowerExpr (.slice mutability (.of (.global global)) lower upper origin)
      (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {targetFuel : Nat} {stop : Stop}
    (stopped : DemandInstructionStop cx targetFuel
      ⟨(point.1, point.2 + 1), initial.set (lowerPlace (.global global) (lowerEnv cfg.mod env.vars results) before).1
        (.val (.ref ⟨.global global, []⟩)), state⟩ stop after) (nonTimeout : stop ≠ .timeout) :
    (∀ fuel, DemandInstructionStep cx fuel ⟨point, initial, state⟩
      ⟨(point.1, point.2 + 1), initial.set (lowerPlace (.global global) (lowerEnv cfg.mod env.vars results) before).1
        (.val (.ref ⟨.global global, []⟩)), state⟩) ∧
    evalExpr 3 cfg env (.slice mutability (.of (.global global)) lower upper origin) state = .stop stop after := by
  obtain ⟨view, canonical, viewOccurrence, viewRows, placed, post, first⟩ :=
    accepted_generated_slice_global_address source occurrence rows atPoint related extended
  have viewStop := accepted_generated_snapshot_runtime_stop view viewOccurrence viewRows placed post
    (generated_slice_view_extended extended) nonTimeout stopped
  refine ⟨first, ?_⟩
  simp only [evalExpr, bind_apply, viewStop]

#print axioms accepted_generated_slice_global_snapshot_stop

#print axioms accepted_generated_slice_global_snapshot
end Goose.Lower
