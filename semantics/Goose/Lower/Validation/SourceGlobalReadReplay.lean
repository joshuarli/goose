import Goose.Lower.Validation.SourceGlobalReadContracts
import Goose.Lower.Validation.SummaryPreservationReplayScalarRead

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

private theorem read_emit_cur (op : Op) (le : LEnv) (state : LS) :
    (Goose.Lower.emitDef op le state).2.cur = state.cur := by
  cases current : state.cur with
  | none => rw [emitDef_none _ _ current]; exact current
  | some block => rw [emitDef_run _ _ current]; exact current

theorem typedGlobalRead {typingEnv : TEnv} {env : PEnv} {place : Place} {type : Ty}
    {start finish : Nat} {before after : RState} {sourceRoots : List RootRef}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {func : Func}
    {returnTypes : List Ty} {slots : Array (List RootRef)} {target : Core.Eff}
    {scopeCount : Nat} {ls : LS} {upper : Prov}
    (checked : SourceReadableEnvironment typingEnv) (variables : typingEnv.vars = #[])
    (tables : SourceRootTables typingEnv env) (closed : ParameterRootsClosed func)
    (source : tyExpr typingEnv (.read place) start = .ok (type, finish))
    (replayed : rpExpr env (.read place) before = .ok (sourceRoots, after))
    (wholeEffect : EffectRefinement func after.eff target)
    (ready : ReplayBuilder (lower env.mod) results vt func target
      (lowerEnv env.mod env.impl.vars returnTypes) scopeCount slots ls upper)
    (generated : GeneratedBuilderState ls)
    (native : NativeRows vt (lowerExpr (.read place) (lowerEnv env.mod env.impl.vars returnTypes) ls).2)
    (placeChild : GlobalPlaceReplayAt typingEnv env results vt func returnTypes slots target scopeCount place ls upper) :
    ∃ next, ReplayBuilder (lower env.mod) results vt func target
        (lowerEnv env.mod env.impl.vars returnTypes) scopeCount slots
        (lowerExpr (.read place) (lowerEnv env.mod env.impl.vars returnTypes) ls).2 next ∧
      ((lowerExpr (.read place) (lowerEnv env.mod env.impl.vars returnTypes) ls).2.cur.isSome = true →
        ReplayValue func next (lowerExpr (.read place) (lowerEnv env.mod env.impl.vars returnTypes) ls).2
          (lowerExpr (.read place) (lowerEnv env.mod env.impl.vars returnTypes) ls).1 sourceRoots (.data type)) ∧
      ∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old := by
  let le := lowerEnv env.mod env.impl.vars returnTypes
  let address := lowerPlace place le ls
  have nonref := source_empty_read_nonref checked variables source
  obtain ⟨info, placeFinish, placeTyped, typeEq⟩ := tyExpr_read_place source
  obtain ⟨placeRoots, placeState, placeReplay, tail⟩ := (st_bind_ok _ _ _ _).mp replayed
  have placeEffect := effectRefinement_before_of_replay
    (PMono.bind (PMono.addReads placeRoots) (fun _ => PMono.readRoots env place))
    (PMonoRebinds.bind (PMonoRebinds.addReads placeRoots) (fun _ => PMonoRebinds.readRoots env place))
    (PFlagsMono.bind (PFlagsMono.addReads placeRoots) (fun _ => PFlagsMono.readRoots env place)) tail wholeEffect
  have variablesAligned : le.vars = typingEnv.vars := by
    simpa only [le, lowerEnv] using tables.variablesEq
  have inactive := nonrefRead_record_inactive source nonref variablesAligned
  have whole : lowerExpr (.read place) le ls = Goose.Lower.emitDef (.load address.1) le address.2 := by
    simp only [lowerExpr, bind_run, inactive, pure_run]
    rfl
  have placeNative : NativeRows vt address.2 := by
    apply native.of_prefix
    rw [whole]
    exact types_emitDef _ le address.2 _ _ rfl
  obtain ⟨middle, middleReady, input, retained⟩ := placeChild info start placeFinish before placeState placeRoots
    placeTyped placeReplay placeEffect ready generated placeNative
  obtain ⟨next, nextReady, value, nextRetained⟩ := middleReady.scalarRead type nonref closed placeReplay replayed wholeEffect
    (placeRun := (rfl : lowerPlace place le ls = address)) input (by
      intro live
      have resultLive : (lowerExpr (.read place) le ls).2.cur.isSome = true := by
        rw [whole, read_emit_cur]
        exact live
      have environment : lowerEnv typingEnv.mod typingEnv.vars returnTypes = le := by
        rw [← tables.moduleEq, ← tables.variablesEq]
      have tag := native.expression generated source (by rw [environment]) resultLive
      obtain ⟨block, current⟩ := Option.isSome_iff_exists.mp live
      have fresh : (lowerExpr (.read place) le ls).1 = address.2.vals.size := by
        rw [whole, emitDef_run _ _ current]
      simpa only [fresh] using tag) inactive
  refine ⟨next, nextReady, value, ?_⟩
  intro old bound
  have middleBound : old < middle.vals.size := by
    rw [middleReady.roots.valueSize]
    exact Nat.lt_of_lt_of_le (by simpa only [ready.roots.valueSize] using bound)
      (advB_lowerPlace place le ls address.1 address.2 rfl).vals
  rw [nextRetained old middleBound, retained old bound]

#print axioms typedGlobalRead

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
