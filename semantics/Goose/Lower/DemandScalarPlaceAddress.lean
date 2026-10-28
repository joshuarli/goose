import Goose.Lower.DemandGeneratedPlaceLeaves
import Goose.Lower.DemandRuntimePrefix

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

inductive ScalarReadPlace : Place → Prop
  | global (global : GlobalId) : ScalarReadPlace (.global global)
  | slot (slot : VarId) : ScalarReadPlace (.var slot)

theorem accepted_generated_scalar_place_address {cfg : Cfg} {env : Env} {state : St} {place : Place}
    (source : PlaceSource cfg env place state) (form : ScalarReadPlace place)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root source.path (.place place) before)
    {required : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    {frame : GIR.Frame} {point : Pt} (atPoint : before.pp = some point) (related : Rel cfg env cx frame before)
    (extended : ExtT (lowerPlace place (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks) :
    ∃ location : Loc,
      evalPlace 1 cfg env place state = .ok location state ∧
      Post cfg env cx before frame (lowerPlace place (lowerEnv cfg.mod env.vars results) before).2
        (frame.set (lowerPlace place (lowerEnv cfg.mod env.vars results) before).1 (.val (.ref location)))
        (point.1, point.2 + 1) [((lowerPlace place (lowerEnv cfg.mod env.vars results) before).1, .val (.ref location))] ∧
      ∀ fuel, DemandInstructionStep cx fuel ⟨point, frame, state⟩
        ⟨(point.1, point.2 + 1), frame.set (lowerPlace place (lowerEnv cfg.mod env.vars results) before).1
          (.val (.ref location)), state⟩ := by
  let le := lowerEnv cfg.mod env.vars results
  let addressed := lowerPlace place le before
  cases form with
  | global global =>
    have site := GeneratedDemandInstruction.globalAddress_auto occurrence rows atPoint extended
    have post := (Post.def_leaf (Post.init related atPoint)
      (show emitDef (.globalAddr global) le before = (addressed.1, addressed.2) from rfl)
      extended (.val (.ref ⟨.global global, []⟩))).1
    refine ⟨⟨.global global, []⟩, ?_, post, ?_⟩
    · simp only [evalPlace, pure_apply]
    · intro fuel
      apply DemandInstructionStep.definition site.instruction
      simp only [execOp, execPure, pure_apply]
  | slot slot =>
    have typed := source.typed
    simp only [tyPlace] at typed
    obtain ⟨binding, next, checked, resultType⟩ := (st_bind_ok _ _ _ _).1 typed
    have visible := ((varOf_ok source.typingEnv slot source.typingStart (binding, next)).1 checked).1
    obtain ⟨binding, scope, old, variableAt, scopeAt, parameter, stored, shape⟩ := source.frame.bindings slot visible
    let location : Loc := ⟨.local env.act scope slot, []⟩
    have site := GeneratedDemandInstruction.slotAddress_auto occurrence rows atPoint extended
    have post := (Post.def_leaf (Post.init related atPoint)
      (show emitDef (.slotAddr slot) le before = (addressed.1, addressed.2) from rfl)
      extended (.val (.ref location))).1
    refine ⟨location, ?_, post, ?_⟩
    · simp [evalPlace, rootOf, variableAt, scopeAt, location, bind_apply, pure_apply]
    · intro fuel
      apply DemandInstructionStep.definition site.instruction
      simp only [execOp, execPure, slotRoot_eq related]
      simp [rootOf, variableAt, scopeAt, location, bind_apply, pure_apply]

#print axioms accepted_generated_scalar_place_address

end Goose.Lower
