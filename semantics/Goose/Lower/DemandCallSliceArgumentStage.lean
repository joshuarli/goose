import Goose.Lower.DemandCallSliceRetained
import Goose.Lower.DemandCallReferenceBorrow

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_call_slice_argument {cfg : Cfg} {env : Env} {initialState state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) initialState)
    {index : Nat} {borrow : Mutability} {slot : VarId}
    (found : arguments[index]? = some (.byRef borrow (.var slot)))
    (child : PlaceSource cfg env (.var slot) state)
    (target : child.ty.refTarget = true ∨ (child.ty.isSlice = true ∧ child.mutable = true ∧ (Place.var slot).sliceArg = true))
    (canonical : (ArgSource.byRef borrow child target).MatchesContext source.world source.typingEnv source.rootsEnv
      (callArgContext source.context index (.byRef borrow (.var slot)) found))
    {mutability : Mutability} {element : Ty} (type : child.ty = .slice mutability element)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.call context arguments origin)) before)
    {required : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    {prior : List (ValueId × RetainedAlias)}
    (tracked : GeneratedCallArgumentRows source.rootsEnv.access source.path 0 (arguments.take index)
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).1 prior)
    {initial : GIR.Frame} {start : Pt}
    (atPoint : (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2.pp = some start)
    (related : Rel cfg env cx initial (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks) :
    ∃ (location : Loc) (length : Nat) (point : Pt) (frame : GIR.Frame) (cell : SliceSlotArgumentCell),
      let stage := (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2
      let id := (lowerArg (.byRef borrow (.var slot)) (lowerEnv cfg.mod env.vars results) stage).1
      evalArg 2 cfg env (.byRef borrow (.var slot)) state = .ok (.ref location) state ∧
      DemandRuntimePrefix cx length ⟨start, initial, state⟩ ⟨point, frame, state⟩ ∧
      Post cfg env cx stage initial (lowerArg (.byRef borrow (.var slot)) (lowerEnv cfg.mod env.vars results) stage).2
        frame point [(id, .val (.ref location))] ∧
      cell.value = id ∧ cell.Checked source (index + 1) frame ∧
      SliceSlotAliasAt cfg.mod source.world env state.store frame id cell.alias mutability element := by
  let le := lowerEnv cfg.mod env.vars results
  let stage := (lowerArgs (arguments.take index) le before).2
  let address := (lowerPlace (.var slot) le stage).1
  let middle := (lowerPlace (.var slot) le stage).2
  obtain ⟨location, placed, addressPost, firstStep⟩ :=
    accepted_generated_call_reference_address source found child target canonical (.slot slot) occurrence rows tracked atPoint related extended
  have argExtended := generated_call_argument_extended found extended
  have argEq : lowerArg (.byRef borrow (.var slot)) le stage = borrowTo borrow address le middle := by
    simp [lowerArg, bind_run, address, middle]
  have borrowExtended : ExtT (borrowTo borrow address le middle).2 cx.fn.blocks := by
    rw [← argEq]
    exact argExtended
  obtain ⟨length, point, frame, tail, post⟩ := generated_call_reference_borrow addressPost borrow le borrowExtended
  have finalPost : Post cfg env cx stage initial (lowerArg (.byRef borrow (.var slot)) le stage).2 frame point
      [((lowerArg (.byRef borrow (.var slot)) le stage).1, .val (.ref location))] := by
    rw [argEq]
    exact post
  obtain ⟨cell, cellValue, checked, alias⟩ := SliceSlotArgumentCell.ofReference source found child target canonical type placed finalPost
  refine ⟨location, length + 1, point, frame, cell, ?_, .next ((firstStep 0).runtime) tail, finalPost, cellValue, checked, alias⟩
  simp [evalArg, bind_apply, placed, pure_apply]

#print axioms accepted_generated_call_slice_argument
end Goose.Lower
