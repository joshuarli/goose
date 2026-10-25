import Goose.Lower.DemandTrace
import Goose.Lower.TypedExpressions

namespace Goose.Lower

open Goose.Core Goose.GIR

def SlotStorageAt (env : Env) (store : Store) (frame : GIR.Frame) (slot : VarId) (id : ValueId) : Prop :=
  ∃ binding scope old, env.vars[slot]? = some binding ∧ env.scopes.lookup binding.scope = some scope ∧
    store.roots[RootInst.local env.act scope slot]? = some old ∧
    frame.vals[id]? = some (.val (.ref ⟨.local env.act scope slot, []⟩))

theorem slotAddress_storage_step {cfg : Cfg} {env : Env} {world : Core.Sound.World}
    {typing : TEnv} {roots : PEnv} {state : St} {future : List VarId}
    (source : Core.Sound.Frame cfg.mod world typing roots env state future)
    {slot : VarId} (visible : slot ∈ typing.visible) {cx : FnCtx} {before : LS} {frame : GIR.Frame}
    (related : Rel cfg env cx frame before) {point : Pt} {id : ValueId}
    (instruction : instAt cx.fn point = some (.def id (.slotAddr slot))) (fuel : Nat) :
    ∃ location, DemandInstructionStep cx fuel ⟨point, frame, state⟩
        ⟨(point.1, point.2 + 1), frame.set id (.val (.ref location)), state⟩ ∧
      SlotStorageAt env state.store (frame.set id (.val (.ref location))) slot id := by
  obtain ⟨binding, scope, old, variableAt, scopeAt, parameter, stored, shape⟩ := source.bindings slot visible
  let location : Loc := ⟨.local env.act scope slot, []⟩
  refine ⟨location, .definition instruction ?_, binding, scope, old, variableAt, scopeAt, stored, Frame.set_get _ _ _⟩
  simp only [execOp, execPure, slotRoot_eq related]
  simp [rootOf, variableAt, scopeAt, location, bind_apply, pure_apply]

theorem SlotStorageAt.store {env : Env} {state : St} {frame : GIR.Frame} {slot : VarId} {address : ValueId}
    (storage : SlotStorageAt env state.store frame slot address) {value : ValueId} {new : Val}
    (valueAt : frame.vals[value]? = some (.val new)) (function : Func) (origin : Option OriginId) :
    ∃ after, execEff function frame (.store address value origin) state = .ok frame after ∧
      SlotStorageAt env after.store frame slot address ∧
      ∃ binding scope, env.vars[slot]? = some binding ∧ env.scopes.lookup binding.scope = some scope ∧
        after.store.roots[RootInst.local env.act scope slot]? = some new := by
  obtain ⟨binding, scope, old, variableAt, scopeAt, stored, addressAt⟩ := storage
  let root := RootInst.local env.act scope slot
  let after : St := { state with store := ⟨(state.store.roots.erase root).insert root new⟩ }
  have written := Core.Sound.write_root state.store root old new stored
  dsimp only [root] at written
  have newAt : after.store.roots[root]? = some new := by
    simp [after]
  refine ⟨after, ?_, ⟨binding, scope, new, variableAt, scopeAt, newAt, addressAt⟩,
    binding, scope, variableAt, scopeAt, newAt⟩
  simp only [execEff, getVal_of addressAt, pure_bind, expectRef, getVal_of valueAt]
  simp [bind_apply, pure_apply, writeLoc, written, after, root]

end Goose.Lower
