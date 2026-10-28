import Goose.Lower.DemandCallReferenceAlias

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

def SliceSlotAliasAt (m : Core.Module) (world : World) (env : Env) (store : Store)
    (frame : GIR.Frame) (id : ValueId) (alias : RetainedAlias) (mutability : Mutability) (element : Ty) : Prop :=
  ∃ slot backing start length,
    frame.vals[id]? = some (.val (.ref slot)) ∧ slot.path = [] ∧
    store.roots[slot.root]? = some (.slice backing start length) ∧
    HasTy m world.G store (.ref slot) (.ref mutability alias.ty) ∧
    alias.ty = .slice mutability element ∧ AliasAt m world env store alias (.slice backing start length)

theorem PlaceSource.sliceSlotAlias {cfg : Cfg} {env : Env} {state after : St} {slot : VarId}
    (source : PlaceSource cfg env (.var slot) state) {mutability : Mutability} {element : Ty}
    (type : source.ty = .slice mutability element) {fuel : Nat} {location : Loc}
    (placed : evalPlace fuel cfg env (.var slot) state = .ok location after) {path : List Nat}
    {cx : FnCtx} {before built : LS} {initial frame : GIR.Frame} {point : Pt} {id : ValueId}
    (post : Post cfg env cx before initial built frame point [(id, .val (.ref location))]) :
    ∃ alias, source.rootsEnv.access.aliasArg path (.byRef .mutable (.var slot)) = .ok [alias] ∧
      SliceSlotAliasAt cfg.mod source.world env after.store frame id alias mutability element := by
  have result := source.result fuel location placed
  have placeOk := result.typed
  rw [type] at placeOk
  rcases placeOk with impossible | valid | impossible
  · simp [Ty.refTarget] at impossible
  · obtain ⟨x, lv, si, value, equal, variableAt, scope, locationEq, variableType, _, stored, typed⟩ := valid
    cases equal
    obtain ⟨backing, start, length, valueEq, flat, sliceTyped⟩ := typed
    subst value
    have rooted := result.frame.rooted slot lv si (.slice backing start length) variableAt scope stored backing.root (by simp [Targets])
    obtain ⟨roots, annotation, rooted⟩ := rooted
    let alias : RetainedAlias := ⟨.slice mutability element, roots, .operand path⟩
    have accessVariable : source.rootsEnv.impl.vars[slot]? = some lv := by
      rw [result.frame.vars_p]
      exact variableAt
    have rootQuery : source.rootsEnv.access.variableRoots slot = .ok roots := by
      change (match source.rootsEnv.ann slot with | some rs => pure rs | none => reject .root _) = .ok roots
      rw [annotation]
      rfl
    simp only [PEnv.access] at rootQuery
    have query : source.rootsEnv.access.aliasArg path (.byRef .mutable (.var slot)) = .ok [alias] := by
      simp [AccessEnv.aliasArg, AccessEnv.placeType?, PEnv.access, accessVariable, variableType,
        AccessEnv.exprRoots, Ty.isRefLike, alias, rootQuery, Functor.map, Except.map]
    have aliasAt : AliasAt cfg.mod source.world env after.store alias (.slice backing start length) := by
      refine ⟨⟨backing, start, length, rfl, flat, sliceTyped⟩, ?_⟩
      intro root target
      have eq : root = backing.root := by simpa [Targets] using target.symm
      subst root
      exact rooted
    have referenceTyped : HasTy cfg.mod source.world.G after.store (.ref location) (.ref mutability alias.ty) := by
      refine ⟨location, rfl, Or.inr ⟨?_, ?_, ?_⟩⟩
      · simp [alias, Ty.isSlice, flat]
      · simpa [locationEq]
      · rw [locationEq]
        simp [stored]
    refine ⟨alias, query, ?_⟩
    exact ⟨location, backing, start, length, post.has (id, .val (.ref location)) (by simp), by simpa [locationEq], by simpa [locationEq] using stored,
      referenceTyped, rfl, aliasAt⟩
  · obtain ⟨x, lv, mu0, mu, ty, ann, impossible, _⟩ := impossible
    cases impossible

theorem SliceSlotAliasAt.transport {m : Core.Module} {world : World} {env : Env} {before after : Store}
    {initial frame : GIR.Frame} {id : ValueId} {alias : RetainedAlias} {mutability : Mutability} {element : Ty}
    (source : SliceSlotAliasAt m world env before initial id alias mutability element)
    (sameValue : frame.vals[id]? = initial.vals[id]?)
    (sameSlot : ∀ slot, initial.vals[id]? = some (.val (.ref slot)) → after.roots[slot.root]? = before.roots[slot.root]?)
    (retained : RetainsAlias m world env before after alias) : SliceSlotAliasAt m world env after frame id alias mutability element := by
  obtain ⟨slot, backing, start, length, cell, path, stored, typed, aliasType, aliasAt⟩ := source
  have nextStored : after.roots[slot.root]? = some (.slice backing start length) := by
    rw [sameSlot slot cell]
    exact stored
  have nextAlias := retained.typed (.slice backing start length) aliasAt
  have flat : element.flat = true := by
    have sliceType := aliasAt.1
    rw [aliasType] at sliceType
    obtain ⟨_, _, _, _, flat, _⟩ := sliceType
    exact flat
  have nextReference : HasTy m world.G after (.ref slot) (.ref mutability alias.ty) := by
    refine ⟨slot, rfl, Or.inr ⟨?_, path, ?_⟩⟩
    · rw [aliasType]; simp [Ty.isSlice, flat]
    · rw [nextStored]; simp
  exact ⟨slot, backing, start, length, sameValue.trans cell, path, nextStored, nextReference, aliasType, nextAlias⟩

#print axioms SliceSlotAliasAt.transport

theorem sliceSlot_not_valueAlias {m : Core.Module} {world : World} {env : Env} {store : Store}
    {frame : GIR.Frame} {id : ValueId} {alias : RetainedAlias} {slot : Loc} {mutability : Mutability} {element : Ty}
    (cell : frame.vals[id]? = some (.val (.ref slot))) (aliasType : alias.ty = .slice mutability element) :
    ¬ ValueAliasAt m world env store frame id alias := by
  intro ⟨value, valueAt, typed, _⟩
  rw [cell] at valueAt
  cases valueAt
  rw [aliasType] at typed
  simp [HasTy] at typed

#print axioms sliceSlot_not_valueAlias

#print axioms PlaceSource.sliceSlotAlias
end Goose.Lower
