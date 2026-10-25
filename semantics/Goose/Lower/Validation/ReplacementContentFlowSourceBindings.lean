import Goose.Lower.Validation.ReplacementContentFlowSourceRoots
import Goose.GIR.ReplacementContentFlowProofsNormalization
import Goose.GIR.ReplacementContentFlowProofsRank

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem bindRoots_slot_add_normalized {env : PEnv} {chain : List Nat} {varId : VarId}
    {sourceRoots bound valueRoots : List RootRef} {state : State} {value : Roots}
    (checked : bindRootsV env chain varId sourceRoots = .ok ())
    (annotation : env.ann varId = some bound)
    (shape : state.Shape (lowerContextAt env.mod env.ctx env.impl))
    (prior : flowAt state.slots varId = .pending ∨
      ∃ actual, normalize (lowerContextAt env.mod env.ctx env.impl) (flowAt state.slots varId) = some actual ∧
        ∀ root ∈ actual, root ∈ bound.flatMap (lowerContextAt env.mod env.ctx env.impl).expandParameterRoot)
    (valueKnown : normalize (lowerContextAt env.mod env.ctx env.impl) value = some valueRoots)
    (valueWithin : ∀ root ∈ valueRoots,
      root ∈ sourceRoots.flatMap (lowerContextAt env.mod env.ctx env.impl).expandParameterRoot) :
    let func := lowerContextAt env.mod env.ctx env.impl
    ∃ actual, normalize func (flowAt (addFlow state.slots varId value) varId) = some actual ∧
      ∀ root ∈ actual, root ∈ bound.flatMap func.expandParameterRoot := by
  dsimp only
  obtain ⟨localVar, actualBound, variableRow, actualAnnotation, sourceWithin, outlives⟩ :=
    bindRootsV_ok env chain varId sourceRoots checked
  have same : actualBound = bound := Option.some.inj (actualAnnotation.symm.trans annotation)
  subst actualBound
  have bounded : varId < state.slots.size := by
    rw [shape.slots]
    change varId < (env.impl.vars.mapIdx (fun i lv => (⟨lv.ty, lv.kind, lv.scope, i⟩ : Slot))).size
    simpa only [Array.size_mapIdx] using (Array.getElem?_eq_some_iff.mp variableRow).1
  have added : flowAt (addFlow state.slots varId value) varId = (flowAt state.slots varId).join value := by
    simp only [addFlow, flowAt, Array.set!_eq_setIfInBounds, Array.getD_getElem?_setIfInBounds,
      bounded, ite_true]
  rw [added]
  have assignedWithin : ∀ root ∈ valueRoots,
      root ∈ bound.flatMap (lowerContextAt env.mod env.ctx env.impl).expandParameterRoot := by
    intro root member
    obtain ⟨sourceRoot, sourceMember, expanded⟩ := List.mem_flatMap.mp (valueWithin root member)
    exact List.mem_flatMap.mpr ⟨sourceRoot, sourceWithin sourceRoot sourceMember, expanded⟩
  rcases prior with pending | ⟨oldRoots, oldKnown, oldWithin⟩
  · have pendingJoin : Roots.pending.join value = value := by cases value <;> rfl
    rw [pending, pendingJoin]
    exact ⟨valueRoots, valueKnown, assignedWithin⟩
  · obtain ⟨actual, known, within⟩ := normalize_join_known _ _ _ _ _ oldKnown valueKnown
    refine ⟨actual, known, ?_⟩
    intro root member
    exact (within root member).elim (oldWithin root) (assignedWithin root)

#print axioms bindRoots_slot_add_normalized

theorem bindRoots_slotInit_normalized {env : PEnv} {chain : List Nat} {varId : VarId}
    {sourceRoots bound valueRoots : List RootRef} {state : State} {states : Array State}
    {value : ValueId} {origin : Option OriginId}
    (checked : bindRootsV env chain varId sourceRoots = .ok ())
    (annotation : env.ann varId = some bound)
    (shape : state.Shape (lowerContextAt env.mod env.ctx env.impl))
    (prior : flowAt state.slots varId = .pending ∨
      ∃ actual, normalize (lowerContextAt env.mod env.ctx env.impl) (flowAt state.slots varId) = some actual ∧
        ∀ root ∈ actual, root ∈ bound.flatMap (lowerContextAt env.mod env.ctx env.impl).expandParameterRoot)
    (valueKnown : normalize (lowerContextAt env.mod env.ctx env.impl) (flowAt state.values value) = some valueRoots)
    (valueWithin : ∀ root ∈ valueRoots,
      root ∈ sourceRoots.flatMap (lowerContextAt env.mod env.ctx env.impl).expandParameterRoot) :
    let func := lowerContextAt env.mod env.ctx env.impl
    ∃ actual, normalize func (flowAt
        (step (lower env.mod) states func (func.valueTypes (lower env.mod)) state
          (.eff (.slotInit varId value origin))).slots varId) = some actual ∧
      ∀ root ∈ actual, root ∈ bound.flatMap func.expandParameterRoot := by
  exact bindRoots_slot_add_normalized (state := state) checked annotation shape prior valueKnown valueWithin

#print axioms bindRoots_slotInit_normalized

end Goose.Lower.Validation.ReplacementContentFlowSource
