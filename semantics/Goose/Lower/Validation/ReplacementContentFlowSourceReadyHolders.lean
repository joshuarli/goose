import Goose.Lower.Validation.ReplacementContentFlowSourceReadyReads
import Goose.GIR.ReplacementContentFlowProofsCanonicalHolders

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem holder_content_ready {func : Func} {state : State} {payload : Ty}
    {upper : List RootRef} {address : Roots}
    (physical : HolderRoots func payload upper address)
    (available : address ≠ .pending)
    (locals : ∀ slot, RootRef.local slot ∈ upper → flowAt state.slots slot ≠ .pending)
    (parameters : ∀ index, (func.params[index]?).any Ty.isRefSlice = true → flowAt state.contents index ≠ .pending) :
    content func state address ≠ .pending := by
  apply content_ready available _ parameters
  intro atoms equality slot member
  rw [equality] at physical
  exact locals slot (physical (.local slot) member).local.choose_spec.2.2

theorem holder_local_content_ready {env : TEnv} {func : Func} {state : State}
    {payload : Ty} {varId : VarId} {localVar : LocalVar} {address : Roots}
    (visible : varId ∈ env.visible) (row : env.vars[varId]? = some localVar)
    (reference : localVar.ty.isRefLike = true)
    (slots : VisibleSlotsReady env state)
    (physical : HolderRoots func payload [.local varId] address)
    (available : address ≠ .pending)
    (parameters : ∀ index, (func.params[index]?).any Ty.isRefSlice = true → flowAt state.contents index ≠ .pending) :
    content func state address ≠ .pending := by
  apply holder_content_ready physical available _ parameters
  intro slot member
  have same : slot = varId := by simpa using member
  subst slot
  exact slots varId visible localVar row reference

theorem holder_parameter_content_ready {func : Func} {types : Array (Option VTy)} {state : State}
    {payload : Ty} {upper : List RootRef} {address : Roots}
    (growth : (start func types).Extends state)
    (physical : HolderRoots func payload upper address)
    (available : address ≠ .pending)
    (external : ∀ slot, RootRef.local slot ∉ upper) :
    content func state address ≠ .pending := by
  apply holder_content_ready physical available
  · intro slot member
    exact False.elim (external slot member)
  · intro index _
    exact contents_ready_of_initial_extends growth index

#print axioms holder_content_ready
#print axioms holder_local_content_ready
#print axioms holder_parameter_content_ready

end Goose.Lower.Validation.ReplacementContentFlowSource
