import Goose.Proofs.ExitExecutionUnwind
import Goose.Proofs.ExitExecutionLandedChannels

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

theorem literal_return_landed (fuel : Nat) (config : EvalConfig)
    (source target : RuntimeActivation) (ty : Goose.Core.IntTy) (value : Int)
    (origin : Goose.Core.OriginId) (initial final : ExecutionState) (carriers : List Carrier)
    (channels : target.channels = [.register (.int ty)])
    (completed : withExitChannels source target [.lit ty value] origin
      (fun channels => evalOperands (fuel + 3) config source channels [.lit ty value]) initial = .ok carriers final) :
    LandedResultChannels final target.channels [.int ty] carriers := by
  obtain ⟨selected, prepared, raw, afterOperands, afterMaterialized, setup, evaluated, materialized, _⟩ :=
    withExitChannels_ok_origin source target [.lit ty value] origin
      (fun channels => evalOperands (fuel + 3) config source channels [.lit ty value]) initial final carriers completed
  simp only [exitChannels, channels, List.length_cons, List.length_nil, bne_self_eq_false,
    Bool.false_eq_true, ↓reduceIte, List.zip_cons_cons, List.zip_nil_left, List.mapM_cons,
    List.mapM_nil, bind, pure] at setup
  cases setup
  simp only [evalOperands, evalProduce, evalValue, bind, pure, singleCarrier] at evaluated
  cases evaluated
  simp only [materializeOwnedCarriers, List.mapM_cons, List.mapM_nil, bind, pure] at materialized
  cases materialized
  rw [channels]
  exact .cons (.register _ _) .nil

theorem literal_return_landed_after_unwind (fuel : Nat) (config : EvalConfig)
    (source inner target : RuntimeActivation) (ty : Goose.Core.IntTy) (value : Int)
    (origin : Goose.Core.OriginId) (initial final : ExecutionState) (carriers : List Carrier)
    (innerScope blockScope : Nat) (innerInst blockInst : Goose.Core.ScopeInst)
    (results : List Ty) (resultType : results = [.int ty])
    (channels : target.channels = [.register (.int ty)])
    (completed : withExitChannels source target [.lit ty value] origin
      (fun channels => evalOperands (fuel + 3) config source channels [.lit ty value]) initial = .ok carriers final) :
    let innerEnv := { inner with scopes := (innerScope, innerInst) :: inner.scopes }
    let unwound := releaseScopeState inner innerScope innerInst
      (releaseScopeState innerEnv blockScope blockInst final)
    LandedResultChannels { unwound with activations := unwound.activations.filter (fun current => current.act != inner.act) } target.channels results carriers := by
  subst results
  have ready := literal_return_landed fuel config source target ty value origin initial final carriers channels completed
  exact ready.of_construction_eq (before := final) (after := { (releaseScopeState inner innerScope innerInst
    (releaseScopeState { inner with scopes := (innerScope, innerInst) :: inner.scopes } blockScope blockInst final)) with
    activations := (releaseScopeState inner innerScope innerInst
      (releaseScopeState { inner with scopes := (innerScope, innerInst) :: inner.scopes } blockScope blockInst final)).activations.filter
        (fun current => current.act != inner.act) }) rfl

#print axioms literal_return_landed_after_unwind
#print axioms literal_return_landed

end Goose.Proofs.ExitExecution
