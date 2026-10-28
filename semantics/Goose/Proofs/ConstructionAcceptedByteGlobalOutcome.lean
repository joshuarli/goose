import Goose.Proofs.ConstructionAcceptedByteGlobal
import Goose.Proofs.ExitExecutionInvocationStatementsGlobalReplay

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

private theorem evalBind_assoc (action : EvalM α) (next : α → EvalM β) (last : β → EvalM γ) :
    ((action >>= next) >>= last) = (action >>= fun value => next value >>= last) := by
  funext state
  cases evaluated : action state <;> simp only [bind, evaluated]

private theorem evalBind_unit (action : EvalM Unit) : (action >>= fun _ => pure ()) = action := by
  funext state
  cases evaluated : action state <;> simp only [bind, evaluated, pure]

theorem initGlobals_head_factor (fuel : Nat) (config : EvalConfig) (id : Goose.Core.GlobalId)
    (rest : List Goose.Core.GlobalId) :
    initGlobals fuel config (id :: rest) =
      (initGlobals fuel config [id] >>= fun _ => initGlobals fuel config rest) := by
  rw [statementGlobal_next_action fuel config id rest, statementGlobal_next_action fuel config id []]
  simp only [initGlobals]
  simp only [← evalBind_assoc, evalBind_unit]

theorem initGlobals_byteOwner_split (fuel : Nat) (config : EvalConfig) (initialized : Nat) (descriptor : Global)
    (bytes : List UInt8) (bytesOrigin : Goose.Core.OriginId) (rest : List Goose.Core.GlobalId)
    (before : ExecutionState) (result : ExecutionStep Unit) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop)
    (world : AcceptedWorld config initialized before ambient types live [] []) (clear : FutureGlobalsClear config initialized before)
    (declared : config.module.globals[initialized]? = some descriptor) (ty : descriptor.ty = .varr (.int .u8))
    (initializer : descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin)
    (executed : initGlobals (fuel + 1) config (initialized :: rest) before = result) :
    initGlobals (fuel + 1) config [initialized] before = result ∨
    ∃ middle, initGlobals (fuel + 1) config rest middle = result ∧
      AcceptedWorld config (initialized + 1) middle ambient types
        (fun root => root = .global initialized ∨ live root) [] [] ∧
      FutureGlobalsClear config (initialized + 1) middle := by
  rw [initGlobals_head_factor] at executed
  cases head : initGlobals (fuel + 1) config [initialized] before with
  | stop reason state | escape reason carriers state | jump reason kind state =>
    left
    simp only [bind, head] at executed
    exact executed
  | ok value middle =>
    cases value
    right
    simp only [bind, head] at executed
    obtain ⟨checked, done, finalWorld, finalClear⟩ := initGlobals_byteOwner_head fuel config initialized descriptor bytes bytesOrigin []
      before middle ambient types live world clear declared ty initializer head
    simp only [initGlobals, pure, ExecutionStep.ok.injEq, true_and] at done
    subst checked
    exact ⟨middle, executed, finalWorld, finalClear⟩

theorem initGlobals_byteOwners_prefix (count : Nat) :
    ∀ (fuel initialized : Nat) (config : EvalConfig) (before : ExecutionState) (result : ExecutionStep Unit)
      (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
      (rest : List Goose.Core.GlobalId),
      initialized + count ≤ config.module.globals.size →
      (∀ id, initialized ≤ id → id < initialized + count →
        ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
          descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin) →
      AcceptedWorld config initialized before ambient types live [] [] → FutureGlobalsClear config initialized before →
      initGlobals (fuel + 1) config (List.range' initialized count ++ rest) before = result →
      ∃ completed middle nextLive, completed ≤ count ∧
        AcceptedWorld config (initialized + completed) middle ambient types nextLive [] [] ∧
        FutureGlobalsClear config (initialized + completed) middle ∧
        ((completed = count ∧ initGlobals (fuel + 1) config rest middle = result) ∨
         (completed < count ∧ initGlobals (fuel + 1) config [initialized + completed] middle = result)) := by
  induction count with
  | zero =>
    intro fuel initialized config before result ambient types live rest bound declarations world clear executed
    refine ⟨0, before, live, Nat.le_refl _, ?_, ?_, Or.inl ⟨rfl, ?_⟩⟩
    · simpa only [Nat.add_zero] using world
    · simpa only [Nat.add_zero] using clear
    · simpa only [List.range'_zero, List.nil_append] using executed
  | succ count ih =>
    intro fuel initialized config before result ambient types live rest bound declarations world clear executed
    obtain ⟨descriptor, bytes, bytesOrigin, declared, ty, initializer⟩ :=
      declarations initialized (Nat.le_refl _) (by omega)
    have tailDeclaration : ∀ id, initialized + 1 ≤ id → id < (initialized + 1) + count →
        ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
          descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin := by
      intro id lower upper
      exact declarations id (by omega) (by omega)
    simp only [List.range'_succ, List.cons_append] at executed
    have split := initGlobals_byteOwner_split fuel config initialized descriptor bytes bytesOrigin
      (List.range' (initialized + 1) count ++ rest) before result ambient types live world clear declared ty initializer executed
    rcases split with stopped | ⟨middle, tail, nextWorld, nextClear⟩
    · refine ⟨0, before, live, by omega, ?_, ?_, Or.inr ⟨by omega, ?_⟩⟩
      · simpa only [Nat.add_zero] using world
      · simpa only [Nat.add_zero] using clear
      · simpa only [Nat.add_zero] using stopped
    · obtain ⟨completed, final, nextLive, completedBound, finalWorld, finalClear, outcome⟩ :=
        ih fuel (initialized + 1) config middle result ambient types
          (fun root => root = .global initialized ∨ live root) rest (by omega) tailDeclaration nextWorld nextClear tail
      refine ⟨completed + 1, final, nextLive, by omega, ?_, ?_, ?_⟩
      · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalWorld
      · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalClear
      · rcases outcome with ⟨done, remaining⟩ | ⟨notDone, stopped⟩
        · exact Or.inl ⟨by omega, remaining⟩
        · refine Or.inr ⟨by omega, ?_⟩
          simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using stopped

#print axioms initGlobals_head_factor
#print axioms initGlobals_byteOwner_split
#print axioms initGlobals_byteOwners_prefix

end Goose.Proofs.ConstructionAcceptedExecution
