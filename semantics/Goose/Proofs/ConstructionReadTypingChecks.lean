import Goose.Proofs.ConstructionReadTyping

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution.ReadBoundsChecks
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation

private def layout : LayoutEnv := ⟨#[]⟩
private def ownerType : Ty := .arr (.int .i64) 1
private def owner : Value := .fixed #[.int .i64 7]
private def state : ExecutionState := { ExecutionState.initial with objects := [(.global 0, owner)] }
private def registry : RootTypes
  | .global 0 => some ownerType
  | _ => none
private def location : Goose.Core.Loc := ⟨.global 0, [1]⟩

theorem typed_backed_root_can_have_an_out_of_bounds_reference :
    state.objects.lookup location.root = some owner ∧
      ValueStorageBacked layout state owner ∧
      PointerTypedValue registry (.ref .readOnly (.int .i64)) (.ref location) ∧
      readLoc 8 layout location state = .stop (.fault .pathRange) state := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · apply ValueStorageBacked.array
    intro value member
    have same : value = .int .i64 7 := by simpa only [List.mem_singleton] using member
    subst value
    exact .integer .i64 7
  · apply PointerTypedValue.reference
    exact ⟨ownerType, rfl, .element ownerType (.int .i64) (.int .i64) 1 [] rfl (.root _)⟩
  · cbv

#print axioms typed_backed_root_can_have_an_out_of_bounds_reference

end Goose.Proofs.ConstructionAcceptedExecution.ReadBoundsChecks
