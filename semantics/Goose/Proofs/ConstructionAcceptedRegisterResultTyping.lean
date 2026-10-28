import Goose.Construct.Validate
import Goose.Proofs.ConstructionAcceptedParameterSource

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem validated_scalarRegister_body_typing (module : Module) (id : Nat) (implementation : Impl)
    (accepted : validate module = .ok ()) (present : module.impls[id]? = some implementation)
    (ty : Ty) (result : implementation.results = #[⟨ty, .register, none⟩])
    (scalar : (∃ intTy, ty = .int intTy) ∨ ty = .bool) (tail : implementation.body.value.isSome = true) :
    ∃ declared, typeBlock 4096 {
      module := module
      implementation := some implementation
      variables := implementation.vars
      visible := List.range implementation.params.size
      scope := implementation.body.scope
      loops := 0
      use := if implementation.results.isEmpty then .ordinary else .result
      request := .value
      resultRequests := implementation.results.toList.map (·.request)
      globalLimit := module.globals.size } implementation.body implementation.params.size = .ok ([ty], declared) := by
  obtain ⟨source, declared, checked, passing⟩ := validated_implementation_register_typing module id implementation
    accepted present ty result tail
  have equal := scalarParameter_passesTo_eq source ty scalar passing
  subst source
  exact ⟨declared, checked⟩

#print axioms validated_implementation_register_typing
#print axioms validated_scalarRegister_body_typing
end Goose.Proofs.ConstructionAcceptedExecution
