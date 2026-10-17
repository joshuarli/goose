import Goose.Core.Json
import Goose.Proofs.Core

namespace Goose.Core.OriginsChecks

private def moduleWithOrigin (file line : Nat) (kind : String) : Module := {
  files := #["origin.goose"], types := #[], globals := #[],
  impls := #[⟨"origin", #[], #[], #[], .mk 0 [.abort "origin" 0] none, .unknown⟩],
  contexts := #[⟨0, "origin", [], [], []⟩], entry := 0,
  origins := #[⟨file, line, kind⟩] }

private def rejectsType (m : Module) : Bool :=
  match validate m with
  | .error rejection => rejection.rule == .type
  | .ok _ => false

#guard rejectsType (moduleWithOrigin 99 1 "abort")
#guard rejectsType (moduleWithOrigin 0 0 "abort")
#guard rejectsType (moduleWithOrigin 0 1 "stmt")
#guard (validate (moduleWithOrigin 0 1 "abort")).isOk

private def originJson (file line : Nat) (kind : String) : Lean.Json :=
  .arr #[.str "origin", Lean.toJson file, Lean.toJson line, .str kind]

#guard !(Decode.decOrigin 1 (originJson 99 1 "abort")).isOk
#guard !(Decode.decOrigin 1 (originJson 0 0 "abort")).isOk
#guard !(Decode.decOrigin 1 (originJson 0 1 "stmt")).isOk
#guard (Decode.decOrigin 1 (originJson 0 1 "abort")).isOk

#guard originKinds.all fun kind =>
  (Decode.decOrigin 1 (originJson 0 1 kind)).isOk &&
    (validate (moduleWithOrigin 0 1 kind)).isOk

theorem invalid_file_not_wellFormed : ¬ WellFormed (moduleWithOrigin 99 1 "abort") := by
  intro wellFormed
  have valid := wellFormed.tables.origins ⟨99, 1, "abort"⟩ (by simp [moduleWithOrigin])
  simp [OriginRecordValid, moduleWithOrigin] at valid

theorem zero_line_not_wellFormed : ¬ WellFormed (moduleWithOrigin 0 0 "abort") := by
  intro wellFormed
  have valid := wellFormed.tables.origins ⟨0, 0, "abort"⟩ (by simp [moduleWithOrigin])
  simp [OriginRecordValid] at valid

theorem unknown_kind_not_wellFormed : ¬ WellFormed (moduleWithOrigin 0 1 "stmt") := by
  intro wellFormed
  have valid := wellFormed.tables.origins ⟨0, 1, "stmt"⟩ (by simp [moduleWithOrigin])
  simp [OriginRecordValid, originKinds] at valid

#print axioms Goose.Proofs.Core.validate_wellFormed
#print axioms checkOriginRecord_iff
#print axioms invalid_file_not_wellFormed
#print axioms zero_line_not_wellFormed
#print axioms unknown_kind_not_wellFormed

end Goose.Core.OriginsChecks
