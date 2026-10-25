import Goose.Lower.Validation.SourceReadablePlaceShape
import Goose.Lower.Validation.SourceRootShapeReads
import Goose.Lower.Validation.SummaryPreservationEffects

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem source_empty_readable_place_nonref {env : TEnv} (checked : SourceReadableEnvironment env)
    (variables : env.vars = #[]) {place : Place} {info : PlaceInfo} {start finish : Nat}
    (source : tyPlace env place start = .ok (info, finish)) (readable : info.ty.readable = true) :
    info.ty.isRefLike = false := by
  cases reference : info.ty.isRefLike with
  | false => rfl
  | true =>
    have shape := source_readable_place_shape checked source readable reference
    rcases shape with ⟨index, localVar, _, row, _⟩ | ⟨index, localVar, _, _, _, _, row, _⟩
    all_goals simp [variables] at row

theorem source_empty_read_nonref {env : TEnv} (checked : SourceReadableEnvironment env)
    (variables : env.vars = #[]) {place : Place} {type : Ty} {start finish : Nat}
    (source : tyExpr env (.read place) start = .ok (type, finish)) : type.isRefLike = false := by
  cases reference : type.isRefLike with
  | false => rfl
  | true =>
    have shape := source_read_expression_shape checked source reference
    rcases shape with ⟨index, localVar, _, row, _⟩ | ⟨index, localVar, _, _, _, _, row, _⟩
    all_goals simp [variables] at row

theorem source_initializer_readable (module : Core.Module) (index : GlobalId)
    (accepted : Core.validate module = .ok ()) : SourceReadableEnvironment (initEnv module index) :=
  .empty accepted rfl

theorem source_initializer_root_tables (module : Core.Module) (index : GlobalId) (scopes : List ScopeId) :
    SourceRootTables (initEnv module index) ⟨module, initImpl, initContext, scopes⟩ := ⟨rfl, rfl⟩

theorem source_initializer_read_nonref {module : Core.Module} (index : GlobalId)
    (accepted : Core.validate module = .ok ()) {place : Place} {type : Ty} {start finish : Nat}
    (source : tyExpr (initEnv module index) (.read place) start = .ok (type, finish)) :
    type.isRefLike = false := source_empty_read_nonref (source_initializer_readable module index accepted) rfl source

namespace SummaryPreservation

theorem global_initializer_parameterRoots_closed (module : Core.Module) (global : Core.Global) :
    ParameterRootsClosed (lowerGlobal module global).init := by
  intro index root member
  apply Or.inl
  simpa [Func.parameterRoots, lowerGlobal] using member

end SummaryPreservation

#print axioms source_empty_read_nonref
#print axioms SummaryPreservation.global_initializer_parameterRoots_closed

end Goose.Lower.Validation
