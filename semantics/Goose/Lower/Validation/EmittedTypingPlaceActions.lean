import Goose.Lower.Validation.EmittedTypingSourceActions
import Goose.Lower.Validation.EmittedTypingSourceOutputs
import Goose.Lower.Validation.EmittedTypingPlaceSource
import Goose.Lower.Validation.EmittedTypingViewSource

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem emitted_source_variable (env : Core.TEnv) (results : List Ty) (index : VarId) :
    EmittedSourcePlace env results (.var index) := by
  intro info start finish source initial before generated builder
  exact emitted_checked_lowerPlace_var source results builder

theorem emitted_source_global (env : Core.TEnv) (results : List Ty) (index : GlobalId) :
    EmittedSourcePlace env results (.global index) := by
  intro info start finish source initial before generated builder
  exact emitted_checked_lowerPlace_global source results builder

theorem emitted_source_read {env : Core.TEnv} {results : List Ty} (place : Place)
    (child : EmittedSourcePlace env results place) : EmittedSourceExpression env results (.read place) := by
  intro type start finish source initial before generated builder
  obtain ⟨info, childFinish, childSource, _⟩ := tyExpr_read_place source
  exact emitted_checked_read_source (emitted_source_results env results) childSource generated
    (child childSource generated builder)

theorem emitted_source_reference {env : Core.TEnv} {results : List Ty} (requested : Mutability) (place : Place)
    (child : EmittedSourcePlace env results place) : EmittedSourceExpression env results (.ref requested place) := by
  intro type start finish source initial before generated builder
  obtain ⟨info, childFinish, childSource, _, _⟩ := tyExpr_ref_place source
  exact emitted_checked_lowerExpr_ref requested place (child childSource generated builder)

theorem emitted_source_field {env : Core.TEnv} {results : List Ty} (place : Place) (field : Nat)
    (child : EmittedSourcePlace env results place) : EmittedSourcePlace env results (.field place field) := by
  intro info start finish source initial before generated builder
  exact emitted_checked_field_source (emitted_source_results env results) source child generated builder

theorem emitted_source_index {env : Core.TEnv} {results : List Ty} (view : View) (index : Expr) (origin : OriginId)
    (viewChild : EmittedSourceView env results view) (indexChild : EmittedSourceExpression env results index) :
    EmittedSourcePlace env results (.elem view index origin) := by
  intro info start finish source initial before generated builder
  exact emitted_checked_index_source (emitted_source_results env results) source viewChild indexChild generated builder

theorem emitted_source_dereference {env : Core.TEnv} {results : List Ty} (expr : Expr)
    (child : EmittedSourceExpression env results expr) : EmittedSourcePlace env results (.deref expr) := by
  intro info start finish source initial before generated builder
  cases special : Core.sliceRefTy env expr with
  | none =>
    obtain ⟨mu, childFinish, childSource⟩ := tyPlace_deref_child special source
    exact child childSource generated builder
  | some type =>
    cases expr with
    | read place =>
      cases place with
      | var index =>
        obtain ⟨localVar, row, _, visible⟩ := sliceRefTy_variable_row special
        have variableSource : Core.tyPlace env (.var index) start =
            .ok (⟨localVar.ty, localVar.kind == .mutable, true⟩, start) := by
          simp [Core.tyPlace, Core.varOf, List.contains_iff_mem, visible, row,
            pure, StateT.pure, Except.pure, bind, StateT.bind, Except.bind]
        exact emitted_checked_read_source (emitted_source_results env results) variableSource generated
          (emitted_checked_lowerPlace_var variableSource results builder)
      | _ => simp [Core.sliceRefTy] at special
    | _ => simp [Core.sliceRefTy] at special

theorem emitted_source_view_of {env : Core.TEnv} {results : List Ty} (place : Place)
    (child : EmittedSourcePlace env results place) : EmittedSourceView env results (.of place) := by
  intro element writable start finish source initial before generated builder
  exact emitted_checked_view_of_source (emitted_source_results env results) source child generated builder

theorem emitted_source_view_val {env : Core.TEnv} {results : List Ty} (expr : Expr)
    (child : EmittedSourceExpression env results expr) : EmittedSourceView env results (.val expr) := by
  intro element writable start finish source initial before generated builder
  exact emitted_checked_view_val_source (emitted_source_results env results) source child generated builder

theorem emitted_source_length {env : Core.TEnv} {results : List Ty} (view : View)
    (child : EmittedSourceView env results view) : EmittedSourceExpression env results (.len view) := by
  intro type start finish source initial before generated builder
  exact emitted_checked_len_source (emitted_source_results env results) source child generated builder

end Goose.Lower.Validation
