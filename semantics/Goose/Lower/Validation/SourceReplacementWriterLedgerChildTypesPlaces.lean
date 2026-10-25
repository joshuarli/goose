import Goose.Lower.Validation.SourceReplacementWriterLedgerChildTypes

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR

theorem Fragment.place_child_span_types {place : Place} {child : Fragment} {env : LEnv} {before start : LS}
    {index : Nat} (row : (Fragment.place place).child? env before index = some (child, start)) :
    TypePrefix before start ∧ TypePrefix (child.finish env start) ((Fragment.place place).finish env before) := by
  have member := Fragment.child_member row
  cases place with
  | var variableId => simp [Fragment.children] at member
  | global globalId => simp [Fragment.children] at member
  | deref expression =>
    simp only [Fragment.children, List.mem_singleton] at member
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj member)
    exact ⟨.refl _, .refl _⟩
  | field owner fieldIndex =>
    simp only [Fragment.children, List.mem_singleton] at member
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj member)
    exact ⟨.refl _, bind_suffix_ext_types (lowerPlace owner)
      (fun value => emitDef (.fieldAddr value fieldIndex)) (fun _ => types_emitDef _) env _⟩
  | elem view expression origin =>
    simp only [Fragment.children, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
      exact ⟨.refl _, bind_suffix_ext_types (lowerView view)
        (fun value => do let offset ← lowerExpr expression; emitDef (.indexChecked value offset (some origin)))
        (fun _ => TypeRun.bind (types_lowerExpr expression) (fun _ => types_emitDef _)) env _⟩
    · obtain ⟨rfl, same⟩ := Prod.mk.inj (Option.some.inj same)
      subst start
      refine ⟨(types_lowerView view env before _ _ rfl), ?_⟩
      exact bind_suffix_ext_types (lowerExpr expression)
        (fun offset => emitDef (.indexChecked (lowerView view env before).1 offset (some origin)))
        (fun _ => types_emitDef _) env _

theorem Fragment.view_child_span_types {view : View} {child : Fragment} {env : LEnv} {before start : LS}
    {index : Nat} (row : (Fragment.view view).child? env before index = some (child, start)) :
    TypePrefix before start ∧ TypePrefix (child.finish env start) ((Fragment.view view).finish env before) := by
  have member := Fragment.child_member row
  cases view with
  | of place =>
    simp only [Fragment.children, List.mem_singleton] at member
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj member)
    refine ⟨.refl _, ?_⟩
    cases place <;> exact bind_suffix_ext_types _ (fun value => emitDef (.snapshot _ value))
      (fun _ => types_emitDef _) env _
  | val expression =>
    simp only [Fragment.children, List.mem_singleton] at member
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj member)
    exact ⟨.refl _, bind_suffix_ext_types (lowerExpr expression)
      (fun value => emitDef (.sliceView value)) (fun _ => types_emitDef _) env _⟩

theorem Fragment.bound_child_span_types {bound : Bound} {child : Fragment} {env : LEnv} {before start : LS}
    {index : Nat} (row : (Fragment.bound bound).child? env before index = some (child, start)) :
    TypePrefix before start ∧ TypePrefix (child.finish env start) ((Fragment.bound bound).finish env before) := by
  have member := Fragment.child_member row
  cases bound with
  | omitted => simp [Fragment.children] at member
  | expr expression =>
    simp only [Fragment.children, List.mem_singleton] at member
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj member)
    exact ⟨.refl _, bind_suffix_ext_types (lowerExpr expression)
      (fun value => pure (Bnd.val value)) (fun _ => TypeRun.pure _) env _⟩
  | fromEnd expression =>
    simp only [Fragment.children, List.mem_singleton] at member
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj member)
    exact ⟨.refl _, bind_suffix_ext_types (lowerExpr expression)
      (fun value => pure (Bnd.fromEnd value)) (fun _ => TypeRun.pure _) env _⟩

#print axioms Fragment.place_child_span_types
#print axioms Fragment.view_child_span_types
#print axioms Fragment.bound_child_span_types

end Goose.Lower.Validation.SourceReplacementWriterLedger
