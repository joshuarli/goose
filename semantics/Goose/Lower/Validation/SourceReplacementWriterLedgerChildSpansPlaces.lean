import Goose.Lower.Validation.SourceReplacementWriterLedgerChildSpans

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR

theorem Fragment.place_child_span {place : Place} {child : Fragment} {env : LEnv} {before start : LS}
    {index : Nat} (row : (Fragment.place place).child? env before index = some (child, start)) :
    before.Ext start ∧ (child.finish env start).Ext ((Fragment.place place).finish env before) := by
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
    exact ⟨.refl _, bind_suffix_ext (lowerPlace owner)
      (fun value => emitDef (.fieldAddr value fieldIndex)) (fun _ => advB_emitDef _) env _⟩
  | elem view expression origin =>
    simp only [Fragment.children, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
      exact ⟨.refl _, bind_suffix_ext (lowerView view)
        (fun value => do let offset ← lowerExpr expression; emitDef (.indexChecked value offset (some origin)))
        (fun _ => AdvB.bind (advB_lowerExpr expression) (fun _ => advB_emitDef _)) env _⟩
    · obtain ⟨rfl, same⟩ := Prod.mk.inj (Option.some.inj same)
      subst start
      refine ⟨(advB_lowerView view env before _ _ rfl).ext, ?_⟩
      exact bind_suffix_ext (lowerExpr expression)
        (fun offset => emitDef (.indexChecked (lowerView view env before).1 offset (some origin)))
        (fun _ => advB_emitDef _) env _

theorem Fragment.view_child_span {view : View} {child : Fragment} {env : LEnv} {before start : LS}
    {index : Nat} (row : (Fragment.view view).child? env before index = some (child, start)) :
    before.Ext start ∧ (child.finish env start).Ext ((Fragment.view view).finish env before) := by
  have member := Fragment.child_member row
  cases view with
  | of place =>
    simp only [Fragment.children, List.mem_singleton] at member
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj member)
    refine ⟨.refl _, ?_⟩
    cases place <;> exact bind_suffix_ext _ (fun value => emitDef (.snapshot _ value))
      (fun _ => advB_emitDef _) env _
  | val expression =>
    simp only [Fragment.children, List.mem_singleton] at member
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj member)
    exact ⟨.refl _, bind_suffix_ext (lowerExpr expression)
      (fun value => emitDef (.sliceView value)) (fun _ => advB_emitDef _) env _⟩

theorem Fragment.bound_child_span {bound : Bound} {child : Fragment} {env : LEnv} {before start : LS}
    {index : Nat} (row : (Fragment.bound bound).child? env before index = some (child, start)) :
    before.Ext start ∧ (child.finish env start).Ext ((Fragment.bound bound).finish env before) := by
  have member := Fragment.child_member row
  cases bound with
  | omitted => simp [Fragment.children] at member
  | expr expression =>
    simp only [Fragment.children, List.mem_singleton] at member
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj member)
    exact ⟨.refl _, bind_suffix_ext (lowerExpr expression)
      (fun value => pure (Bnd.val value)) (fun _ => AdvB.pure _) env _⟩
  | fromEnd expression =>
    simp only [Fragment.children, List.mem_singleton] at member
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj member)
    exact ⟨.refl _, bind_suffix_ext (lowerExpr expression)
      (fun value => pure (Bnd.fromEnd value)) (fun _ => AdvB.pure _) env _⟩

#print axioms Fragment.place_child_span
#print axioms Fragment.view_child_span
#print axioms Fragment.bound_child_span

end Goose.Lower.Validation.SourceReplacementWriterLedger
