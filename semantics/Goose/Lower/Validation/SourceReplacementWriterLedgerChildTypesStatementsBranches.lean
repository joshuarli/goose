import Goose.Lower.Validation.SourceReplacementWriterLedgerChildTypesStatements

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR ReplacementContentFlowSource

theorem Fragment.ifS_child_span_types {loop : Option LoopCtx} {condition : Expr} {yes : Core.Block}
    {no : Option Core.Block} {origin : OriginId} {child : Fragment}
    {env : LEnv} {before start : LS} {index : Nat}
    (row : (Fragment.statement loop (.ifS condition yes no origin)).child? env before index = some (child, start)) :
    TypePrefix before start ∧ TypePrefix (child.finish env start) ((Fragment.statement loop (.ifS condition yes no origin)).finish env before) := by
  have member := Fragment.child_member row
  simp only [Fragment.children, List.mem_cons] at member
  rcases member with same | member
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
    cases no with
    | none => exact ⟨.refl _, bind_suffix_ext_types (lowerExpr condition) _
        (fun value => types_ifS_none_core value (types_lowerBlock loop [] false yes)) env _⟩
    | some no => exact ⟨.refl _, bind_suffix_ext_types (lowerExpr condition) _
        (fun value => types_ifS_some_core value (types_lowerBlock loop [] false yes)
          (types_lowerBlock loop [] false no)) env _⟩
  · unfold branchChildren at member
    split at member
    · rename_i live
      let tested := lowerExpr condition env before
      let split := fork tested.1 env tested.2
      let yesStart := (setCur (some split.1.1) env split.2).2
      let yesOut := lowerBlock loop [] false yes env yesStart
      have startSpan : TypePrefix before yesStart := (types_lowerExpr condition env before _ _ rfl).trans
        ((types_fork tested.1 env tested.2 _ _ rfl).trans (setCur_extension_types _ _ _))
      obtain ⟨current, currentAt⟩ := Option.isSome_iff_exists.mp live
      cases no with
      | none =>
        change some (child, start) ∈ [some (.block loop [] false yes, yesStart), none] at member
        simp only [List.mem_cons, List.not_mem_nil, or_false, Option.some_ne_none, or_false] at member
        obtain ⟨rfl, same⟩ := Prod.mk.inj (Option.some.inj member)
        subst start
        have whole : ((Fragment.statement loop (.ifS condition yes none origin)).finish env before) =
            (setCur (some split.1.2) env (emitTerm (.br split.1.2 []) env yesOut.2).2).2 := by
          simp only [Fragment.finish, lowerStmt, bind_run, whenLive_some _ _ _ currentAt]
          rfl
        rw [whole]
        exact ⟨startSpan, (types_emitTerm _ env yesOut.2 _ _ rfl).trans (setCur_extension_types _ _ _)⟩
      | some no =>
        let noStart := (setCur (some split.1.2) env yesOut.2).2
        let noOut := lowerBlock loop [] false no env noStart
        have whole : ((Fragment.statement loop (.ifS condition yes (some no) origin)).finish env before) =
            (joinArms yesOut.2.cur noOut.2.cur env noOut.2).2 := by
          simp only [Fragment.finish, lowerStmt, bind_run, whenLive_some _ _ _ currentAt, curBlock_run]
          rfl
        have between : TypePrefix yesOut.2 noStart := setCur_extension_types _ _ _
        have endSpan : TypePrefix noOut.2 ((Fragment.statement loop (.ifS condition yes (some no) origin)).finish env before) := by
          rw [whole]
          exact types_joinArms _ _ _ _ _ _ rfl
        change some (child, start) ∈ [some (.block loop [] false yes, yesStart), some (.block loop [] false no, noStart)] at member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with same | same
        · obtain ⟨rfl, same⟩ := Prod.mk.inj (Option.some.inj same)
          subst start
          exact ⟨startSpan, between.trans ((types_lowerBlock loop [] false no env noStart _ _ rfl).trans endSpan)⟩
        · obtain ⟨rfl, same⟩ := Prod.mk.inj (Option.some.inj same)
          subst start
          exact ⟨startSpan.trans ((types_lowerBlock loop [] false yes env yesStart _ _ rfl).trans between), endSpan⟩
    · simp at member

#print axioms Fragment.ifS_child_span_types

end Goose.Lower.Validation.SourceReplacementWriterLedger
