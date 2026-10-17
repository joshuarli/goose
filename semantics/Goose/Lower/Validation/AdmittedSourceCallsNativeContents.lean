import Goose.Lower.Validation.AdmittedSourceCallsContentRows

namespace Goose.Lower.Validation.AdmittedSourceCalls

open Goose.Core Goose.GIR

private theorem content_fold_eq {index : Nat} {ceiling : List RootRef}
    (rows : List (Nat × List RootRef)) (initial : List RootRef)
    (matching : ∀ row ∈ rows, row.1 = index → row.2 = ceiling)
    (present : initial = ceiling ∨ (index, ceiling) ∈ rows) :
    rows.foldl (fun roots row => if row.1 == index then row.2 else roots) initial = ceiling := by
  induction rows generalizing initial with
  | nil => simpa using present
  | cons row rest ih =>
      apply ih _
        (fun entry member => matching entry (List.mem_cons_of_mem row member))
      by_cases same : row.1 == index
      · exact .inl (by simpa only [same, ite_true] using matching row (by simp) (eq_of_beq same))
      · simp only [same, ite_false]
        rcases present with equal | member
        · exact .inl equal
        · rcases List.mem_cons.mp member with equal | member
          · cases equal; simp at same
          · exact .inr member

theorem lowerContextAt_contentRoots_eq {module : Core.Module} {context : Context} {impl : Impl}
    {index : Nat} {parameter : Param} {roots : List RootRef}
    (parameterAt : impl.params[index]? = some parameter)
    (annotation : (context.contentRoots.find? (·.1 == parameter.var)).map (·.2) = some roots) :
    (lowerContextAt module context impl).contentRoots index = roots := by
  have nativeRow : (lowerContextAt module context impl).roots.contents.find? (·.1 == index) =
      some (index, roots) := SummaryPreservation.lowerContextRootInfo_contents_eq parameterAt annotation
  have member := Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some nativeRow)
  unfold Func.contentRoots
  rw [← Array.foldl_toList]
  apply content_fold_eq _ _ ?_ (.inr member)
  rintro ⟨actualIndex, actualRoots⟩ actualMember same
  dsimp only at same
  subst actualIndex
  obtain ⟨formal, formalAt, actualAnnotation⟩ := lowerContextAt_content_row_source actualMember
  have sameFormal : formal = parameter := Option.some.inj (formalAt.symm.trans parameterAt)
  subst formal
  exact Option.some.inj (actualAnnotation.symm.trans annotation)

#print axioms lowerContextAt_contentRoots_eq

end Goose.Lower.Validation.AdmittedSourceCalls
