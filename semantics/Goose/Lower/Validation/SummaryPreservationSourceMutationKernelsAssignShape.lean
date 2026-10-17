import Goose.Lower.Validation.SummaryPreservationSourceMutationKernelsCommon

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

private theorem derefVar_shape {place : Place} {x : VarId} (row : place.derefVar? = some x) :
    place = .deref (.read (.var x)) := by
  cases place with
  | deref expression =>
    cases expression <;> try { simp [Place.derefVar?] at row }
    rename_i inner
    cases inner <;> simp [Place.derefVar?] at row
    subst x
    rfl
  | _ => simp [Place.derefVar?] at row

theorem mutation_assign_source_cases {typingEnv : TEnv} {env : PEnv} {place : Place} {info : PlaceInfo}
    {start finish : Nat} (tables : SourceRootTables typingEnv env)
    (typed : tyPlace typingEnv place start = .ok (info, finish))
    (shape : (info.ty.flat || info.ty.isSlice && place.derefVar?.isSome) = true) :
    info.ty.isRefLike = false ∨ ∃ x localVar,
      place = .deref (.read (.var x)) ∧ env.impl.vars[x]? = some localVar ∧ localVar.ty.isRefSlice = true := by
  by_cases nonref : info.ty.isRefLike = false
  · exact Or.inl nonref
  · have slice : info.ty.isSlice = true ∧ place.derefVar?.isSome = true := by
      cases type : info.ty <;> simp_all [Ty.isRefLike, Ty.isSlice, Ty.flat]
    obtain ⟨x, variableRow⟩ := Option.isSome_iff_exists.mp slice.2
    have placeEq := derefVar_shape variableRow
    have access := tyPlace_accessType tables.moduleEq.symm tables.variablesEq.symm typed
    rw [placeEq] at access
    cases localRow : env.impl.vars[x]? with
    | none => simp [PEnv.access, AccessEnv.placeType?, AccessEnv.exprType?, localRow] at access
    | some localVar =>
      refine Or.inr ⟨_, localVar, placeEq, localRow, ?_⟩
      simp only [PEnv.access, AccessEnv.placeType?, AccessEnv.exprType?, localRow, Option.map_some] at access
      cases type : localVar.ty <;> simp only [type, bind, Option.bind] at access <;> try contradiction
      rename_i mutability referent
      have same : referent = info.ty := Option.some.inj access
      have referentSlice : referent.isSlice = true := same.symm ▸ slice.1
      cases referent <;> simp_all [Ty.isSlice, Ty.isRefSlice]

end Goose.Lower.Validation.SummaryPreservation
