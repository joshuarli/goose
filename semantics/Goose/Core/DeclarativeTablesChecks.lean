import Goose.Core.DeclarativeTables

namespace Goose.Core.DeclarativeTablesChecks

private def main : Impl :=
  { name := "main", params := #[], results := #[], vars := #[],
    body := .mk 0 [] none, summary := .unknown }

private def base : Module :=
  { files := #["tables.goose"], types := #[], globals := #[], impls := #[main],
    contexts := #[⟨0, "main", [], [], []⟩], entry := 0, origins := #[⟨0, 1, "test"⟩] }

private def referenceSlice : Ty := .ref .mutable (.slice .mutable (.int .i64))

private def receiver : Impl :=
  { main with
    name := "receiver", params := #[⟨0, .byRef⟩],
    vars := #[⟨"p", referenceSlice, .immutable, 0, 0⟩] }

private def legalReferenceSlice : Module :=
  { base with impls := #[main, receiver], contexts := #[⟨0, "main", [], [], []⟩,
    ⟨1, "receiver", [(0, [.param 0])], [], [(0, [.param 0])]⟩] }

private def unusedReferenceSlice : Module :=
  { base with impls := #[{ main with vars := receiver.vars }] }

private def unusedBadOrigin : Module :=
  { base with impls := #[{ main with vars := #[⟨"unused", .int .i64, .immutable, 0, 1⟩] }] }

private def unusedBadScope : Module :=
  { base with impls := #[{ main with vars := #[⟨"unused", .int .i64, .immutable, 1, 0⟩] }] }

private def overlappingDescriptor : StructDef :=
  { byteSize := 16,
    fields := #[⟨.int .i64, .immutable, .readOnly, 0⟩,
      ⟨.int .i64, .immutable, .readOnly, 0⟩] }

private def badLayout : Module :=
  { base with profile := .shrink, structs := #[overlappingDescriptor] }

private def nominalMismatch : Module :=
  { base with
    profile := .shrink, types := #[.structT 0 (.cons (.int .i64) .nil)],
    structs := #[{ overlappingDescriptor with fields := #[] }] }

theorem legalReferenceSliceParameter : ParameterModeType .byRef referenceSlice := by
  simp [ParameterModeType, referenceSlice, Ty.isSlice, Ty.flat]

#guard (validate legalReferenceSlice).isOk

theorem legalReferenceSliceIsNotStorable : referenceSlice.storable = false := by decide

theorem legalReferenceSliceVariable : ImplementationTables legalReferenceSlice receiver := by
  constructor
  · decide
  · simp [receiver, main]
  · intro i p parameter
    have atZero : i = 0 := by
      have bound := (Array.getElem?_eq_some_iff.1 parameter).1
      simp [receiver] at bound
      omega
    subst i
    have same : p = ⟨0, .byRef⟩ := by simpa [receiver] using parameter.symm
    subst p
    exact ⟨rfl, ⟨"p", referenceSlice, .immutable, 0, 0⟩, rfl, rfl,
      legalReferenceSliceParameter⟩
  · intro i lv variableAt
    have atZero : i = 0 := by
      have bound := (Array.getElem?_eq_some_iff.1 variableAt).1
      simp [receiver] at bound
      omega
    subst i
    have same : lv = ⟨"p", referenceSlice, .immutable, 0, 0⟩ := by
      simpa [receiver] using variableAt.symm
    subst lv
    exact Or.inr ⟨by decide, ⟨0, .byRef⟩, rfl, rfl, rfl⟩
  · intro lv member
    simp [receiver] at member
    subst lv
    decide
  · rfl
  · exact .cons (by simp) (.nil 1)
  · intro lv member
    simp [receiver] at member
    subst lv
    decide

theorem unusedReferenceSliceRejected : ¬ DeclarativeTables unusedReferenceSlice := by
  intro tables
  have metadata := tables.implementations (unusedReferenceSlice.impls[0]'(by decide)) (by simp [unusedReferenceSlice])
  have variableType := metadata.variables 0 (receiver.vars[0]'(by decide)) (by rfl)
  simp [unusedReferenceSlice, receiver, main, referenceSlice, Ty.storable,
    Ty.refTarget] at variableType

theorem unusedOriginRejected : ¬ DeclarativeTables unusedBadOrigin := by
  intro tables
  have metadata := tables.implementations (unusedBadOrigin.impls[0]'(by decide)) (by simp [unusedBadOrigin])
  have origin := metadata.origins ⟨"unused", .int .i64, .immutable, 0, 1⟩ (by simp [unusedBadOrigin, main])
  simp [unusedBadOrigin, base] at origin

theorem unusedScopeRejected : ¬ DeclarativeTables unusedBadScope := by
  intro tables
  have metadata := tables.implementations (unusedBadScope.impls[0]'(by decide)) (by simp [unusedBadScope])
  have scope := metadata.variableScopes ⟨"unused", .int .i64, .immutable, 1, 0⟩ (by simp [unusedBadScope, main])
  simp [unusedBadScope, main, blockScopes, stmtsScopes] at scope

theorem overlappingLayoutRejected : ¬ DeclarativeTables badLayout := by
  intro tables
  obtain ⟨_, layout⟩ := tables.descriptors overlappingDescriptor (by simp [badLayout])
  cases layout with
  | cons _ _ size _ _ _ rest =>
    simp [Module.fixedByteSize?, IntTy.bits] at size
    subst size
    cases rest with
    | cons _ _ _ _ ordered _ _ =>
      simp at ordered

theorem nominalPayloadMismatchRejected : ¬ DeclarativeTables nominalMismatch := by
  intro tables
  have resolved := tables.types (.structT 0 (.cons (.int .i64) .nil)) (by simp [nominalMismatch])
  simp [ResolvedType, nominalMismatch, Module.structType?, overlappingDescriptor,
    TyList.ofList] at resolved

theorem nonDenseScopesRejected : ¬ DenseScopes 0 [(0, none), (2, some 0)] := by
  intro scopes
  cases scopes with
  | cons _ rest => cases rest

theorem nonEarlierParentRejected : ¬ DenseScopes 0 [(0, none), (1, some 1)] := by
  intro scopes
  cases scopes with
  | cons _ rest =>
    cases rest with
    | cons earlier _ => have := earlier 1 rfl; omega

#print axioms validate_declarativeTables
#print axioms resolvedType_iff
#print axioms legalReferenceSliceVariable
#print axioms legalReferenceSliceParameter
#print axioms unusedReferenceSliceRejected
#print axioms overlappingLayoutRejected

end Goose.Core.DeclarativeTablesChecks
