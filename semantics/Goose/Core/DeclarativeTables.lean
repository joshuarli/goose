import Goose.Core.Sound.Module

namespace Goose.Core

set_option maxHeartbeats 800000
set_option maxRecDepth 4096

open Sound

mutual

def ResolvedType (m : Module) : Ty → Prop
  | .structT sid fs => m.profile = .shrink ∧ m.structType? sid = some (.structT sid fs) ∧ ResolvedTypes m fs
  | .arr e _ | .grow e | .ref _ e | .slice _ e => ResolvedType m e
  | .growshrink e => m.profile = .shrink ∧ e.flat = true ∧ ResolvedType m e
  | .limited e capacity => m.profile = .shrink ∧ e.flat = true ∧ 0 < capacity ∧ capacity ≤ 2^31 - 1 ∧ ResolvedType m e
  | .tuple ts => ResolvedTypes m ts
  | .int _ | .bool | .unit => True

def ResolvedTypes (m : Module) : TyList → Prop
  | .nil => True
  | .cons t ts => ResolvedType m t ∧ ResolvedTypes m ts

end

inductive DescriptorLayout (m : Module) (byteSize : Nat) : Nat → List StructField → Prop
  | nil (offset) : DescriptorLayout m byteSize offset []
  | cons {offset field rest bytes} :
      ResolvedType m field.ty → field.ty.flat = true →
      m.fixedByteSize? field.ty = some bytes → 0 < bytes →
      offset ≤ field.byteOffset → field.byteOffset + bytes ≤ byteSize →
      DescriptorLayout m byteSize (field.byteOffset + bytes) rest →
      DescriptorLayout m byteSize offset (field :: rest)

inductive DenseScopes : Nat → List (Nat × Option Nat) → Prop
  | nil (next) : DenseScopes next []
  | cons {next parent rest} : (∀ p, parent = some p → p < next) →
      DenseScopes (next + 1) rest → DenseScopes next ((next, parent) :: rest)

def ParameterModeType : Mode → Ty → Prop
  | .byRef, .ref _ target => target.refTarget = true ∨ target.isSlice = true
  | .byRef, _ => False
  | .byValue, .ref _ _ | .byValue, .grow _ | .byValue, .growshrink _ | .byValue, .limited _ _ => False
  | .byValue, ty => ty.storable = true

structure ImplementationTables (m : Module) (impl : Impl) : Prop where
  resultsCount : impl.results.size ≤ 1
  results : ∀ ty ∈ impl.results.toList, ty.readable = true ∧ ty ≠ .unit
  parameters : ∀ (i : Nat) (p : Param), impl.params[i]? = some p → p.var = i ∧
    ∃ lv : LocalVar, impl.vars[i]? = some lv ∧ lv.scope = 0 ∧ ParameterModeType p.mode lv.ty
  variables : ∀ (i : Nat) (lv : LocalVar), impl.vars[i]? = some lv → lv.ty.storable = true ∨
    (lv.ty.isRefSlice = true ∧ ∃ p : Param, impl.params[i]? = some p ∧ p.var = i ∧ p.mode = .byRef)
  origins : ∀ lv ∈ impl.vars.toList, lv.org < m.origins.size
  bodyScope : impl.body.scope = 0
  scopes : DenseScopes 0 (blockScopes none impl.body)
  variableScopes : ∀ lv ∈ impl.vars.toList, lv.scope < (blockScopes none impl.body).length

structure GlobalTables (m : Module) (gl : Global) : Prop where
  storedType : gl.ty.storable = true
  ownsContents : gl.ty.isRefLike = false
  origin : gl.org < m.origins.size
  scopes : DenseScopes 0 (exprScopes none gl.init)

structure DeclarativeTables (m : Module) : Prop where
  pilotStructs : m.profile = .pilot → m.structs = #[]
  descriptors : ∀ d ∈ m.structs.toList, 0 < d.byteSize ∧ DescriptorLayout m d.byteSize 0 d.fields.toList
  types : ∀ ty ∈ m.types.toList, ResolvedType m ty
  globalTypes : ∀ gl ∈ m.globals.toList, ResolvedType m gl.ty
  variableTypes : ∀ impl ∈ m.impls.toList, ∀ lv ∈ impl.vars.toList, ResolvedType m lv.ty
  resultTypes : ∀ impl ∈ m.impls.toList, ∀ ty ∈ impl.results.toList, ResolvedType m ty
  implementations : ∀ impl ∈ m.impls.toList, ImplementationTables m impl
  globals : ∀ gl ∈ m.globals.toList, GlobalTables m gl
  contextBounds : ∀ ctx ∈ m.contexts.toList, ctx.impl < m.impls.size
  contextCoverage : ∀ i, i < m.impls.size → ∃ ctx ∈ m.contexts.toList, ctx.impl = i
  entry : ∃ ctx impl, m.contexts[m.entry]? = some ctx ∧ m.impls[ctx.impl]? = some impl ∧
    impl.params.size = 0 ∧ impl.results.toList = []

mutual

private theorem resolvedType_of_check (m : Module) : ∀ t,
    checkResolvedType m t = .ok () → ResolvedType m t
  | .int _, _ | .bool, _ | .unit, _ => trivial
  | .arr e _, h | .grow e, h | .ref _ e, h | .slice _ e, h => resolvedType_of_check m e h
  | .tuple ts, h => resolvedTypes_of_check m ts h
  | .structT sid fs, h => by
    simp only [checkResolvedType] at h
    inv at h
    obtain ⟨hp, hd, hf⟩ := h
    exact ⟨eq_of_beq hp, eq_of_beq hd, resolvedTypes_of_check m fs hf⟩
  | .growshrink e, h => by
    simp only [checkResolvedType] at h
    inv at h
    obtain ⟨hp, he⟩ := h
    simp only [Bool.and_eq_true] at hp
    exact ⟨eq_of_beq hp.1, hp.2, resolvedType_of_check m e he⟩
  | .limited e capacity, h => by
    simp only [checkResolvedType] at h
    inv at h
    obtain ⟨hp, he⟩ := h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    exact ⟨eq_of_beq hp.1.1.1, hp.1.1.2, hp.1.2, hp.2, resolvedType_of_check m e he⟩

private theorem resolvedTypes_of_check (m : Module) : ∀ ts,
    checkResolvedTypes m ts = .ok () → ResolvedTypes m ts
  | .nil, _ => trivial
  | .cons t ts, h => by
    simp only [checkResolvedTypes] at h
    inv at h
    exact ⟨resolvedType_of_check m t h.1, resolvedTypes_of_check m ts h.2⟩

end

mutual

private theorem check_of_resolvedType (m : Module) : ∀ t,
    ResolvedType m t → checkResolvedType m t = .ok ()
  | .int _, _ | .bool, _ | .unit, _ => rfl
  | .arr e _, h | .grow e, h | .ref _ e, h | .slice _ e, h => check_of_resolvedType m e h
  | .tuple ts, h => check_of_resolvedTypes m ts h
  | .structT sid fs, ⟨profile, descriptor, fields⟩ => by
    simp [checkResolvedType, profile, descriptor, check_of_resolvedTypes m fs fields,
      pure, Except.pure, bind, Except.bind]
  | .growshrink e, ⟨profile, flat, element⟩ => by
    simp [checkResolvedType, profile, flat, check_of_resolvedType m e element,
      pure, Except.pure, bind, Except.bind]
  | .limited e capacity, ⟨profile, flat, positive, bounded, element⟩ => by
    simp [checkResolvedType, profile, flat, positive, bounded, check_of_resolvedType m e element,
      pure, Except.pure, bind, Except.bind]

private theorem check_of_resolvedTypes (m : Module) : ∀ ts,
    ResolvedTypes m ts → checkResolvedTypes m ts = .ok ()
  | .nil, _ => rfl
  | .cons t ts, ⟨head, rest⟩ => by
    simp [checkResolvedTypes, check_of_resolvedType m t head, check_of_resolvedTypes m ts rest,
      pure, Except.pure, bind, Except.bind]

end

theorem resolvedType_iff (m : Module) (ty : Ty) :
    ResolvedType m ty ↔ checkResolvedType m ty = .ok () :=
  ⟨check_of_resolvedType m ty, resolvedType_of_check m ty⟩

private theorem denseScopes_of_check : ∀ pairs next,
    scopeOrderError pairs next = none → DenseScopes next pairs
  | [], next, _ => .nil next
  | (scope, parent) :: rest, next, h => by
    simp only [scopeOrderError] at h
    split at h
    · contradiction
    · rename_i same
      have equal : scope = next := by simpa using same
      subst scope
      cases parent with
      | none => exact .cons (by simp) (denseScopes_of_check rest (next + 1) h)
      | some p =>
        simp only at h
        split at h
        · exact .cons (by intro q equal; cases equal; assumption)
            (denseScopes_of_check rest (next + 1) h)
        · contradiction

private theorem parameter_of_check (impl : Impl) (i : Nat) (p : Param)
    (h : checkParam impl i = .ok ()) (hp : impl.params[i]? = some p) :
    p.var = i ∧ ∃ lv : LocalVar, impl.vars[i]? = some lv ∧ lv.scope = 0 ∧ ParameterModeType p.mode lv.ty := by
  unfold checkParam at h
  simp only [hp] at h
  cases hv : impl.vars[i]? with
  | none => simp only [hv] at h; inv at h
  | some lv =>
    simp only [hv] at h
    inv at h
    obtain ⟨hi, hs, ht⟩ := h
    refine ⟨hi, lv, rfl, hs, ?_⟩
    cases hm : p.mode <;> cases hty : lv.ty <;> simp only [hm, hty] at ht <;>
      inv at ht <;> first | exact ht | simpa only [ParameterModeType, Bool.or_eq_true] using ht

private theorem implementationTables_of_check (m : Module) (impl : Impl)
    (h : checkImpl m impl = .ok ()) : ImplementationTables m impl := by
  unfold checkImpl at h
  cases hscope : scopeOrderError (blockScopes none impl.body) 0 with
  | some message => simp only [hscope] at h; inv at h
  | none =>
    simp only [hscope] at h
    inv at h
    obtain ⟨count, results, params, vars, origins, bodyScope, scopes, _, _, _, _⟩ := h
    refine ⟨by omega, ?_, ?_, ?_, ?_, bodyScope, denseScopes_of_check _ _ hscope, ?_⟩
    · intro ty member
      have ht := (forAll_ok _ _).1 results ty member
      inv at ht
      simpa only [Bool.and_eq_true, bne_iff_ne] using ht
    · intro i p hp
      exact parameter_of_check impl i p
        ((forAll_ok _ _).1 params i (List.mem_range.2 (Array.getElem?_eq_some_iff.1 hp).1)) hp
    · intro i lv hv
      have member : (lv, i) ∈ impl.vars.toList.zipIdx := by
        apply List.mk_mem_zipIdx_iff_getElem?.2
        simpa only [Array.getElem?_toList] using hv
      have ht := (forAll_ok _ _).1 vars (lv, i) member
      inv at ht
      simp only [Bool.or_eq_true, Bool.and_eq_true] at ht
      rcases ht with stored | ⟨refSlice, parameter⟩
      · exact Or.inl stored
      · right
        refine ⟨refSlice, ?_⟩
        cases hp : impl.params[i]? with
        | none => simp [hp] at parameter
        | some p =>
          simp only [hp, Bool.and_eq_true, beq_iff_eq] at parameter
          exact ⟨p, rfl, parameter⟩
    · intro lv member
      have ht := (forAll_ok _ _).1 origins lv member
      inv at ht
      exact ht
    · intro lv member
      have ht := (forAll_ok _ _).1 scopes lv member
      inv at ht
      exact ht

private theorem globalTables_of_check (m : Module) (g : Nat) (gl : Global)
    (h : checkGlobal m g gl = .ok ()) : GlobalTables m gl := by
  unfold checkGlobal at h
  cases hscope : scopeOrderError (exprScopes none gl.init) 0 with
  | some message => simp only [hscope] at h; inv at h
  | none =>
    simp only [hscope] at h
    inv at h
    obtain ⟨ht, ho, _, _, _, _⟩ := h
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at ht
    exact ⟨ht.1, ht.2, ho, denseScopes_of_check _ _ hscope⟩

private theorem forInUnit_facts {α : Type} {xs : List α}
    {body : α → PUnit.{1} → V (ForInStep PUnit.{1})}
    (h : forIn xs PUnit.unit body = .ok PUnit.unit)
    (yields : ∀ value accumulator step, body value accumulator = .ok step → step = .yield PUnit.unit) :
    ∀ value ∈ xs, body value PUnit.unit = .ok (.yield PUnit.unit) := by
  induction xs with
  | nil => simp
  | cons head tail ih =>
    rw [List.forIn_cons] at h
    obtain ⟨step, first, rest⟩ := (ex_bind_ok _ _ _).1 h
    have same := yields head PUnit.unit step first
    subst step
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact first
    · exact ih rest value member

private theorem forIn_layout (m : Module) (byteSize : Nat) (fields : List StructField)
    (body : StructField → Nat → V (ForInStep Nat))
    (stepFacts : ∀ field offset step, body field offset = .ok step →
      ∃ bytes, ResolvedType m field.ty ∧ field.ty.flat = true ∧
      m.fixedByteSize? field.ty = some bytes ∧ 0 < bytes ∧ offset ≤ field.byteOffset ∧
      field.byteOffset + bytes ≤ byteSize ∧ step = .yield (field.byteOffset + bytes)) :
    ∀ offset out, forIn fields offset body = .ok out → DescriptorLayout m byteSize offset fields := by
  induction fields with
  | nil => intro offset out h; exact .nil offset
  | cons field rest ih =>
    intro offset out h
    rw [List.forIn_cons] at h
    obtain ⟨step, first, tail⟩ := (ex_bind_ok _ _ _).1 h
    obtain ⟨bytes, resolved, flat, size, positive, ordered, bounded, rfl⟩ := stepFacts field offset step first
    exact .cons resolved flat size positive ordered bounded (ih _ _ tail)

private theorem structTables_of_check (m : Module) (h : checkStructTables m = .ok ()) :
    (m.profile = .pilot → m.structs = #[]) ∧
    (∀ d ∈ m.structs.toList, 0 < d.byteSize ∧ DescriptorLayout m d.byteSize 0 d.fields.toList) ∧
    (∀ t ∈ m.types.toList, ResolvedType m t) ∧
    (∀ gl ∈ m.globals.toList, ResolvedType m gl.ty) ∧
    (∀ impl ∈ m.impls.toList, ∀ lv ∈ impl.vars.toList, ResolvedType m lv.ty) ∧
    (∀ impl ∈ m.impls.toList, ∀ t ∈ impl.results.toList, ResolvedType m t) := by
  unfold checkStructTables at h
  inv at h
  obtain ⟨profile, descriptors, types, globals, implementations⟩ := h
  have descriptorFacts := forInUnit_facts (xs := m.structs.toList) (by simpa only [Array.forIn_toList] using descriptors) (by
    intro d accumulator step checked
    inv at checked
    exact checked.2.choose_spec.2)
  have globalFacts := forInUnit_facts (xs := m.globals.toList)
    (by simpa only [Array.forIn_toList] using globals) (by
      intro gl accumulator step checked
      inv at checked
      exact checked.2)
  have implementationFacts := forInUnit_facts (xs := m.impls.toList)
    (by simpa only [Array.forIn_toList] using implementations) (by
      intro impl accumulator step checked
      inv at checked
      exact checked.2.2)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro pilot
    simp only [pilot, beq_self_eq_true, Bool.true_and, Bool.not_eq_true'] at profile
    have empty : m.structs.isEmpty = true := by
      cases he : m.structs.isEmpty
      · simp only [he, Bool.false_eq_true, not_false_eq_true, not_true_eq_false] at profile
      · rfl
    exact Array.eq_empty_of_size_eq_zero (Array.isEmpty_iff_size_eq_zero.1 empty)
  · intro d member
    have checked := descriptorFacts d member
    inv at checked
    obtain ⟨positive, offset, fields⟩ := checked
    refine ⟨Nat.pos_of_ne_zero (by simpa only [beq_iff_eq] using positive), ?_⟩
    apply forIn_layout m d.byteSize d.fields.toList _ ?_ 0 offset
      (by simpa only [Array.forIn_toList] using fields)
    intro field previous step checked
    inv at checked
    obtain ⟨resolved, flat, checked⟩ := checked
    cases size : m.fixedByteSize? field.ty with
    | none => simp only [size] at checked; inv at checked
    | some bytes =>
      simp only [size] at checked
      inv at checked
      have positive : bytes ≠ 0 := by simpa only [beq_iff_eq] using checked.1
      exact ⟨bytes, resolvedType_of_check m field.ty resolved, flat, rfl,
        by omega, by omega, by omega, checked.2.2.2⟩
  · intro t member
    exact resolvedType_of_check m t ((forAll_ok _ _).1 types t member)
  · intro gl member
    have checked := globalFacts gl member
    inv at checked
    exact resolvedType_of_check m gl.ty checked
  · intro impl member lv localMember
    have checked := implementationFacts impl member
    inv at checked
    have each := forInUnit_facts (xs := impl.vars.toList)
      (by simpa only [Array.forIn_toList] using checked.1) (by
        intro value accumulator step h
        inv at h
        exact h.2)
    have checked := each lv localMember
    inv at checked
    exact resolvedType_of_check m lv.ty checked
  · intro impl member t result
    have checked := implementationFacts impl member
    inv at checked
    have each := forInUnit_facts (xs := impl.results.toList)
      (by simpa only [Array.forIn_toList] using checked.2) (by
        intro value accumulator step h
        inv at h
        exact h.2)
    have checked := each t result
    inv at checked
    exact resolvedType_of_check m t checked
theorem validate_declarativeTables (m : Module) (h : validate m = .ok ()) : DeclarativeTables m := by
  unfold validate at h
  inv at h
  obtain ⟨structs, entry, coverage, globals, implementations, contexts, _, _⟩ := h
  obtain ⟨pilotStructs, descriptors, types, globalTypes, variableTypes, resultTypes⟩ :=
    structTables_of_check m structs
  refine ⟨pilotStructs, descriptors, types, globalTypes, variableTypes, resultTypes, ?_, ?_, ?_, ?_,
    checkEntry_ok m entry⟩
  · intro impl member
    exact implementationTables_of_check m impl ((forAll_ok _ _).1 implementations impl member)
  · intro gl member
    obtain ⟨g, hg⟩ := Array.mem_iff_getElem?.1 (Array.mem_toList_iff.1 member)
    have bound := (Array.getElem?_eq_some_iff.1 hg).1
    have checked := (forAll_ok _ _).1 globals g (List.mem_range.2 bound)
    simp only [hg] at checked
    exact globalTables_of_check m g gl checked
  · intro ctx member
    obtain ⟨impl, hi, _⟩ := checkContext_ok m ctx ((forAll_ok _ _).1 contexts ctx member)
    exact (Array.getElem?_eq_some_iff.1 hi).1
  · intro i bound
    unfold checkImplementationContexts at coverage
    have checked := (forAll_ok _ _).1 coverage i (List.mem_range.2 bound)
    inv at checked
    simpa only [List.any_eq_true, beq_iff_eq] using checked

end Goose.Core
