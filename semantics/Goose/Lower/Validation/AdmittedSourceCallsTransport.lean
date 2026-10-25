import Goose.Core.Sound.Invert
import Goose.GIR.AdmittedRegions

namespace Goose.Lower.Validation.AdmittedSourceCalls

open Goose.Core Goose.GIR

theorem checkContent_receiver_bounds
    {env : PEnv} {context : Context} {arguments : List Arg}
    {argumentRoots : List (List RootRef)} {index : Nat} {declared : List RootRef}
    (checked : checkContent env context arguments argumentRoots index = .ok ())
    (row : (context.contentRoots.find? (·.1 == index)).map (·.2) = some declared) :
    ∃ mapped, mapResultRoots argumentRoots [] declared = .ok mapped ∧
      ((∃ mutability slot ceiling,
        arguments[index]? = some (.byRef mutability (.var slot)) ∧
        env.ann slot = some ceiling ∧ mapped ⊆ ceiling ∧ ceiling ⊆ mapped) ∨
      (∃ mutability parameter ceiling,
        arguments[index]? = some (.byRef mutability (.deref (.read (.var parameter)))) ∧
        env.cont parameter = some ceiling ∧ mapped ⊆ ceiling ∧ ceiling ⊆ mapped)) := by
  obtain ⟨mapped, mappedChecked, localReceiver | parameterReceiver⟩ :=
    Sound.checkContent_ok env context arguments argumentRoots index declared checked row
  · obtain ⟨mutability, slot, ceiling, argument, annotation, lower, bound⟩ := localReceiver
    obtain ⟨storage, ceiling', found, annotation', upper, lifetime⟩ :=
      Sound.bindRootsV_ok env env.scopes slot mapped bound
    have same : ceiling' = ceiling := Option.some.inj (annotation'.symm.trans annotation)
    subst ceiling'
    exact ⟨mapped, mappedChecked, .inl
      ⟨mutability, slot, ceiling, argument, annotation, fun _ member => upper _ member, lower⟩⟩
  · obtain ⟨mutability, parameter, ceiling, argument, contents, upper, lower⟩ := parameterReceiver
    exact ⟨mapped, mappedChecked, .inr
      ⟨mutability, parameter, ceiling, argument, contents, upper, lower⟩⟩

theorem checkContents_receiver_bounds
    {env : PEnv} {contextId : ContextId} {context : Context} {arguments : List Arg}
    {argumentRoots : List (List RootRef)} {index : Nat} {declared : List RootRef}
    (checked : checkContents env contextId arguments argumentRoots = .ok ())
    (contextFound : env.mod.contexts[contextId]? = some context)
    (indexBound : index < arguments.length)
    (row : (context.contentRoots.find? (·.1 == index)).map (·.2) = some declared) :
    ∃ mapped, mapResultRoots argumentRoots [] declared = .ok mapped ∧
      ((∃ mutability slot ceiling,
        arguments[index]? = some (.byRef mutability (.var slot)) ∧
        env.ann slot = some ceiling ∧ mapped ⊆ ceiling ∧ ceiling ⊆ mapped) ∨
      (∃ mutability parameter ceiling,
        arguments[index]? = some (.byRef mutability (.deref (.read (.var parameter)))) ∧
        env.cont parameter = some ceiling ∧ mapped ⊆ ceiling ∧ ceiling ⊆ mapped)) := by
  exact checkContent_receiver_bounds
    (Sound.checkContents_ok env contextId arguments argumentRoots context checked contextFound
      index indexBound) row

theorem mapRawContentRoots_refines
    {func : Func} {provenance : Prov} {arguments : List ValueId}
    {argumentRoots : List (List RootRef)} {declared mapped : List RootRef}
    (checked : mapResultRoots argumentRoots [] declared = .ok mapped)
    (argumentBounds : ∀ (index : Nat) (value : ValueId) (source : List RootRef),
      RootRef.param index ∈ declared →
      arguments[index]? = some value → argumentRoots[index]? = some source →
      RootsRefine func (rootsAt provenance.vals value) source) :
    RootsRefine func (mapRawContentRoots provenance arguments declared) mapped := by
  intro root member
  obtain ⟨declaredRoot, declaredMember, mappedMember⟩ :=
    List.mem_flatMap.mp (List.mem_eraseDups.mp member)
  have source := (Sound.mapResultRoots_ok argumentRoots declared [] mapped checked).2
    declaredRoot declaredMember
  cases declaredRoot with
  | «local» slot => simp at mappedMember
  | global global =>
    have same : root = RootRef.global global := List.mem_singleton.mp mappedMember
    subst root
    exact .inl source
  | param index =>
    obtain ⟨sourceRoots, sourceFound, sourceBound⟩ := source
    cases valueFound : arguments[index]? with
    | none => simp [valueFound] at mappedMember
    | some value =>
      simp only [valueFound, Option.map_some, Option.getD_some] at mappedMember
      rcases argumentBounds index value sourceRoots declaredMember valueFound sourceFound root mappedMember with
        literal | expanded
      · exact .inl (sourceBound root literal)
      · exact .inr (fun concrete concreteMember => sourceBound concrete
          (expanded concrete concreteMember))

theorem mapRawContentRoots_refines_reverse
    {func : Func} {provenance : Prov} {arguments : List ValueId}
    {argumentRoots : List (List RootRef)} {declared mapped : List RootRef}
    (checked : mapResultRoots argumentRoots [] declared = .ok mapped)
    (argumentBounds : ∀ (index : Nat) (source : List RootRef),
      RootRef.param index ∈ declared → argumentRoots[index]? = some source →
      ∃ value, arguments[index]? = some value ∧
        RootsRefine func source (rootsAt provenance.vals value)) :
    RootsRefine func mapped (mapRawContentRoots provenance arguments declared) := by
  intro root member
  rcases Sound.mapResultRoots_sub argumentRoots declared [] mapped checked root member with
    empty | ⟨declaredRoot, declaredMember, origin⟩
  · simp at empty
  cases declaredRoot with
  | «local» slot => exact False.elim origin
  | global global =>
    change root = RootRef.global global at origin
    subst root
    exact .inl (List.mem_eraseDups.mpr (List.mem_flatMap.mpr
      ⟨.global global, declaredMember, by simp⟩))
  | param index =>
    obtain ⟨sourceRoots, sourceFound, sourceMember⟩ := origin
    obtain ⟨value, valueFound, bound⟩ := argumentBounds index sourceRoots declaredMember sourceFound
    have included : rootsAt provenance.vals value ⊆
        mapRawContentRoots provenance arguments declared := by
      intro concrete concreteMember
      exact List.mem_eraseDups.mpr (List.mem_flatMap.mpr
        ⟨.param index, declaredMember, by simpa [valueFound] using concreteMember⟩)
    rcases bound root sourceMember with literal | expanded
    · exact .inl (included literal)
    · exact .inr (fun concrete concreteMember => included (expanded concrete concreteMember))

theorem mapRawContentRoots_source_floor
    {provenance : Prov} {arguments : List ValueId}
    {argumentRoots : List (List RootRef)} {declared mapped : List RootRef}
    (checked : mapResultRoots argumentRoots [] declared = .ok mapped)
    (argumentFloors : ∀ (index : Nat) (source : List RootRef),
      RootRef.param index ∈ declared → argumentRoots[index]? = some source →
      ∃ value, arguments[index]? = some value ∧ source ⊆ rootsAt provenance.vals value) :
    mapped ⊆ mapRawContentRoots provenance arguments declared := by
  intro root member
  rcases Sound.mapResultRoots_sub argumentRoots declared [] mapped checked root member with
    empty | ⟨declaredRoot, declaredMember, origin⟩
  · simp at empty
  cases declaredRoot with
  | «local» slot => exact False.elim origin
  | global global =>
    change root = RootRef.global global at origin
    subst root
    exact List.mem_eraseDups.mpr (List.mem_flatMap.mpr
      ⟨.global global, declaredMember, by simp⟩)
  | param index =>
    obtain ⟨sourceRoots, sourceFound, sourceMember⟩ := origin
    obtain ⟨value, valueFound, floor⟩ := argumentFloors index sourceRoots declaredMember sourceFound
    exact List.mem_eraseDups.mpr (List.mem_flatMap.mpr
      ⟨.param index, declaredMember, by simpa [valueFound] using floor sourceMember⟩)

theorem admittedCallReceiver_of_source_bounds
    {func : Func} {provenance : Prov} {arguments : List ValueId}
    {argumentRoots : List (List RootRef)} {declared mapped : List RootRef} {receiver : ValueId}
    (checked : mapResultRoots argumentRoots [] declared = .ok mapped)
    (argumentBounds : ∀ (index : Nat) (value : ValueId) (source : List RootRef),
      RootRef.param index ∈ declared →
      arguments[index]? = some value → argumentRoots[index]? = some source →
      RootsRefine func (rootsAt provenance.vals value) source)
    (argumentFloors : ∀ (index : Nat) (source : List RootRef),
      RootRef.param index ∈ declared → argumentRoots[index]? = some source →
      ∃ value, arguments[index]? = some value ∧ source ⊆ rootsAt provenance.vals value)
    (receiverBounds : ∀ root ∈ rootsAt provenance.vals receiver,
      RootsRefine func (func.receiverContentCeiling provenance root) mapped)
    (receiverFloors : ∀ root ∈ rootsAt provenance.vals receiver,
      mapped ⊆ func.receiverContentCeiling provenance root) :
    func.admittedCallReceiver provenance receiver
      (mapRawContentRoots provenance arguments declared) = true := by
  have mappedBound := mapRawContentRoots_refines checked argumentBounds
  have mappedFloor := mapRawContentRoots_source_floor checked argumentFloors
  apply List.all_eq_true.mpr
  intro receiverRoot receiverMember
  simp only [Bool.and_eq_true]
  constructor
  · apply (Func.rootsWithin_eq_true _ _ _).mpr
    intro root member
    rcases mappedBound root member with literal | expanded
    · exact .inl (receiverFloors receiverRoot receiverMember literal)
    · exact .inr (fun concrete concreteMember =>
        receiverFloors receiverRoot receiverMember (expanded concrete concreteMember))
  · apply (Func.rootsWithin_eq_true _ _ _).mpr
    intro root member
    rcases receiverBounds receiverRoot receiverMember root member with literal | expanded
    · exact .inl (mappedFloor literal)
    · exact .inr (fun concrete concreteMember => mappedFloor (expanded concrete concreteMember))

end Goose.Lower.Validation.AdmittedSourceCalls
