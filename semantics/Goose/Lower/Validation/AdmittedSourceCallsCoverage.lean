import Goose.Lower.Validation.AdmittedSourceCallsTransport
import Goose.GIR.RootBoundsRefinement

namespace Goose.Lower.Validation.AdmittedSourceCalls

open Goose.Core Goose.GIR

private theorem union_mem {left right : List RootRef} {root : RootRef} :
    root ∈ unionRoots left right ↔ root ∈ left ∨ root ∈ right :=
  ⟨Sound.unionRoots_mem left right root,
    fun member => member.elim (Sound.unionRoots_left left right root)
      (Sound.unionRoots_right left right root)⟩

private theorem flattened_mem (roots accumulated : List RootRef) (root : RootRef) :
    root ∈ roots.foldl (fun prior next => unionRoots prior [next]) accumulated ↔
      root ∈ accumulated ∨ root ∈ roots := by
  induction roots generalizing accumulated with
  | nil => simp
  | cons first rest inductionHypothesis =>
    simp only [List.foldl_cons, inductionHypothesis, union_mem,
      List.mem_cons, or_assoc, List.not_mem_nil, false_or]

theorem mapArgumentRoots_mem {func : Func} {provenance : Prov} {value : ValueId}
    {parameter : Nat} {root : RootRef} :
    root ∈ mapArgumentRoots func provenance value parameter ↔
      ∃ raw ∈ rootsAt provenance.vals value, root ∈ (match raw with
        | .local _ => [RootRef.param parameter]
        | .global _ => [raw]
        | .param index => (func.parameterRoots index).map fun (concrete : RootRef) =>
          match concrete with
          | .global global => RootRef.global global
          | _ => RootRef.param parameter) := by
  simp only [mapArgumentRoots, flattened_mem, List.not_mem_nil, false_or, List.mem_flatMap]
  constructor <;> rintro ⟨raw, member, mapped⟩ <;> refine ⟨raw, member, ?_⟩
  all_goals
    cases raw with
    | «local» slot => simpa using mapped
    | global global => simpa using mapped
    | param index =>
      obtain ⟨concrete, concreteMember, same⟩ := List.mem_map.mp mapped
      exact List.mem_map.mpr ⟨concrete, concreteMember, by cases concrete <;> simpa using same⟩

theorem raw_parameter_contract_of_argument_domain
    {func callee : Func} {provenance : Prov} {arguments : List ValueId}
    {index : Nat} {value : ValueId} (argument : arguments[index]? = some value)
    (domain : RootRef.param index ∈ callee.parameterRoots index ∨
      mapArgumentRoots func provenance value index ⊆ callee.parameterRoots index) :
    RootsRefine func (mapRawContentRoots provenance arguments [.param index])
      (mapRawContentRoots provenance arguments (callee.parameterRoots index)) := by
  have actualMember : ∀ root, root ∈ mapRawContentRoots provenance arguments [.param index] →
      root ∈ rootsAt provenance.vals value := by
    intro root member
    simpa [mapRawContentRoots, argument] using member
  have includedGlobal : ∀ global, RootRef.global global ∈ callee.parameterRoots index →
      RootRef.global global ∈ mapRawContentRoots provenance arguments (callee.parameterRoots index) := by
    intro global member
    exact List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨.global global, member, by simp⟩)
  by_cases generic : RootRef.param index ∈ callee.parameterRoots index
  · intro root member
    exact .inl (List.mem_eraseDups.mpr (List.mem_flatMap.mpr
      ⟨.param index, generic, by simpa [argument] using actualMember root member⟩))
  · have constrained := domain.resolve_left generic
    intro root member
    have actual := actualMember root member
    cases root with
    | «local» slot =>
      have forbidden : RootRef.param index ∈ callee.parameterRoots index :=
        constrained (mapArgumentRoots_mem.mpr ⟨.local slot, actual, by simp⟩)
      exact False.elim (generic forbidden)
    | global global =>
      exact .inl (includedGlobal global
        (constrained (mapArgumentRoots_mem.mpr ⟨.global global, actual, by simp⟩)))
    | param parameter =>
      refine .inr ?_
      intro concrete concreteMember
      cases concrete with
      | global global =>
        exact includedGlobal global (constrained (mapArgumentRoots_mem.mpr
          ⟨.param parameter, actual, List.mem_map.mpr ⟨.global global, concreteMember, rfl⟩⟩))
      | «local» slot =>
        exact False.elim (generic (constrained (mapArgumentRoots_mem.mpr
          ⟨.param parameter, actual, List.mem_map.mpr ⟨.local slot, concreteMember, rfl⟩⟩)))
      | param other =>
        exact False.elim (generic (constrained (mapArgumentRoots_mem.mpr
          ⟨.param parameter, actual, List.mem_map.mpr ⟨.param other, concreteMember, rfl⟩⟩)))

theorem raw_parameter_contracts_of_argument_domains
    {func callee : Func} {provenance : Prov} {arguments : List ValueId}
    (domains : ∀ (index : Nat) (value : ValueId), arguments[index]? = some value →
      RootRef.param index ∈ callee.parameterRoots index ∨
        mapArgumentRoots func provenance value index ⊆ callee.parameterRoots index) :
    ∀ index, RootsRefine func (mapRawContentRoots provenance arguments [.param index])
      (mapRawContentRoots provenance arguments (callee.parameterRoots index)) := by
  intro index
  cases argument : arguments[index]? with
  | none =>
    intro root member
    simp [mapRawContentRoots, argument] at member
  | some value => exact raw_parameter_contract_of_argument_domain argument (domains index value argument)

theorem mapArgumentRoots_subset_of_value_subset
    {func : Func} {provenance upper : Prov} {value : ValueId} {parameter : Nat}
    (below : rootsAt provenance.vals value ⊆ rootsAt upper.vals value) :
    mapArgumentRoots func provenance value parameter ⊆ mapArgumentRoots func upper value parameter := by
  intro root member
  obtain ⟨raw, rawMember, mapped⟩ := mapArgumentRoots_mem.mp member
  exact mapArgumentRoots_mem.mpr ⟨raw, below rawMember, mapped⟩

theorem raw_parameter_contracts_below_argument_domains
    {func callee : Func} {provenance upper : Prov} {arguments : List ValueId}
    (domains : ∀ (index : Nat) (value : ValueId), arguments[index]? = some value →
      RootRef.param index ∈ callee.parameterRoots index ∨
        mapArgumentRoots func upper value index ⊆ callee.parameterRoots index)
    (below : ∀ (index : Nat) (value : ValueId), arguments[index]? = some value →
      rootsAt provenance.vals value ⊆ rootsAt upper.vals value) :
    ∀ index, RootsRefine func (mapRawContentRoots provenance arguments [.param index])
      (mapRawContentRoots provenance arguments (callee.parameterRoots index)) := by
  apply raw_parameter_contracts_of_argument_domains
  intro index value argument
  rcases domains index value argument with generic | constrained
  · exact .inl generic
  · exact .inr ((mapArgumentRoots_subset_of_value_subset (below index value argument)).trans constrained)

theorem argumentContents_mem {func : Func} {provenance : Prov} {value : ValueId}
    {root : RootRef} :
    root ∈ argumentContents func provenance value ↔
      ∃ receiver ∈ rootsAt provenance.vals value,
        ∃ content ∈ func.receiverContentCeiling provenance receiver,
          root ∈ func.expandParameterRoot content := by
  simp only [argumentContents, flattened_mem, List.not_mem_nil, false_or, List.mem_flatMap]
  apply exists_congr
  intro receiver
  apply and_congr_right
  intro member
  cases receiver with
  | «local» slot => rfl
  | global global => rfl
  | param parameter =>
    cases found : func.params[parameter]? with
    | none => simp [Func.receiverContentCeiling, found]
    | some type => simp [Func.receiverContentCeiling, found]

theorem mapContentRoots_mem {func : Func} {provenance : Prov} {arguments : List ValueId}
    {declared : List RootRef} {root : RootRef} :
    root ∈ mapContentRoots func provenance arguments declared ↔
      root ∈ (mapRawContentRoots provenance arguments declared).flatMap func.expandParameterRoot := by
  simp only [mapContentRoots, flattened_mem, List.not_mem_nil, false_or, List.mem_flatMap,
    mapRawContentRoots, List.mem_eraseDups]
  constructor
  · rintro ⟨declaredRoot, declaredMember, member⟩
    cases declaredRoot with
    | «local» slot => simp at member
    | global global =>
      have same : root = RootRef.global global := List.mem_singleton.mp member
      subst root
      exact ⟨.global global, ⟨.global global, declaredMember, by simp⟩,
        by simp [Func.expandParameterRoot]⟩
    | param parameter =>
      cases found : arguments[parameter]? with
      | none => simp [found] at member
      | some value =>
        simp only [found, List.mem_flatMap] at member
        obtain ⟨actual, actualMember, expandedMember⟩ := member
        exact ⟨actual, ⟨.param parameter, declaredMember, by simpa [found] using actualMember⟩,
          expandedMember⟩
  · rintro ⟨actual, ⟨declaredRoot, declaredMember, member⟩, expandedMember⟩
    refine ⟨declaredRoot, declaredMember, ?_⟩
    cases declaredRoot with
    | «local» slot => simp at member
    | global global =>
      have same : actual = RootRef.global global := List.mem_singleton.mp member
      subst actual
      simpa only [Func.expandParameterRoot, List.mem_singleton] using expandedMember
    | param parameter =>
      cases found : arguments[parameter]? with
      | none => simp [found] at member
      | some value =>
        simp only [found]
        apply List.mem_flatMap.mpr
        exact ⟨actual, by simpa [found] using member, expandedMember⟩

theorem call_content_coverage_of_receivers
    {func : Func} {provenance : Prov} {arguments : List ValueId}
    {declared : List RootRef} {value : ValueId}
    (closed : ∀ index root, root ∈ func.parameterRoots index →
      root = .param index ∨ ∃ global, root = .global global)
    (nonempty : ∃ root, root ∈ rootsAt provenance.vals value)
    (receivers : func.admittedCallReceiver provenance value
      (mapRawContentRoots provenance arguments declared) = true) :
    argumentContents func provenance value ⊆ mapContentRoots func provenance arguments declared ∧
      mapContentRoots func provenance arguments declared ⊆ argumentContents func provenance value := by
  have bounds := List.all_eq_true.mp receivers
  constructor
  · intro root member
    obtain ⟨receiver, receiverMember, content, contentMember, expandedMember⟩ :=
      argumentContents_mem.mp member
    have reverse : func.rootsWithin (func.receiverContentCeiling provenance receiver)
        (mapRawContentRoots provenance arguments declared) = true := by
      have checked := bounds receiver receiverMember
      simp only [Bool.and_eq_true] at checked
      exact checked.2
    apply mapContentRoots_mem.mpr
    exact ((Func.rootsWithin_eq_true _ _ _).mp reverse).expanded closed
      content contentMember root expandedMember
  · intro root member
    obtain ⟨receiver, receiverMember⟩ := nonempty
    obtain ⟨content, contentMember, expandedMember⟩ := List.mem_flatMap.mp
      (mapContentRoots_mem.mp member)
    have forward : func.rootsWithin (mapRawContentRoots provenance arguments declared)
        (func.receiverContentCeiling provenance receiver) = true := by
      have checked := bounds receiver receiverMember
      simp only [Bool.and_eq_true] at checked
      exact checked.1
    obtain ⟨origin, originMember, concreteMember⟩ := List.mem_flatMap.mp
      (((Func.rootsWithin_eq_true _ _ _).mp forward).expanded closed
        content contentMember root expandedMember)
    exact argumentContents_mem.mpr ⟨receiver, receiverMember, origin, originMember, concreteMember⟩

theorem admittedCallReceiver_of_source_refinements
    {func : Func} {provenance : Prov} {arguments : List ValueId}
    {argumentRoots : List (List RootRef)} {declared mapped : List RootRef} {receiver : ValueId}
    (closed : ∀ index root, root ∈ func.parameterRoots index →
      root = .param index ∨ ∃ global, root = .global global)
    (checked : mapResultRoots argumentRoots [] declared = .ok mapped)
    (argumentBounds : ∀ (index : Nat) (value : ValueId) (source : List RootRef),
      RootRef.param index ∈ declared →
      arguments[index]? = some value → argumentRoots[index]? = some source →
      RootsRefine func (rootsAt provenance.vals value) source)
    (argumentFloors : ∀ (index : Nat) (source : List RootRef),
      RootRef.param index ∈ declared → argumentRoots[index]? = some source →
      ∃ value, arguments[index]? = some value ∧
        RootsRefine func source (rootsAt provenance.vals value))
    (receiverBounds : ∀ root ∈ rootsAt provenance.vals receiver,
      RootsRefine func (func.receiverContentCeiling provenance root) mapped)
    (receiverFloors : ∀ root ∈ rootsAt provenance.vals receiver,
      RootsRefine func mapped (func.receiverContentCeiling provenance root)) :
    func.admittedCallReceiver provenance receiver
      (mapRawContentRoots provenance arguments declared) = true := by
  have mappedBound := mapRawContentRoots_refines checked argumentBounds
  have mappedFloor := mapRawContentRoots_refines_reverse checked argumentFloors
  apply List.all_eq_true.mpr
  intro receiverRoot receiverMember
  simp only [Bool.and_eq_true]
  exact ⟨(Func.rootsWithin_eq_true _ _ _).mpr
      (mappedBound.trans closed (receiverFloors receiverRoot receiverMember)),
    (Func.rootsWithin_eq_true _ _ _).mpr
      ((receiverBounds receiverRoot receiverMember).trans closed mappedFloor)⟩

theorem admittedInstruction_call_of_source_refinements
    {module : GIR.Module} {func callee : Func} {types : Array (Option VTy)}
    {provenance : Prov} {function : FnId} {arguments : List ValueId}
    {value : ValueId} {origin : Option OriginId}
    (calleeFound : module.funcs[function]? = some callee)
    (closed : ∀ index root, root ∈ func.parameterRoots index →
      root = .param index ∨ ∃ global, root = .global global)
    (rows : ∀ parameter declared, (parameter, declared) ∈ callee.roots.contents.toList →
      (callee.params[parameter]?).any Ty.isRefSlice = true →
      ∃ argumentRoots mapped,
        mapResultRoots argumentRoots [] declared = .ok mapped ∧
        (∀ (index : Nat) (argument : ValueId) (source : List RootRef),
          RootRef.param index ∈ declared → arguments[index]? = some argument →
          argumentRoots[index]? = some source →
          RootsRefine func (rootsAt provenance.vals argument) source) ∧
        (∀ (index : Nat) (source : List RootRef),
          RootRef.param index ∈ declared → argumentRoots[index]? = some source →
          ∃ argument, arguments[index]? = some argument ∧
            RootsRefine func source (rootsAt provenance.vals argument)) ∧
        (∃ receiver, receiver ∈ rootsAt provenance.vals arguments[parameter]!) ∧
        (∀ receiver ∈ rootsAt provenance.vals arguments[parameter]!,
          RootsRefine func (func.receiverContentCeiling provenance receiver) mapped) ∧
        (∀ receiver ∈ rootsAt provenance.vals arguments[parameter]!,
          RootsRefine func mapped (func.receiverContentCeiling provenance receiver))) :
    func.admittedInstruction module types provenance
      (.def value (.call function arguments origin)) = true := by
  simp only [Func.admittedInstruction, calleeFound, List.all_eq_true]
  rintro ⟨parameter, declared⟩ member
  by_cases reference : (callee.params[parameter]?).any Ty.isRefSlice = true
  · obtain ⟨sourceArguments, mapped, mappedChecked, argumentBounds, argumentFloors,
      nonempty, receiverBounds, receiverFloors⟩ := rows parameter declared member reference
    have raw := admittedCallReceiver_of_source_refinements closed mappedChecked argumentBounds
      argumentFloors receiverBounds receiverFloors
    have coverage := call_content_coverage_of_receivers closed nonempty raw
    simp only [reference, Bool.not_true, Bool.false_or, raw, Bool.and_true,
      Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem]
    exact coverage
  · simp [reference]

theorem admittedInstruction_call_of_source_bounds
    {module : GIR.Module} {func callee : Func} {types : Array (Option VTy)}
    {provenance : Prov} {function : FnId} {arguments : List ValueId}
    {value : ValueId} {origin : Option OriginId}
    (calleeFound : module.funcs[function]? = some callee)
    (closed : ∀ index root, root ∈ func.parameterRoots index →
      root = .param index ∨ ∃ global, root = .global global)
    (rows : ∀ parameter declared, (parameter, declared) ∈ callee.roots.contents.toList →
      (callee.params[parameter]?).any Ty.isRefSlice = true →
      ∃ argumentRoots mapped,
        mapResultRoots argumentRoots [] declared = .ok mapped ∧
        (∀ (index : Nat) (argument : ValueId) (source : List RootRef),
          RootRef.param index ∈ declared → arguments[index]? = some argument →
          argumentRoots[index]? = some source →
          RootsRefine func (rootsAt provenance.vals argument) source) ∧
        (∀ (index : Nat) (source : List RootRef),
          RootRef.param index ∈ declared → argumentRoots[index]? = some source →
          ∃ argument, arguments[index]? = some argument ∧
            source ⊆ rootsAt provenance.vals argument) ∧
        (∃ receiver, receiver ∈ rootsAt provenance.vals arguments[parameter]!) ∧
        (∀ receiver ∈ rootsAt provenance.vals arguments[parameter]!,
          RootsRefine func (func.receiverContentCeiling provenance receiver) mapped) ∧
        (∀ receiver ∈ rootsAt provenance.vals arguments[parameter]!,
          mapped ⊆ func.receiverContentCeiling provenance receiver)) :
    func.admittedInstruction module types provenance
      (.def value (.call function arguments origin)) = true := by
  simp only [Func.admittedInstruction, calleeFound, List.all_eq_true]
  rintro ⟨parameter, declared⟩ member
  by_cases reference : (callee.params[parameter]?).any Ty.isRefSlice = true
  · obtain ⟨sourceArguments, mapped, mappedChecked, argumentBounds, argumentFloors,
      nonempty, receiverBounds, receiverFloors⟩ := rows parameter declared member reference
    have raw := admittedCallReceiver_of_source_bounds mappedChecked argumentBounds argumentFloors
      receiverBounds receiverFloors
    have coverage := call_content_coverage_of_receivers closed nonempty raw
    simp only [reference, Bool.not_true, Bool.false_or, raw, Bool.and_true,
      Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem]
    exact coverage
  · simp [reference]

end Goose.Lower.Validation.AdmittedSourceCalls
