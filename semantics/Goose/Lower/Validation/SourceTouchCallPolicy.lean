import Goose.Lower.Validation.SourceTouchSummaryBounds
import Goose.Lower.Validation.SourceCanonicalFactsAssembly
import Goose.Lower.Validation.SummaryPreservationCallEffects
import Goose.GIR.ReplacementContentFlowProofsSliceTouches

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR Goose.GIR.ReplacementContentFlow.Model

private def targetRoot : Target → RootRef
  | .param index => .param index
  | .global index => .global index

private theorem mapSummaryTargets_append (args : List (List RootRef)) (left right : List Target) :
    mapSummaryTargets args (left ++ right) =
      mapSummaryTargets args left ++ mapSummaryTargets args right := by
  induction left with
  | nil => rfl
  | cons first rest ih => cases first <;> simp [mapSummaryTargets, ih, List.append_assoc]

private theorem callMappedTouchTargets_append {caller callee : Func} {provenance : Prov}
    {args : List ValueId} {left right : List Target} {target : Target} :
    target ∈ callMappedTouchTargets caller callee provenance args (left ++ right) ↔
      target ∈ callMappedTouchTargets caller callee provenance args left ∨
      target ∈ callMappedTouchTargets caller callee provenance args right := by
  simp [callMappedTouchTargets, mapSummaryTargets_append, mem_addTargets_iff,
    List.flatMap_append, or_assoc, or_left_comm]

private theorem parameter_global_row {func : Func} {index global : Nat}
    (member : RootRef.global global ∈ func.parameterRoots index) :
    ∃ row, func.roots.params.find? (·.1 == index) = some row ∧ .global global ∈ row.2 := by
  unfold Func.parameterRoots at member
  cases found : func.roots.params.find? (·.1 == index) with
  | none => simp [found] at member
  | some row => exact ⟨row, rfl, by simpa [found] using member⟩

private theorem parameter_annotation_reference {module : GIR.Module} {func : Func} {index : Nat}
    {row : Nat × List RootRef} (annotations : annotationsValid module func = true)
    (found : func.roots.params.find? (·.1 == index) = some row) :
    (func.params[index]?).any Ty.isRefLike = true := by
  have member := Array.mem_of_find?_eq_some found
  have key : row.1 = index := eq_of_beq (Array.find?_some (p := fun row : Nat × List RootRef => row.1 == index) (a := row) found)
  simp only [annotationsValid, Bool.and_eq_true] at annotations
  have checked := (List.all_eq_true.mp annotations.1.1.2) row
    (Array.mem_toList_iff.mpr member)
  simp only [Bool.and_eq_true] at checked
  exact key ▸ checked.1

private theorem mapSummaryTargets_member {args : List (List RootRef)} {targets : List Target}
    {source target : Target} (sourceMember : source ∈ targets)
    (present : target ∈ mapSummaryTargets args [source]) :
    target ∈ mapSummaryTargets args targets := by
  induction targets with
  | nil => simp at sourceMember
  | cons first rest ih =>
    rcases List.mem_cons.mp sourceMember with same | restMember
    · subst first
      cases source <;> simp_all [mapSummaryTargets]
    · cases first <;> simp [mapSummaryTargets, ih restMember]

private theorem mapped_storage_summary_bound {module : GIR.Module} {caller callee : Func}
    {provenance : Prov} {args : List ValueId} {targets : List Target}
    (closed : ParameterRootsClosed callee) (annotations : annotationsValid module callee = true) :
    ∀ target ∈ caller.storageTargets (rootsTargets
      (mapRawContentRoots provenance args ((callee.storageTargets targets).map targetRoot))),
      target ∈ callMappedTouchTargets caller callee provenance args targets := by
  intro target member
  rw [storageTargets_rootsTargets] at member
  obtain ⟨root, rootMember, rootTargetAt⟩ := List.mem_filterMap.mp member
  obtain ⟨mapped, mappedMember, expanded⟩ := List.mem_flatMap.mp rootMember
  obtain ⟨original, originalMember, mappedRoot⟩ :=
    (mapRawContentRoots_member provenance args _ mapped).mp mappedMember
  obtain ⟨originalTarget, originalTargetMember, originalEq⟩ := List.mem_map.mp originalMember
  subst original
  obtain ⟨declared, declaredMember, stored⟩ := List.mem_flatMap.mp originalTargetMember
  have actual (found : target ∈ mapSummaryTargets (args.map fun value =>
      ((rootsAt provenance.vals value).flatMap caller.expandParameterRoot).foldl
        (fun acc root => unionRoots acc [root]) []) targets) :
      target ∈ callMappedTouchTargets caller callee provenance args targets :=
    mem_addTargets_iff.mpr (Or.inl found)
  have annotated (found : target ∈ targets.flatMap fun
      | .param index => match callee.params[index]? with
        | some type => if type.isRefLike then
            ((callee.roots.params.find? (·.1 == index)).map (·.2)).getD [] |>.filterMap fun
              | .global global => some (Target.global global)
              | _ => none
          else []
        | none => []
      | .global _ => []) :
      target ∈ callMappedTouchTargets caller callee provenance args targets :=
    mem_addTargets_iff.mpr (Or.inr found)
  have singletonActual (source : Target) (sourceMember : source ∈ targets)
      (present : target ∈ mapSummaryTargets (args.map fun value =>
        ((rootsAt provenance.vals value).flatMap caller.expandParameterRoot).foldl
          (fun acc root => unionRoots acc [root]) []) [source]) :
      target ∈ callMappedTouchTargets caller callee provenance args targets := by
    apply actual
    exact mapSummaryTargets_member sourceMember present
  cases declared with
  | global global =>
    have same : originalTarget = .global global := List.mem_singleton.mp stored
    subst originalTarget
    have same : mapped = .global global := by simpa [mapRawContentRoots, targetRoot] using mappedRoot
    subst mapped
    have same : root = .global global := by simpa [Func.expandParameterRoot] using expanded
    subst root
    have same : target = .global global := by simpa [rootTarget] using rootTargetAt.symm
    subst target
    exact singletonActual (.global global) declaredMember (by simp [mapSummaryTargets])
  | param index =>
    cases originalTarget with
    | global global =>
      have rootMember : RootRef.global global ∈ callee.parameterRoots index := by
        obtain ⟨source, sourceMember, equal⟩ := List.mem_filterMap.mp stored
        cases source <;> simp_all [rootTarget]
      obtain ⟨row, found, rowMember⟩ := parameter_global_row rootMember
      have reference := parameter_annotation_reference annotations found
      have same : mapped = .global global := by simpa [mapRawContentRoots, targetRoot] using mappedRoot
      subst mapped
      have same : root = .global global := by simpa [Func.expandParameterRoot] using expanded
      subst root
      have same : target = .global global := by simpa [rootTarget] using rootTargetAt.symm
      subst target
      apply annotated
      apply List.mem_flatMap.mpr
      refine ⟨.param index, declaredMember, ?_⟩
      cases typeAt : callee.params[index]? with
      | none => simp [typeAt] at reference
      | some type =>
        have refLike : type.isRefLike = true := by simpa [typeAt] using reference
        simp only [typeAt, refLike, ↓reduceIte, found, Option.map_some, Option.getD_some]
        exact List.mem_filterMap.mpr ⟨.global global, rowMember, rfl⟩
    | param sourceIndex =>
      have rootMember : RootRef.param sourceIndex ∈ callee.parameterRoots index :=
        rootsTargets_param_iff.mp stored
      have same : sourceIndex = index := by
        rcases closed index (.param sourceIndex) rootMember with same | ⟨global, impossible⟩
        · exact RootRef.param.inj same
        · cases impossible
      subst sourceIndex
      apply singletonActual (.param index) declaredMember
      cases argumentAt : args[index]? with
      | none => simp [mapRawContentRoots, targetRoot, argumentAt] at mappedRoot
      | some value =>
        have provenanceMember : mapped ∈ rootsAt provenance.vals value := by
          simpa [mapRawContentRoots, targetRoot, argumentAt] using mappedRoot
        simp only [mapSummaryTargets, List.append_nil, List.getElem?_map, argumentAt,
          Option.map_some, Option.getD_some]
        apply List.mem_filterMap.mpr
        refine ⟨root, ?_, rootTargetAt⟩
        apply mem_union_singletons_fold.mpr
        exact Or.inr (List.mem_flatMap.mpr ⟨mapped, provenanceMember, expanded⟩)

private theorem storage_target_fixed {func : Func} {targets : List Target} {target : Target}
    (closed : ParameterRootsClosed func) (member : target ∈ func.storageTargets targets) :
    target ∈ func.storageTargets [target] := by
  cases target with
  | global global => simp [Func.storageTargets]
  | param index =>
    obtain ⟨original, originalMember, expanded⟩ := List.mem_flatMap.mp member
    cases original with
    | global global => simp at expanded
    | param originalIndex =>
      have included := rootsTargets_param_iff.mp expanded
      have same : index = originalIndex := by
        rcases closed originalIndex (.param index) included with same | ⟨global, impossible⟩
        · exact RootRef.param.inj same
        · cases impossible
      subst originalIndex
      simpa [Func.storageTargets] using expanded

theorem accepted_call_mapped_summary_storage_bound {module : Core.Module} {index : Nat}
    {caller callee : Func} {summary calleeSummary : Summary} {block : GIR.Block}
    {function : FnId} {args : List ValueId} {result : ValueId} {origin : Option OriginId}
    (accepted : Core.validate module = .ok ())
    (functionRow : (lower module).funcs[index]? = some caller)
    (known : caller.summary = .known summary)
    (blockMember : block ∈ caller.blocks.toList)
    (instMember : Inst.def result (.call function args origin) ∈ block.insts)
    (calleeRow : (lower module).funcs[function]? = some callee)
    (calleeKnown : callee.summary = .known calleeSummary)
    (callerClosed : ParameterRootsClosed caller) (calleeClosed : ParameterRootsClosed callee) :
    ∀ target ∈ caller.storageTargets (rootsTargets
      (mapRawContentRoots
        (caller.provenance (resultRoots (lower module) (lower module).implTypes)
          ((lower module).implTypes[index]?.getD #[]) (lower module).rootCount) args
        ((callee.storageTargets (summaryTouchTargets calleeSummary)).map targetRoot))),
      target ∈ caller.storageTargets (summaryTouchTargets summary) := by
  intro target member
  have annotations := ReplacementContentFlowSource.accepted_function_annotationsValid accepted calleeRow
  have mapped := mapped_storage_summary_bound calleeClosed annotations target member
  have fixed := storage_target_fixed callerClosed member
  apply accepted_call_touch_storage_bound accepted functionRow known blockMember instMember calleeRow calleeKnown
  obtain ⟨original, originalMember, expanded⟩ := List.mem_flatMap.mp fixed
  have same : original = target := List.mem_singleton.mp originalMember
  subst original
  apply List.mem_flatMap.mpr
  refine ⟨target, ?_, ?_⟩
  · simpa only [summaryTouchTargets, callMappedTouchTargets_append, List.mem_append] using mapped
  · simpa using expanded

theorem summaryTouchPolicy_parameter_refines {module : GIR.Module} {callee : Func}
    {summary : Summary} {index : Nat} (known : callee.summary = .known summary)
    (closed : ParameterRootsClosed callee)
    (policy : summaryTouchPolicy module callee (.param index)) :
    RootsRefine callee [.param index]
      ((callee.storageTargets (summaryTouchTargets summary)).map targetRoot) := by
  simp only [summaryTouchPolicy, summaryTouchRoots, known] at policy
  obtain ⟨actual, actualAt, within⟩ := policy
  have normalized : normalize callee (.known [.param index]) =
      some (unionRoots [] (callee.parameterRoots index)) :=
    normalize_singleton_atom (by rfl)
  rw [ownerDependencies_param, normalized] at actualAt
  cases actualAt
  intro root member
  have same : root = .param index := List.mem_singleton.mp member
  subst root
  apply Or.inr
  intro concrete concreteMember
  have bounded := within concrete
    ((unionRoots_mem_iff _ _ _).mpr (Or.inr concreteMember))
  rcases bounded with ⟨slot, localRoot⟩ | bounded
  · rcases closed index concrete concreteMember with same | ⟨global, same⟩
    · rw [same] at localRoot
      cases localRoot
    · rw [same] at localRoot
      cases localRoot
  · exact bounded

theorem accepted_call_parameter_touch_policy {module : Core.Module} {index : Nat}
    {caller callee : Func} {summary calleeSummary : Summary} {block : GIR.Block}
    {function : FnId} {args : List ValueId} {result : ValueId} {origin : Option OriginId}
    {parameter : Nat} {roots : Roots}
    (accepted : Core.validate module = .ok ())
    (functionRow : (lower module).funcs[index]? = some caller)
    (known : caller.summary = .known summary)
    (blockMember : block ∈ caller.blocks.toList)
    (instMember : Inst.def result (.call function args origin) ∈ block.insts)
    (calleeRow : (lower module).funcs[function]? = some callee)
    (calleeKnown : callee.summary = .known calleeSummary)
    (callerClosed : ParameterRootsClosed caller) (calleeClosed : ParameterRootsClosed callee)
    (policy : summaryTouchPolicy (lower module) callee (.param parameter))
    (contracts : ∀ parameter, RootsRefine caller
      (mapRawContentRoots
        (caller.provenance (resultRoots (lower module) (lower module).implTypes)
          ((lower module).implTypes[index]?.getD #[]) (lower module).rootCount) args [.param parameter])
      (mapRawContentRoots
        (caller.provenance (resultRoots (lower module) (lower module).implTypes)
          ((lower module).implTypes[index]?.getD #[]) (lower module).rootCount) args
        (callee.parameterRoots parameter)))
    (refined : SymbolicRootsRefine caller roots
      (mapRawContentRoots
        (caller.provenance (resultRoots (lower module) (lower module).implTypes)
          ((lower module).implTypes[index]?.getD #[]) (lower module).rootCount) args [.param parameter])) :
    roots.AtomsWithin (summaryTouchPolicy (lower module) caller) := by
  have parameterBound := summaryTouchPolicy_parameter_refines calleeKnown calleeClosed policy
  have mapped := RootsRefine.mapRaw contracts parameterBound
  apply symbolicRoots_summaryTouchPolicy callerClosed (refined.refine callerClosed mapped)
  intro otherSummary otherKnown target member
  have same : otherSummary = summary := SummaryAnn.known.inj (otherKnown.symm.trans known)
  subst otherSummary
  exact accepted_call_mapped_summary_storage_bound accepted functionRow known blockMember instMember
    calleeRow calleeKnown callerClosed calleeClosed target member

theorem accepted_call_global_touch_policy {module : Core.Module} {index : Nat}
    {caller callee : Func} {summary calleeSummary : Summary} {block : GIR.Block}
    {function : FnId} {args : List ValueId} {result : ValueId} {origin : Option OriginId}
    {global : GlobalId} (accepted : Core.validate module = .ok ())
    (functionRow : (lower module).funcs[index]? = some caller)
    (known : caller.summary = .known summary)
    (blockMember : block ∈ caller.blocks.toList)
    (instMember : Inst.def result (.call function args origin) ∈ block.insts)
    (calleeRow : (lower module).funcs[function]? = some callee)
    (calleeKnown : callee.summary = .known calleeSummary)
    (callerClosed : ParameterRootsClosed caller) (calleeClosed : ParameterRootsClosed callee)
    (policy : summaryTouchPolicy (lower module) callee (.global global)) :
    summaryTouchPolicy (lower module) caller (.global global) := by
  simp only [summaryTouchPolicy, summaryTouchRoots, calleeKnown] at policy
  obtain ⟨actual, actualAt, within⟩ := policy
  rw [ownerDependencies_literal_global] at actualAt
  cases actualAt
  simp only [summaryTouchPolicy, summaryTouchRoots, known]
  refine ⟨ownerTouches (lower module) [.global global], ownerDependencies_literal_global _ _ _, ?_⟩
  intro root member
  have same : root = .global global := List.mem_singleton.mp (ownerTouches_subset _ _ member)
  subst root
  rcases within (.global global) member with ⟨slot, impossible⟩ | bounded
  · cases impossible
  · apply Or.inr
    let provenance := caller.provenance (resultRoots (lower module) (lower module).implTypes)
      ((lower module).implTypes[index]?.getD #[]) (lower module).rootCount
    have mapped : RootRef.global global ∈ mapRawContentRoots provenance args
        ((callee.storageTargets (summaryTouchTargets calleeSummary)).map targetRoot) := by
      apply (mapRawContentRoots_member _ _ _ _).mpr
      exact ⟨.global global, bounded, by simp [mapRawContentRoots]⟩
    have mappedStorage : Target.global global ∈ caller.storageTargets (rootsTargets
        (mapRawContentRoots provenance args
          ((callee.storageTargets (summaryTouchTargets calleeSummary)).map targetRoot))) := by
      rw [storageTargets_rootsTargets]
      apply List.mem_filterMap.mpr
      refine ⟨.global global, ?_, rfl⟩
      exact List.mem_flatMap.mpr ⟨.global global, mapped, by simp [Func.expandParameterRoot]⟩
    have declared := accepted_call_mapped_summary_storage_bound accepted functionRow known
      blockMember instMember calleeRow calleeKnown callerClosed calleeClosed _ mappedStorage
    exact List.mem_map.mpr ⟨.global global, declared, rfl⟩

#print axioms mapped_storage_summary_bound
#print axioms accepted_call_mapped_summary_storage_bound
#print axioms summaryTouchPolicy_parameter_refines
#print axioms accepted_call_parameter_touch_policy
#print axioms accepted_call_global_touch_policy

end Goose.Lower.Validation.SummaryPreservation
