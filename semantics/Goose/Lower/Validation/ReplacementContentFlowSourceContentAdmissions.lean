import Goose.Lower.Validation.ReplacementContentFlowSourceAdmittedInputs
import Goose.GIR.ReplacementContentFlowProofsBounds

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

private theorem expanded_union_subset (func : Func) (left right : List RootRef) :
    (unionRoots left right).flatMap func.expandParameterRoot ⊆
      left.flatMap func.expandParameterRoot ++ right.flatMap func.expandParameterRoot := by
  intro root member
  obtain ⟨source, sourceMember, expanded⟩ := List.mem_flatMap.mp member
  rcases (unionRoots_mem_iff _ _ _).mp sourceMember with first | second
  · exact List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr ⟨source, first, expanded⟩))
  · exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨source, second, expanded⟩))

private theorem contentInputBound_fold_source (callee caller : Func)
    (argumentRoots : Nat → Option (List RootRef)) (sourceArgs : List (List RootRef))
    (declared : List RootRef)
    (arguments : ∀ index ∈ declared, ∀ parameter, index = .param parameter →
      ∀ source, sourceArgs[parameter]? = some source →
      ∃ bound, admittedArgumentBound callee argumentRoots parameter = some bound ∧
        bound.covers (some (source.flatMap caller.expandParameterRoot)) = true)
    (initial : ContentInputBound) (sourceInitial result : List RootRef)
    (covered : initial.covers (some (sourceInitial.flatMap caller.expandParameterRoot)) = true)
    (mapping : mapResultRoots sourceArgs sourceInitial declared = .ok result) :
    ∃ bound,
      declared.foldlM (init := initial) (fun upper root => do
        let next ← match root with
          | .global global => some (ContentInputBound.roots [.global global])
          | .param index => admittedArgumentBound callee argumentRoots index
          | .local _ => none
        pure (upper.join next)) = some bound ∧
      bound.covers (some (result.flatMap caller.expandParameterRoot)) = true := by
  induction declared generalizing initial sourceInitial with
  | nil =>
      have identity : sourceInitial = result := by simpa [mapResultRoots, pure, Except.pure] using mapping
      subst result
      exact ⟨initial, rfl, covered⟩
  | cons root rest ih =>
      cases root with
      | «local» slot => simp [mapResultRoots, mapCalleeRoots, reject, bind, Except.bind] at mapping
      | global global =>
          have nextCovered : (ContentInputBound.roots [.global global]).covers
              (some (([.global global] : List RootRef).flatMap caller.expandParameterRoot)) = true := by
            simp [Func.expandParameterRoot, ContentInputBound.covers]
          have joined := ContentInputBound.covers_subset
            (ContentInputBound.join_covers covered nextCovered)
            (expanded_union_subset caller sourceInitial [.global global])
          obtain ⟨bound, folded, final⟩ := ih
            (fun index member => arguments index (by simp [member]))
            (initial.join (.roots [.global global])) (unionRoots sourceInitial [.global global]) joined
            (by simpa [mapResultRoots, mapCalleeRoots, pure, Except.pure, bind, Except.bind] using mapping)
          exact ⟨bound, by simpa [List.foldlM, pure, bind, Option.bind] using folded, final⟩
      | param index =>
          cases row : sourceArgs[index]? with
          | none => simp [mapResultRoots, mapCalleeRoots, row, reject, bind, Except.bind] at mapping
          | some source =>
              obtain ⟨next, found, nextCovered⟩ := arguments (.param index) (by simp) index rfl source row
              have joined := ContentInputBound.covers_subset
                (ContentInputBound.join_covers covered nextCovered)
                (expanded_union_subset caller sourceInitial source)
              obtain ⟨bound, folded, final⟩ := ih
                (fun root member => arguments root (by simp [member]))
                (initial.join next) (unionRoots sourceInitial source) joined
                (by simpa [mapResultRoots, mapCalleeRoots, row, pure, Except.pure, bind, Except.bind] using mapping)
              exact ⟨bound, by simpa [List.foldlM, found, pure, bind, Option.bind] using folded, final⟩

theorem contentInputBound_from_source {callee caller : Func}
    {argumentRoots : Nat → Option (List RootRef)} {sourceArgs : List (List RootRef)}
    {declared result : List RootRef}
    (arguments : ∀ index, RootRef.param index ∈ declared →
      ∀ source, sourceArgs[index]? = some source →
      ∃ bound, admittedArgumentBound callee argumentRoots index = some bound ∧
        bound.covers (some (source.flatMap caller.expandParameterRoot)) = true)
    (mapping : mapResultRoots sourceArgs [] declared = .ok result) :
    ∃ bound, contentInputBound callee argumentRoots declared = some bound ∧
      bound.covers (some (result.flatMap caller.expandParameterRoot)) = true := by
  exact contentInputBound_fold_source callee caller argumentRoots sourceArgs declared
    (by intro root member index identity; subst root; exact arguments index member)
    (.roots []) [] result (by simp [ContentInputBound.covers]) mapping

#print axioms contentInputBound_from_source

theorem checkContent_input_admitted {env : Core.PEnv} {ctx : Core.Context}
    {callee caller : Func} {sourceArgs : List Core.Arg} {sourceRoots : List (List RootRef)}
    {argumentRoots : Nat → Option (List RootRef)} {index : Nat}
    {declared sourceContents actualContents : List RootRef}
    (checked : Core.checkContent env ctx sourceArgs sourceRoots index = .ok ())
    (contentRow : (ctx.contentRoots.find? (·.1 == index)).map (·.2) = some declared)
    (sourceArgument :
      (∃ mu slot, sourceArgs[index]? = some (.byRef mu (.var slot)) ∧
        env.ann slot = some sourceContents) ∨
      (∃ mu slot, sourceArgs[index]? = some (.byRef mu (.deref (.read (.var slot)))) ∧
        env.cont slot = some sourceContents))
    (arguments : ∀ parameter, RootRef.param parameter ∈ declared →
      ∀ source, sourceRoots[parameter]? = some source →
      ∃ bound, admittedArgumentBound callee argumentRoots parameter = some bound ∧
        bound.covers (some (source.flatMap caller.expandParameterRoot)) = true)
    (contentsWithin : actualContents ⊆ sourceContents.flatMap caller.expandParameterRoot) :
    ∃ bound, contentInputBound callee argumentRoots declared = some bound ∧
      bound.covers (some actualContents) = true := by
  obtain ⟨mapped, mapping, sourceCases⟩ :=
    Core.Sound.checkContent_ok env ctx sourceArgs sourceRoots index declared checked contentRow
  have sourceWithin : sourceContents ⊆ mapped := by
    rcases sourceArgument with ⟨mu, slot, argument, sourceRow⟩ | ⟨mu, slot, argument, sourceRow⟩
    · rcases sourceCases with ⟨otherMu, otherSlot, annotation, otherArgument, otherRow, within, _⟩ |
        ⟨otherMu, otherSlot, contents, otherArgument, _, _, _⟩
      · have identity := Option.some.inj (argument.symm.trans otherArgument)
        cases identity
        have same := Option.some.inj (sourceRow.symm.trans otherRow)
        subst annotation
        exact within
      · have impossible := Option.some.inj (argument.symm.trans otherArgument)
        cases impossible
    · rcases sourceCases with ⟨otherMu, otherSlot, annotation, otherArgument, _, _, _⟩ |
        ⟨otherMu, otherSlot, contents, otherArgument, otherRow, _, within⟩
      · have impossible := Option.some.inj (argument.symm.trans otherArgument)
        cases impossible
      · have identity := Option.some.inj (argument.symm.trans otherArgument)
        cases identity
        have same := Option.some.inj (sourceRow.symm.trans otherRow)
        subst contents
        exact within
  obtain ⟨bound, found, covered⟩ := contentInputBound_from_source arguments mapping
  refine ⟨bound, found, ContentInputBound.covers_subset covered ?_⟩
  intro root member
  obtain ⟨source, sourceMember, expanded⟩ := List.mem_flatMap.mp (contentsWithin member)
  exact List.mem_flatMap.mpr ⟨source, sourceWithin sourceMember, expanded⟩

#print axioms checkContent_input_admitted

end Goose.Lower.Validation.ReplacementContentFlowSource
