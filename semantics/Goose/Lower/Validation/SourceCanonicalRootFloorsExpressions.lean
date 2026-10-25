import Goose.Lower.Validation.SourceCanonicalRootFloorsContracts

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core Goose.Core.Sound Goose.GIR ReplacementContentFlowSource

theorem read_floor (place : Place) : ExpressionFloor (.read place) := by
  intro env typing func root tables sourceTables valid path location info start finish source
    rootsBefore rootsAfter sourceRoots replayed returnTypes before after value run generated live continuation projects
  exact read_canonical_floor tables sourceTables source replayed run generated live continuation projects

theorem reference_floor (mode : Mutability) (place : Place) (child : PlaceFloor place) :
    ExpressionFloor (.ref mode place) := by
  intro env typing func root tables sourceTables valid path location info start finish source
    rootsBefore rootsAfter sourceRoots replayed returnTypes before after value run generated live continuation projects
  obtain ⟨placeInfo, placeFinish, placeSource, _, _⟩ := tyExpr_ref_place source
  simp only [lowerExpr] at run
  obtain ⟨address, middle, placeRun, borrowed⟩ := bind_eq.mp run
  have middleLive := (dead_borrowTo mode address).live_before borrowed live
  have suffix := advB_borrowTo mode address _ _ _ _ borrowed
  have placeFloor := child tables sourceTables valid (location.snoc 0 rfl) placeSource replayed
    placeRun generated middleLive (continuation.of_advance suffix) (projects.of_advance suffix)
  exact fun _ member => tables.borrowTo_floor (generated.lowerPlace place placeRun)
    borrowed live continuation (placeFloor member)

theorem slice_floor (mode : Mutability) (view : View) (low high : Bound) (origin : OriginId)
    (child : ViewFloor view) : ExpressionFloor (.slice mode view low high origin) := by
  intro env typing func root tables sourceTables valid path location info start finish source
    rootsBefore rootsAfter sourceRoots replayed returnTypes before after value run generated live continuation projects
  obtain ⟨element, writable, viewStart, viewFinish, lowFinish, highFinish, viewSource, _, _, _⟩ :=
    tyExpr_slice_children source
  simp only [rpExpr] at replayed
  obtain ⟨viewRoots, _, viewReplay, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
  obtain ⟨_, _, _, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
  obtain ⟨_, _, _, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
  obtain ⟨_, _, _, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
  have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp replayed)
  dsimp only at shape
  rw [shape]
  simp only [lowerExpr] at run
  obtain ⟨sample, sampled, viewRun, run⟩ := bind_eq.mp run
  obtain ⟨lowValue, lowAfter, lowRun, run⟩ := bind_eq.mp run
  obtain ⟨highValue, middle, highRun, emitted⟩ := bind_eq.mp run
  have middleLive := (dead_emitDef _).live_before emitted live
  have lowLive := (dead_lowerBound high).live_before highRun middleLive
  have sampledLive := (dead_lowerBound low).live_before lowRun lowLive
  have suffix := (advB_lowerBound low _ _ _ _ lowRun).trans
    ((advB_lowerBound high _ _ _ _ highRun).trans (advB_emitDef _ _ _ _ _ emitted))
  have viewFloor := child tables sourceTables valid (location.snoc 0 rfl) viewSource viewReplay
    viewRun generated sampledLive (continuation.of_advance suffix) (projects.of_advance suffix)
  exact fun _ member => tables.emitted_forward_floor
    (((generated.lowerView view viewRun).lowerBound low lowRun).lowerBound high highRun)
      emitted live continuation (.viewSlice mode sample lowValue highValue (some origin)) (viewFloor member)

theorem push_floor (place : Place) (expression : Expr) (origin : Option OriginId)
    (child : PlaceFloor place) : ExpressionFloor (.push place expression origin) := by
  intro env typing func root tables sourceTables valid path location info start finish source
    rootsBefore rootsAfter sourceRoots replayed returnTypes before after value run generated live continuation projects
  obtain ⟨placeInfo, element, placeStart, placeFinish, childStart, childFinish, placeSource, _, _, _⟩ :=
    tyExpr_push_children source
  have rootProjection : ∃ middle, rpPlace env place rootsBefore = .ok (sourceRoots, middle) := by
    simp only [rpExpr] at replayed
    obtain ⟨placeRoots, middle, placeReplay, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
    repeat' first
    | (obtain ⟨_, _, _, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed)
    | (split at replayed)
    all_goals
      have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp replayed)
      dsimp only at shape
      exact ⟨middle, by simpa only [shape] using placeReplay⟩
  obtain ⟨_, placeReplay⟩ := rootProjection
  simp only [lowerExpr] at run
  obtain ⟨address, addressed, placeRun, run⟩ := bind_eq.mp run
  obtain ⟨elementValue, middle, childRun, emitted⟩ := bind_eq.mp run
  have middleLive := (dead_emitDef _).live_before emitted live
  have addressedLive := (dead_lowerExpr expression).live_before childRun middleLive
  have suffix := (advB_lowerExpr expression _ _ _ _ childRun).trans (advB_emitDef _ _ _ _ _ emitted)
  have placeFloor := child tables sourceTables valid (location.snoc 0 rfl) placeSource placeReplay
    placeRun generated addressedLive (continuation.of_advance suffix) (projects.of_advance suffix)
  exact fun _ member => tables.emitted_forward_floor
    ((generated.lowerPlace place placeRun).lowerExpr expression childRun)
      emitted live continuation (.push address elementValue origin) (placeFloor member)

theorem conditional_floor (condition : Expr) (yes no : Core.Block) : ExpressionFloor (.ifE condition yes no) := by
  intro env typing func root tables sourceTables valid path location info start finish source
    rootsBefore rootsAfter sourceRoots replayed returnTypes before after value run generated live continuation projects
  by_cases reference : info.isRefLike = true
  · have recorded := lowerExpr_ifE_typed_recipe source run live generated reference
    obtain ⟨roots, row⟩ := projects.covered (value, .conditionalScope (sourceBlockScope yes)) recorded
    exact projects.ifE_actual_canonical_floor valid location replayed source run live generated reference
      (tables.valueRows value roots row) _ _ _
  · have nonref : info.isRefLike = false := by cases result : info.isRefLike <;> simp_all
    rw [source_expression_nonref_roots_empty _ sourceTables source nonref replayed]
    exact List.nil_subset _

theorem scalar_floor (expression : Expr)
    (scalar : match expression with
      | .lit .. | .bool _ | .len _ | .un .. | .bin .. | .cmp .. | .and .. | .or ..
      | .not _ | .conv .. | .pop .. | .arrLit .. | .structLit .. | .fill .. => True
      | _ => False) : ExpressionFloor expression := by
  intro env typing func root tables sourceTables valid path location info start finish source
    rootsBefore rootsAfter sourceRoots replayed returnTypes before after value run generated live continuation projects
  have empty : sourceRoots = [] := by
    cases expression <;> try contradiction
    all_goals simp only [rpExpr] at replayed
    all_goals repeat' first
      | (exact congrArg Prod.fst ((st_pure_ok _ _ _).mp replayed))
      | (obtain ⟨_, _, _, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed)
      | (split at replayed)
  rw [empty]
  exact List.nil_subset _

end Goose.Lower.Validation.SourceCanonicalRootFloors
