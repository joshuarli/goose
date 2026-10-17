import Goose.Lower.Validation.SourceCanonicalRootFloorsContracts

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core Goose.Core.Sound Goose.GIR ReplacementContentFlowSource

theorem variable_floor (slot : VarId) : PlaceFloor (.var slot) := by
  intro env typing func root tables sourceTables valid path location info start finish source
    rootsBefore rootsAfter sourceRoots replayed returnTypes before after value run generated live continuation projects
  have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp replayed)
  dsimp only at shape
  rw [shape]
  intro found member
  obtain rfl := List.mem_singleton.mp member
  obtain ⟨block, member, definition⟩ := emitted_definition_native generated run live continuation
  exact lowerPlace_var_canonical_floor generated run live continuation
    (tables.definitions _ member _ _ definition) _ _ _

theorem global_floor (global : GlobalId) : PlaceFloor (.global global) := by
  intro env typing func root tables sourceTables valid path location info start finish source
    rootsBefore rootsAfter sourceRoots replayed returnTypes before after value run generated live continuation projects
  have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp replayed)
  dsimp only at shape
  rw [shape]
  intro found member
  obtain rfl := List.mem_singleton.mp member
  obtain ⟨block, member, definition⟩ := emitted_definition_native generated run live continuation
  exact lowerPlace_global_canonical_floor generated run live continuation
    (tables.definitions _ member _ _ definition) _ _ _

theorem field_floor (owner : Place) (index : Nat) (child : PlaceFloor owner) :
    PlaceFloor (.field owner index) := by
  intro env typing func root tables sourceTables valid path location info start finish source
    rootsBefore rootsAfter sourceRoots replayed returnTypes before after value run generated live continuation projects
  simp only [tyPlace] at source
  obtain ⟨ownerInfo, ownerFinish, ownerSource, _⟩ := (st_bind_ok _ _ _ _).mp source
  simp only [lowerPlace] at run
  obtain ⟨address, middle, ownerRun, emitted⟩ := bind_eq.mp run
  have middleLive := (dead_emitDef _).live_before emitted live
  have suffix := advB_emitDef _ _ _ _ _ emitted
  have ownerFloor := child tables sourceTables valid (location.snoc 0 rfl) ownerSource replayed
    ownerRun generated middleLive (continuation.of_advance suffix) (projects.of_advance suffix)
  exact fun _ member => tables.emitted_forward_floor (generated.lowerPlace owner ownerRun)
    emitted live continuation (.fieldAddr address index) (ownerFloor member)

theorem dereference_floor (expression : Expr) (child : ExpressionFloor expression) :
    PlaceFloor (.deref expression) := by
  intro env typing func root tables sourceTables valid path location info start finish source
    rootsBefore rootsAfter sourceRoots replayed returnTypes before after value run generated live continuation projects
  cases special : sliceRefTy typing expression with
  | none =>
      obtain ⟨mode, childFinish, childSource⟩ := tyPlace_deref_child special source
      exact child tables sourceTables valid (location.snoc 0 rfl) childSource replayed
        run generated live continuation projects
  | some type =>
      exact special_dereference_canonical_floor tables sourceTables special source replayed run generated live projects

theorem element_floor (view : View) (index : Expr) (origin : OriginId) (child : ViewFloor view) :
    PlaceFloor (.elem view index origin) := by
  intro env typing func root tables sourceTables valid path location info start finish source
    rootsBefore rootsAfter sourceRoots replayed returnTypes before after value run generated live continuation projects
  obtain ⟨viewStart, viewFinish, indexFinish, writable, integer, viewSource, _⟩ := tyPlace_elem_children source
  simp only [rpPlace] at replayed
  obtain ⟨viewRoots, _, viewReplay, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
  obtain ⟨_, _, _, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
  obtain ⟨_, _, _, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
  have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp replayed)
  dsimp only at shape
  rw [shape]
  simp only [lowerPlace] at run
  obtain ⟨sample, sampled, viewRun, run⟩ := bind_eq.mp run
  obtain ⟨offset, middle, indexRun, emitted⟩ := bind_eq.mp run
  have middleLive := (dead_emitDef _).live_before emitted live
  have sampledLive := (dead_lowerExpr index).live_before indexRun middleLive
  have indexAdvance := advB_lowerExpr index _ _ _ _ indexRun
  have emittedAdvance := advB_emitDef _ _ _ _ _ emitted
  have suffix := indexAdvance.trans emittedAdvance
  have viewFloor := child tables sourceTables valid (location.snoc 0 rfl) viewSource viewReplay
    viewRun generated sampledLive (continuation.of_advance suffix) (projects.of_advance suffix)
  exact fun _ member => tables.emitted_forward_floor
    ((generated.lowerView view viewRun).lowerExpr index indexRun) emitted live continuation
      (.indexChecked sample offset (some origin)) (viewFloor member)

theorem owner_view_floor (place : Place) (child : PlaceFloor place) : ViewFloor (.of place) := by
  intro env typing func root tables sourceTables valid path location info start finish source
    rootsBefore rootsAfter sourceRoots replayed returnTypes before after value run generated live continuation projects
  simp only [tyView] at source
  obtain ⟨placeInfo, placeFinish, placeSource, _⟩ := (st_bind_ok _ _ _ _).mp source
  simp only [rpView] at replayed
  obtain ⟨placeRoots, _, placeReplay, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
  obtain ⟨_, _, _, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
  have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp replayed)
  dsimp only at shape
  rw [shape]
  simp only [lowerView] at run
  obtain ⟨address, middle, placeRun, emitted⟩ := bind_eq.mp run
  have middleLive := (dead_emitDef _).live_before emitted live
  have suffix := advB_emitDef _ _ _ _ _ emitted
  have placeFloor := child tables sourceTables valid (location.snoc 0 rfl) placeSource placeReplay
    placeRun generated middleLive (continuation.of_advance suffix) (projects.of_advance suffix)
  exact fun _ member => tables.emitted_forward_floor (generated.lowerPlace place placeRun)
    emitted live continuation (.snapshot _ address) (placeFloor member)

theorem value_view_floor (expression : Expr) (child : ExpressionFloor expression) : ViewFloor (.val expression) := by
  intro env typing func root tables sourceTables valid path location info start finish source
    rootsBefore rootsAfter sourceRoots replayed returnTypes before after value run generated live continuation projects
  simp only [tyView] at source
  obtain ⟨childType, childFinish, childSource, _⟩ := (st_bind_ok _ _ _ _).mp source
  simp only [lowerView] at run
  obtain ⟨slice, middle, childRun, emitted⟩ := bind_eq.mp run
  have middleLive := (dead_emitDef _).live_before emitted live
  have suffix := advB_emitDef _ _ _ _ _ emitted
  have sliceFloor := child tables sourceTables valid (location.snoc 0 rfl) childSource replayed
    childRun generated middleLive (continuation.of_advance suffix) (projects.of_advance suffix)
  exact fun _ member => tables.emitted_forward_floor (generated.lowerExpr expression childRun)
    emitted live continuation (.sliceView slice) (sliceFloor member)

end Goose.Lower.Validation.SourceCanonicalRootFloors
