import Goose.Lower.Validation.SourceCanonicalRootFloorsContracts

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core Goose.Core.Sound Goose.GIR ReplacementContentFlowSource

theorem arguments_nil_floor : ArgumentsFloor [] := by
  intro env typing func root tables sourceTables valid locations callee params start finish arity source
    rootsBefore rootsAfter argumentRoots replayed returnTypes before after values run generated live continuation projects
  obtain rfl := congrArg Prod.fst ((st_pure_ok _ _ _).mp replayed)
  intro index roots present
  simp at present

private theorem floors_cons {env : PEnv} {func : Func} {headRoots : List RootRef} {headValue : ValueId}
    {restRoots : List (List RootRef)} {restValues : List ValueId}
    (head : headRoots ⊆ canonicalValueRoots env func headValue)
    (rest : ∀ (index : Nat) (roots : List RootRef), restRoots[index]? = some roots →
      ∃ value, restValues[index]? = some value ∧ roots ⊆ canonicalValueRoots env func value) :
    ∀ (index : Nat) (roots : List RootRef), (headRoots :: restRoots)[index]? = some roots →
      ∃ value, (headValue :: restValues)[index]? = some value ∧ roots ⊆ canonicalValueRoots env func value := by
  intro index roots present
  cases index with
  | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at present
            subst roots; exact ⟨headValue, rfl, head⟩
  | succ index => exact rest index roots present

theorem arguments_byValue_floor (expression : Expr) (rest : List Arg)
    (child : ExpressionFloor expression) (tail : ArgumentsFloor rest) : ArgumentsFloor (.byVal expression :: rest) := by
  intro env typing func root tables sourceTables valid locations callee params start finish arity source
    rootsBefore rootsAfter argumentRoots replayed returnTypes before after values run generated live continuation projects
  cases params with
  | nil => simp at arity
  | cons param params =>
    obtain ⟨localVar, argType, childStart, childFinish, restStart, row, childSource, permission, restSource⟩ :=
      tyArgs_byVal_head source
    simp only [rpArgs] at replayed
    obtain ⟨headRoots, rootsMiddle, childReplay, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
    obtain ⟨restRoots, _, restReplay, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
    have rootShape := congrArg Prod.fst ((st_pure_ok _ _ _).mp replayed)
    dsimp only at rootShape
    subst argumentRoots
    simp only [lowerArgs, lowerArg] at run
    obtain ⟨headValue, middle, childRun, run⟩ := bind_eq.mp run
    obtain ⟨restValues, restAfter, restRun, run⟩ := bind_eq.mp run
    obtain ⟨rfl, rfl⟩ := pure_eq.mp run
    have suffix := advB_lowerArgs rest _ _ _ _ restRun
    have middleLive := (dead_lowerArgs rest).live_before restRun live
    obtain ⟨childPath, childLocation⟩ := locations 0 (.byVal expression) rfl
    have headFloor := child tables sourceTables valid childLocation childSource childReplay childRun
      generated middleLive (continuation.of_advance suffix) (projects.of_advance suffix)
    have tailLocations : ∀ (index : Nat) (argument : Arg), rest[index]? = some argument →
        ∃ path, DemandNodeAt root path (argumentSourceNode argument) := by
      intro index argument present
      exact locations (index + 1) argument present
    exact floors_cons headFloor (tail tables sourceTables valid tailLocations (by simpa using arity)
      restSource restReplay restRun (generated.lowerExpr expression childRun) live continuation projects)

theorem arguments_byReference_floor (mode : Mutability) (place : Place) (rest : List Arg)
    (child : PlaceFloor place) (tail : ArgumentsFloor rest) : ArgumentsFloor (.byRef mode place :: rest) := by
  intro env typing func root tables sourceTables valid locations callee params start finish arity source
    rootsBefore rootsAfter argumentRoots replayed returnTypes before after values run generated live continuation projects
  cases params with
  | nil => simp at arity
  | cons param params =>
    obtain ⟨localVar, placeInfo, childFinish, restStart, row, placeSource, writable, permission, restSource⟩ :=
      tyArgs_byRef_head source
    simp only [rpArgs] at replayed
    obtain ⟨headRoots, rootsMiddle, childReplay, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
    obtain ⟨restRoots, _, restReplay, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
    have rootShape := congrArg Prod.fst ((st_pure_ok _ _ _).mp replayed)
    dsimp only at rootShape
    subst argumentRoots
    simp only [lowerArgs] at run
    obtain ⟨headValue, middle, childRun, run⟩ := bind_eq.mp run
    obtain ⟨restValues, restAfter, restRun, run⟩ := bind_eq.mp run
    obtain ⟨rfl, rfl⟩ := pure_eq.mp run
    have tailAdvance := advB_lowerArgs rest _ _ _ _ restRun
    have middleLive := (dead_lowerArgs rest).live_before restRun live
    have lowering := childRun
    simp only [lowerArg] at lowering
    obtain ⟨address, addressed, placeRun, borrowed⟩ := bind_eq.mp lowering
    have borrowedAdvance := advB_borrowTo mode address _ _ _ _ borrowed
    have suffix := borrowedAdvance.trans tailAdvance
    have addressedLive := (dead_borrowTo mode address).live_before borrowed middleLive
    obtain ⟨childPath, childLocation⟩ := locations 0 (.byRef mode place) rfl
    have placeFloor := child tables sourceTables valid childLocation placeSource childReplay placeRun
      generated addressedLive (continuation.of_advance suffix) (projects.of_advance suffix)
    have headFloor := fun root member => tables.borrowTo_floor (generated.lowerPlace place placeRun)
      borrowed middleLive (continuation.of_advance tailAdvance) (placeFloor (a := root) member)
    have tailLocations : ∀ (index : Nat) (argument : Arg), rest[index]? = some argument →
        ∃ path, DemandNodeAt root path (argumentSourceNode argument) := by
      intro index argument present
      exact locations (index + 1) argument present
    exact floors_cons headFloor (tail tables sourceTables valid tailLocations (by simpa using arity)
      restSource restReplay restRun (generated.lowerArg (.byRef mode place) childRun) live continuation projects)

end Goose.Lower.Validation.SourceCanonicalRootFloors
