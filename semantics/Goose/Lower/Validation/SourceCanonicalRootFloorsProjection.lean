import Goose.Lower.SourceRootCeilings
import Goose.Core.Sound.Invert

set_option Elab.async false

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core Goose.Core.Sound

private theorem mapped_roots_agree (arguments : List (List RootRef)) (declared initial actual : List RootRef)
    (checked : mapResultRoots arguments initial declared = .ok actual) :
    declared.foldl (fun roots root => unionRoots roots (match root with
      | .param parameter => arguments[parameter]?.getD []
      | .global global => [.global global]
      | .local _ => [])) initial = actual := by
  induction declared generalizing initial with
  | nil => exact ((ex_pure_ok _ _).mp checked).symm
  | cons root rest ih =>
      simp only [mapResultRoots] at checked
      obtain ⟨mapped, mappedOk, restOk⟩ := (ex_bind_ok _ _ _).mp checked
      cases root with
      | param parameter =>
          cases found : arguments[parameter]? with
          | none => simp [mapCalleeRoots, found, reject] at mappedOk
          | some entry =>
              simp only [mapCalleeRoots, found] at mappedOk
              have same := (ex_pure_ok _ _).mp mappedOk
              subst mapped
              simpa only [List.foldl_cons, found, Option.getD_some] using
                ih (unionRoots initial entry) restOk
      | global global =>
          have same := (ex_pure_ok _ _).mp mappedOk
          subst mapped
          simpa only [List.foldl_cons] using ih (unionRoots initial [.global global]) restOk
      | «local» slot => simp [mapCalleeRoots, reject] at mappedOk

theorem sourceCallRoots_agrees (env : PEnv) (context : ContextId) (arguments : List (List RootRef))
    (before after : RState) (roots : List RootRef)
    (checked : rpCall env context arguments before = .ok (roots, after)) :
    sourceCallRoots env context arguments = roots := by
  obtain ⟨called, impl, contextRow, implRow, _, _, result⟩ :=
    rpCall_ok env context arguments before roots after checked
  simp only [sourceCallRoots, contextRow, implRow]
  cases results : impl.results.toList with
  | nil =>
      simp only [callResultRoots, results] at result
      exact ((ex_pure_ok _ _).mp result).symm
  | cons type rest =>
      cases rest with
      | cons _ _ =>
          simp only [callResultRoots, results] at result
          exact ((ex_pure_ok _ _).mp result).symm
      | nil =>
          cases declared : called.resultRoots with
          | nil =>
              simp only [callResultRoots, results, declared] at result
              exact ((ex_pure_ok _ _).mp result).symm
          | cons row rest =>
              cases rest with
              | cons _ _ =>
                  simp only [callResultRoots, results, declared] at result
                  exact ((ex_pure_ok _ _).mp result).symm
              | nil =>
                  cases reference : type.isRefLike with
                  | false =>
                      simp only [reference, Bool.false_eq_true, ite_false]
                      simp only [callResultRoots, results, declared, reference, Bool.false_eq_true, ite_false] at result
                      exact ((ex_pure_ok _ _).mp result).symm
                  | true =>
                      simp only [reference, ite_true]
                      simp only [callResultRoots, results, declared, reference, ite_true] at result
                      apply Eq.trans ?_ (mapped_roots_agree arguments row [] roots result)
                      unfold sourceMappedRoots
                      apply congrArg (fun step => row.foldl step [])
                      funext prior root
                      cases root <;> rfl

theorem sourceReadRoots_agrees (env : PEnv) (place : Place) (before after : RState)
    (roots : List RootRef) (checked : readRoots env place before = .ok (roots, after)) :
    sourceReadRoots env place = roots := by
  obtain ⟨_, shape⟩ := readRoots_ok env place before (roots, after) checked
  rcases shape with ⟨varId, localVar, rfl, found, reference, annotation⟩ |
    ⟨parameter, rfl, reference, annotation⟩ | ⟨rfl, varIds, contents⟩
  · simp [sourceReadRoots, found, reference, annotation]
  · simp [sourceReadRoots, reference, annotation]
  · cases place with
    | var varId =>
        cases found : env.impl.vars[varId]? with
        | none => simp [sourceReadRoots, found]
        | some localVar => simp [sourceReadRoots, found, varIds varId localVar rfl found]
    | deref expression =>
        cases expression <;> try rfl
        case read owner =>
          cases owner <;> try rfl
          case var varId => simp [sourceReadRoots, contents varId rfl]
    | _ => rfl


private theorem replay_pure_roots {expected actual : List RootRef} {before after : RState}
    (checked : (pure expected : P (List RootRef)) before = .ok (actual, after)) : expected = actual :=
  (congrArg Prod.fst ((st_pure_ok _ _ _).mp checked)).symm

mutual

theorem collectSourceExprRoots_agrees (env : PEnv) (expression : Expr) (table : SourceRootTable)
    {before after : RState} {roots : List RootRef}
    (checked : rpExpr env expression before = .ok (roots, after)) :
    (collectSourceExprRoots env expression table).1 = roots := by
  cases expression with
  | lit _ _ | bool _ | len _ | un _ _ _ | bin _ _ _ _ | cmp _ _ _ | and _ _ | or _ _ | not _
      | conv _ _ _ _ | pop _ _ | arrLit _ _ | structLit _ _ | fill _ _ =>
      change [] = roots
      simp only [rpExpr] at checked
      repeat' first
        | exact replay_pure_roots checked
        | (obtain ⟨_, _, _, checked⟩ := (st_bind_ok _ _ _ _).mp checked)
        | split at checked
  | read place =>
      change sourceReadRoots env place = roots
      simp only [rpExpr] at checked
      obtain ⟨_, _, _, checked⟩ := (st_bind_ok _ _ _ _).mp checked
      obtain ⟨_, _, _, checked⟩ := (st_bind_ok _ _ _ _).mp checked
      exact sourceReadRoots_agrees env place _ _ roots checked
  | ref permission place =>
      simp only [rpExpr] at checked
      exact collectSourcePlaceRoots_agrees env place table checked
  | slice permission view lower upper origin =>
      simp only [rpExpr] at checked
      obtain ⟨viewRoots, _, viewed, checked⟩ := (st_bind_ok _ _ _ _).mp checked
      have same : viewRoots = roots := by
        repeat' first
          | exact replay_pure_roots checked
          | (obtain ⟨_, _, _, checked⟩ := (st_bind_ok _ _ _ _).mp checked)
      rw [← same]
      exact collectSourceViewRoots_agrees env view table viewed
  | push place child origin =>
      simp only [rpExpr] at checked
      obtain ⟨placeRoots, _, placed, checked⟩ := (st_bind_ok _ _ _ _).mp checked
      have same : placeRoots = roots := by
        repeat' first
          | exact replay_pure_roots checked
          | (obtain ⟨_, _, _, checked⟩ := (st_bind_ok _ _ _ _).mp checked)
          | split at checked
      rw [← same]
      exact collectSourcePlaceRoots_agrees env place table placed
  | call context arguments origin =>
      simp only [rpExpr] at checked
      obtain ⟨argumentRoots, _, argumentsOk, checked⟩ := (st_bind_ok _ _ _ _).mp checked
      obtain ⟨_, _, _, checked⟩ := (st_bind_ok _ _ _ _).mp checked
      have same := collectSourceArgumentRoots_agrees env arguments table argumentsOk
      change sourceCallRoots env context (collectSourceArgumentRoots env arguments table).1 = roots
      rw [same]
      exact sourceCallRoots_agrees env context argumentRoots _ _ roots checked
  | blockE body =>
      simp only [rpExpr] at checked
      obtain ⟨result, _, blockOk, checked⟩ := (st_bind_ok _ _ _ _).mp checked
      have same := replay_pure_roots checked
      rw [← same]
      exact collectSourceBlockRoots_agrees env body table blockOk
  | ifE condition yes no =>
      simp only [rpExpr] at checked
      obtain ⟨_, _, _, checked⟩ := (st_bind_ok _ _ _ _).mp checked
      obtain ⟨yesResult, _, yesOk, checked⟩ := (st_bind_ok _ _ _ _).mp checked
      obtain ⟨noResult, _, noOk, checked⟩ := (st_bind_ok _ _ _ _).mp checked
      have same := replay_pure_roots checked
      let afterCondition := (collectSourceExprRoots env condition table).2
      let afterYes := (collectSourceBlockRoots env yes afterCondition).2
      change unionRoots (collectSourceBlockRoots env yes afterCondition).1
        (collectSourceBlockRoots env no afterYes).1 = roots
      rw [collectSourceBlockRoots_agrees env yes afterCondition yesOk,
        collectSourceBlockRoots_agrees env no afterYes noOk]
      exact same
termination_by sizeOf expression

theorem collectSourcePlaceRoots_agrees (env : PEnv) (place : Place) (table : SourceRootTable)
    {before after : RState} {roots : List RootRef}
    (checked : rpPlace env place before = .ok (roots, after)) :
    (collectSourcePlaceRoots env place table).1 = roots := by
  cases place with
  | var slot | global slot => exact replay_pure_roots checked
  | deref expression => exact collectSourceExprRoots_agrees env expression table checked
  | field owner field => exact collectSourcePlaceRoots_agrees env owner table checked
  | elem view index origin =>
      simp only [rpPlace] at checked
      obtain ⟨viewRoots, _, viewed, checked⟩ := (st_bind_ok _ _ _ _).mp checked
      have same : viewRoots = roots := by
        repeat' first
          | exact replay_pure_roots checked
          | (obtain ⟨_, _, _, checked⟩ := (st_bind_ok _ _ _ _).mp checked)
      rw [← same]
      exact collectSourceViewRoots_agrees env view table viewed
termination_by sizeOf place

theorem collectSourceViewRoots_agrees (env : PEnv) (view : View) (table : SourceRootTable)
    {before after : RState} {roots : List RootRef}
    (checked : rpView env view before = .ok (roots, after)) :
    (collectSourceViewRoots env view table).1 = roots := by
  cases view with
  | val expression => exact collectSourceExprRoots_agrees env expression table checked
  | of place =>
      simp only [rpView] at checked
      obtain ⟨placeRoots, _, placed, checked⟩ := (st_bind_ok _ _ _ _).mp checked
      obtain ⟨_, _, _, checked⟩ := (st_bind_ok _ _ _ _).mp checked
      have same := replay_pure_roots checked
      rw [← same]
      exact collectSourcePlaceRoots_agrees env place table placed
termination_by sizeOf view

theorem collectSourceArgumentRoots_agrees (env : PEnv) (arguments : List Arg) (table : SourceRootTable)
    {before after : RState} {roots : List (List RootRef)}
    (checked : rpArgs env arguments before = .ok (roots, after)) :
    (collectSourceArgumentRoots env arguments table).1 = roots := by
  cases arguments with
  | nil => exact (congrArg Prod.fst ((st_pure_ok _ _ _).mp checked)).symm
  | cons argument rest =>
      cases argument with
      | byVal expression =>
          simp only [rpArgs] at checked
          obtain ⟨headRoots, _, headOk, checked⟩ := (st_bind_ok _ _ _ _).mp checked
          obtain ⟨tailRoots, _, tailOk, checked⟩ := (st_bind_ok _ _ _ _).mp checked
          have same := (congrArg Prod.fst ((st_pure_ok _ _ _).mp checked)).symm
          let next := (collectSourceExprRoots env expression table).2
          change (collectSourceExprRoots env expression table).1 ::
            (collectSourceArgumentRoots env rest next).1 = roots
          rw [collectSourceExprRoots_agrees env expression table headOk,
            collectSourceArgumentRoots_agrees env rest next tailOk]
          exact same
      | byRef permission place =>
          simp only [rpArgs] at checked
          obtain ⟨headRoots, _, headOk, checked⟩ := (st_bind_ok _ _ _ _).mp checked
          obtain ⟨tailRoots, _, tailOk, checked⟩ := (st_bind_ok _ _ _ _).mp checked
          have same := (congrArg Prod.fst ((st_pure_ok _ _ _).mp checked)).symm
          let next := (collectSourcePlaceRoots env place table).2
          change (collectSourcePlaceRoots env place table).1 ::
            (collectSourceArgumentRoots env rest next).1 = roots
          rw [collectSourcePlaceRoots_agrees env place table headOk,
            collectSourceArgumentRoots_agrees env rest next tailOk]
          exact same
termination_by sizeOf arguments

theorem collectSourceBlockRoots_agrees (env : PEnv) (body : Block) (table : SourceRootTable)
    {pre : List VarId} {before after : RState} {roots : List RootRef} {range : Nat × Nat}
    (checked : rpBlockValue env pre body before = .ok ((roots, range), after)) :
    (collectSourceBlockRoots env body table).1 = roots := by
  cases body with
  | mk scope statements value =>
      obtain ⟨_, _, _, valueOk, _⟩ := rpBlockValue_ok env pre scope statements value _ _ _ _ checked
      cases value with
      | none => exact valueOk.1.symm
      | some expression =>
          let nested := { env with scopes := scope :: env.scopes }
          let next := (collectSourceStmtListRoots nested statements table).2
          exact collectSourceExprRoots_agrees nested expression next valueOk
termination_by sizeOf body

end

end Goose.Lower.Validation.SourceCanonicalRootFloors
