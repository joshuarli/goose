import Goose.Lower.Validation.SourceReplacementWriterLedgerChildSpansLiveBoundStarts

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR

theorem Fragment.children_liveBound (fragment : Fragment) (env : LEnv) (before : LS)
    (bounded : LiveBound before) : ChildrenLiveBound (fragment.children env before) := by
  cases fragment with
  | expression expression =>
    cases expression with
    | lit type value => trivial
    | bool value => trivial
    | read place => exact ⟨bounded, trivial⟩
    | ref mutability place => exact ⟨bounded, trivial⟩
    | slice mutability view low high origin =>
      exact ⟨bounded, liveBound_lowerView view env before bounded,
        liveBound_of_advB (advB_lowerBound low) env _ (liveBound_lowerView view env before bounded), trivial⟩
    | len view => exact ⟨bounded, trivial⟩
    | un operation expression origin => exact ⟨bounded, trivial⟩
    | bin operation left right origin => exact ⟨bounded, liveBound_lowerExpr left env before bounded, trivial⟩
    | cmp operation left right => exact ⟨bounded, liveBound_lowerExpr left env before bounded, trivial⟩
    | and left right => exact ⟨bounded, shortCircuitChild_liveBound _ _ _ _ _⟩
    | or left right => exact ⟨bounded, shortCircuitChild_liveBound _ _ _ _ _⟩
    | not expression => exact ⟨bounded, trivial⟩
    | conv kind target expression origin => exact ⟨bounded, trivial⟩
    | call function arguments origin => exact argumentChildren_liveBound env arguments before bounded
    | push place expression origin => exact ⟨bounded, liveBound_lowerPlace place env before bounded, trivial⟩
    | pop place origin => exact ⟨bounded, trivial⟩
    | ifE condition yes no => exact ⟨bounded, branchChildren_liveBound _ _ _ _ _ _ _⟩
    | blockE block => exact ⟨bounded, trivial⟩
    | arrLit type expressions => exact expressionChildren_liveBound env expressions before bounded
    | fill type expression => exact ⟨bounded, trivial⟩
    | structLit type expressions => exact expressionChildren_liveBound env expressions before bounded
  | place place =>
    cases place with
    | var variableId => trivial
    | global globalId => trivial
    | deref expression => exact ⟨bounded, trivial⟩
    | field place fieldIndex => exact ⟨bounded, trivial⟩
    | elem view expression origin => exact ⟨bounded, liveBound_lowerView view env before bounded, trivial⟩
  | view view => cases view <;> exact ⟨bounded, trivial⟩
  | bound bound =>
    cases bound with
    | omitted => trivial
    | expr expression => exact ⟨bounded, trivial⟩
    | fromEnd expression => exact ⟨bounded, trivial⟩
  | statement loop statement =>
    cases statement with
    | letS variableId expression origin => exact ⟨bounded, trivial⟩
    | rebind variableId expression origin => exact ⟨bounded, trivial⟩
    | expr expression origin => exact ⟨bounded, trivial⟩
    | assertS expression origin => exact ⟨bounded, trivial⟩
    | exit expression origin => exact ⟨bounded, trivial⟩
    | assign place expression origin => exact ⟨bounded, liveBound_lowerPlace place env before bounded, trivial⟩
    | popN place expression origin => exact ⟨bounded, liveBound_lowerPlace place env before bounded, trivial⟩
    | assignOp operation place expression origin =>
      exact ⟨bounded, liveBound_of_advB (advB_emitDef _) env _ (liveBound_lowerPlace place env before bounded), trivial⟩
    | assignWhole place expression origin =>
      exact ⟨bounded, liveBound_of_advB (advB_emitEffect _) env _ (liveBound_lowerPlace place env before bounded), trivial⟩
    | append place view origin => exact ⟨bounded, liveBound_lowerPlace place env before bounded, trivial⟩
    | resize place size fill origin =>
      have placeBound := liveBound_lowerPlace place env before bounded
      have countBound := liveBound_lowerExpr size env (lowerPlace place env before).2 placeBound
      cases fill <;> exact ⟨bounded, placeBound, by first | trivial | exact ⟨countBound, trivial⟩⟩
    | clear place origin => exact ⟨bounded, trivial⟩
    | ifS condition yes no origin => exact ⟨bounded, branchChildren_liveBound _ _ _ _ _ _ _⟩
    | «while» condition body origin => exact whileChildren_liveBound _ _ _ _
    | forRange variableId low high body origin =>
      exact ⟨bounded, liveBound_lowerExpr low env before bounded, rangeChild_liveBound _ _ _ _ _ _ _⟩
    | forEach variableId index view byRef body origin => exact ⟨bounded, eachChild_liveBound _ _ _ _ _ _ _ _⟩
    | ret expression origin => cases expression <;> first | trivial | exact ⟨bounded, trivial⟩
    | brk origin => trivial
    | cont origin => trivial
    | abort kind origin => trivial
    | print arguments origin => exact printChildren_liveBound env arguments before bounded
  | block loop bindings want block =>
    cases block with
    | mk scope statements value =>
      let entered := (emitEffect (.enter scope) env before).2
      let pushed := (pushScope scope env entered).2
      let initialized := (initSlots bindings env pushed).2
      let stated := (lowerStmts loop statements env initialized).2
      have enteredBound : LiveBound entered := liveBound_of_advB (advB_emitEffect _) env before bounded
      have pushedBound : LiveBound pushed := by simpa only [LiveBound, pushed, pushScope_run] using enteredBound
      have initializedBound : LiveBound initialized := liveBound_of_advB (advB_initSlots bindings) env pushed pushedBound
      have statedBound : LiveBound stated := liveBound_lowerStmts loop statements env initialized initializedBound
      apply ChildrenLiveBound.append
      · exact statementChildren_liveBound env loop statements initialized initializedBound
      · cases value <;> first | trivial | exact ⟨statedBound, trivial⟩

theorem Fragment.child_liveBound {fragment child : Fragment} {env : LEnv} {before start : LS} {index : Nat}
    (bounded : LiveBound before) (row : fragment.child? env before index = some (child, start)) : LiveBound start :=
  (fragment.children_liveBound env before bounded).member (Fragment.child_member row)

#print axioms Fragment.children_liveBound
#print axioms Fragment.child_liveBound

end Goose.Lower.Validation.SourceReplacementWriterLedger
