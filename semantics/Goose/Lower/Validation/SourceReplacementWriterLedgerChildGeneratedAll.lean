import Goose.Lower.Validation.SourceReplacementWriterLedgerChildGeneratedLoops

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR

theorem Fragment.children_generated (fragment : Fragment) (env : LEnv) (before : LS)
    (checked : GeneratedBuilderState before) (bounds : fragment.loopTargets before) :
    ChildrenGenerated (fragment.children env before) := by
  cases fragment with
  | expression expression =>
    cases expression with
    | lit type value => trivial
    | bool value => trivial
    | read place => exact ⟨⟨checked, trivial⟩, trivial⟩
    | ref mutability place => exact ⟨⟨checked, trivial⟩, trivial⟩
    | slice mutability view low high origin =>
      exact ⟨⟨checked, trivial⟩, ⟨checked.lowerView view rfl, trivial⟩,
        ⟨(checked.lowerView view (env := env) rfl).lowerBound low rfl, trivial⟩, trivial⟩
    | len view => exact ⟨⟨checked, trivial⟩, trivial⟩
    | un operation expression origin => exact ⟨⟨checked, trivial⟩, trivial⟩
    | bin operation left right origin => exact ⟨⟨checked, trivial⟩, ⟨checked.lowerExpr left rfl, trivial⟩, trivial⟩
    | cmp operation left right => exact ⟨⟨checked, trivial⟩, ⟨checked.lowerExpr left rfl, trivial⟩, trivial⟩
    | and left right => exact ⟨⟨checked, trivial⟩, shortCircuitChild_generated _ _ _ _ _ (checked.lowerExpr left rfl)⟩
    | or left right => exact ⟨⟨checked, trivial⟩, shortCircuitChild_generated _ _ _ _ _ (checked.lowerExpr left rfl)⟩
    | not expression => exact ⟨⟨checked, trivial⟩, trivial⟩
    | conv kind target expression origin => exact ⟨⟨checked, trivial⟩, trivial⟩
    | call function arguments origin => exact argumentChildren_generated env arguments before checked
    | push place expression origin => exact ⟨⟨checked, trivial⟩, ⟨checked.lowerPlace place rfl, trivial⟩, trivial⟩
    | pop place origin => exact ⟨⟨checked, trivial⟩, trivial⟩
    | ifE condition yes no => exact ⟨⟨checked, trivial⟩,
        branchChildren_generated _ _ _ _ _ _ _ (checked.lowerExpr condition rfl) trivial⟩
    | blockE block => exact ⟨⟨checked, trivial⟩, trivial⟩
    | arrLit type expressions => exact expressionChildren_generated env expressions before checked
    | fill type expression => exact ⟨⟨checked, trivial⟩, trivial⟩
    | structLit type expressions => exact expressionChildren_generated env expressions before checked
  | place place =>
    cases place with
    | var variableId => trivial
    | global globalId => trivial
    | deref expression => exact ⟨⟨checked, trivial⟩, trivial⟩
    | field place fieldIndex => exact ⟨⟨checked, trivial⟩, trivial⟩
    | elem view expression origin => exact ⟨⟨checked, trivial⟩, ⟨checked.lowerView view rfl, trivial⟩, trivial⟩
  | view view => cases view <;> exact ⟨⟨checked, trivial⟩, trivial⟩
  | bound bound =>
    cases bound with
    | omitted => trivial
    | expr expression => exact ⟨⟨checked, trivial⟩, trivial⟩
    | fromEnd expression => exact ⟨⟨checked, trivial⟩, trivial⟩
  | statement loop statement =>
    cases statement with
    | letS variableId expression origin => exact ⟨⟨checked, trivial⟩, trivial⟩
    | rebind variableId expression origin => exact ⟨⟨checked, trivial⟩, trivial⟩
    | expr expression origin => exact ⟨⟨checked, trivial⟩, trivial⟩
    | assertS expression origin => exact ⟨⟨checked, trivial⟩, trivial⟩
    | exit expression origin => exact ⟨⟨checked, trivial⟩, trivial⟩
    | assign place expression origin => exact ⟨⟨checked, trivial⟩, ⟨checked.lowerPlace place rfl, trivial⟩, trivial⟩
    | popN place expression origin => exact ⟨⟨checked, trivial⟩, ⟨checked.lowerPlace place rfl, trivial⟩, trivial⟩
    | assignOp operation place expression origin =>
      exact ⟨⟨checked, trivial⟩, ⟨(checked.lowerPlace place (env := env) rfl).emitDef _ rfl, trivial⟩, trivial⟩
    | assignWhole place expression origin =>
      exact ⟨⟨checked, trivial⟩, ⟨(checked.lowerPlace place (env := env) rfl).emitEffect _ rfl, trivial⟩, trivial⟩
    | append place view origin => exact ⟨⟨checked, trivial⟩, ⟨checked.lowerPlace place rfl, trivial⟩, trivial⟩
    | resize place size fill origin =>
      have placeGenerated := checked.lowerPlace place (env := env) rfl
      have countGenerated := placeGenerated.lowerExpr size (env := env) rfl
      cases fill <;> exact ⟨⟨checked, trivial⟩, ⟨placeGenerated, trivial⟩,
        by first | trivial | exact ⟨⟨countGenerated, trivial⟩, trivial⟩⟩
    | clear place origin => exact ⟨⟨checked, trivial⟩, trivial⟩
    | ifS condition yes no origin =>
      have testedBounds := bounds.mono (advB_lowerExpr condition env before _ _ rfl).ext.1
      exact ⟨⟨checked, trivial⟩,
        branchChildren_generated _ _ _ _ _ _ _ (checked.lowerExpr condition rfl) testedBounds⟩
    | «while» condition body origin => exact whileChildren_generated _ _ _ _ checked
    | forRange variableId low high body origin =>
      exact ⟨⟨checked, trivial⟩, ⟨checked.lowerExpr low rfl, trivial⟩,
        rangeChild_generated _ _ _ _ _ _ _ ((checked.lowerExpr low (env := env) rfl).lowerExpr high rfl)⟩
    | forEach variableId index view byRef body origin =>
      exact ⟨⟨checked, trivial⟩, eachChild_generated _ _ _ _ _ _ _ _ checked⟩
    | ret expression origin => cases expression <;> first | trivial | exact ⟨⟨checked, trivial⟩, trivial⟩
    | brk origin => trivial
    | cont origin => trivial
    | abort kind origin => trivial
    | print arguments origin => exact printChildren_generated env arguments before checked
  | block loop bindings want block =>
    cases block with
    | mk scope statements value =>
      let entered := (emitEffect (.enter scope) env before).2
      let pushed := (pushScope scope env entered).2
      let initialized := (initSlots bindings env pushed).2
      let stated := (lowerStmts loop statements env initialized).2
      have enteredGenerated := checked.emitEffect (.enter scope) (env := env) rfl
      have pushedGenerated : GeneratedBuilderState pushed := by
        rw [show pushed = { entered with stack := scope :: entered.stack } from congrArg Prod.snd (pushScope_run scope env entered)]
        exact ⟨enteredGenerated.dense, enteredGenerated.live, enteredGenerated.targets⟩
      have initializedGenerated := pushedGenerated.initSlots bindings (env := env) rfl
      have enteredGrowth : before.blocks.size ≤ entered.blocks.size :=
        (advB_emitEffect (.enter scope) env before _ _ rfl).ext.1
      have initializedGrowth : pushed.blocks.size ≤ initialized.blocks.size :=
        (advB_initSlots bindings env pushed _ _ rfl).ext.1
      change entered.blocks.size ≤ initialized.blocks.size at initializedGrowth
      have initializedBounds : LoopBuilderTargets loop initialized := bounds.mono
        (Nat.le_trans enteredGrowth initializedGrowth)
      have statedGenerated := initializedGenerated.lowerStmts loop statements initializedBounds (env := env) rfl
      apply ChildrenGenerated.append
      · exact statementChildren_generated env loop statements initialized initializedGenerated initializedBounds
      · cases value <;> first | trivial | exact ⟨⟨statedGenerated, trivial⟩, trivial⟩

theorem Fragment.child_generated {fragment child : Fragment} {env : LEnv} {before start : LS} {index : Nat}
    (checked : GeneratedBuilderState before) (bounds : fragment.loopTargets before)
    (row : fragment.child? env before index = some (child, start)) :
    GeneratedBuilderState start ∧ child.loopTargets start :=
  (fragment.children_generated env before checked bounds).member (Fragment.child_member row)

#print axioms Fragment.children_generated
#print axioms Fragment.child_generated

end Goose.Lower.Validation.SourceReplacementWriterLedger
