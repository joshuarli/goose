import Goose.Lower.Validation.SourceStatementTypingStorage
import Goose.Core.Sound.Invert

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound

theorem tyStmt_if_children {env output : TEnv} {condition : Expr} {thenBlock : Core.Block}
    {otherwise : Option Core.Block} {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.ifS condition thenBlock otherwise origin) start = .ok (output, finish)) :
    ∃ conditionFinish thenType thenFinish,
      Core.tyExpr env condition start = .ok (.bool, conditionFinish) ∧
      Core.tyBlock env [] thenBlock conditionFinish = .ok (thenType, thenFinish) ∧
      (match otherwise with
       | none => finish = thenFinish
       | some body => ∃ type, Core.tyBlock env [] body thenFinish = .ok (type, finish)) ∧
      output = env := by
  cases otherwise <;> simp only [Core.tyStmt] at source <;> inv at source
  case none =>
    obtain ⟨_, conditionType, conditionFinish, conditionChecked, conditionEq,
      thenType, thenFinish, thenChecked, outputEq, finishEq⟩ := source
    subst conditionType
    exact ⟨conditionFinish, thenType, thenFinish, conditionChecked, thenChecked, finishEq, outputEq⟩
  case some body =>
    obtain ⟨_, conditionType, conditionFinish, conditionChecked, conditionEq,
      thenType, thenFinish, thenChecked, elseType, elseFinish, elseChecked, outputEq, finishEq⟩ := source
    subst conditionType
    subst finish
    exact ⟨conditionFinish, thenType, thenFinish, conditionChecked, thenChecked, ⟨elseType, elseChecked⟩, outputEq⟩

theorem tyStmt_while_children {env output : TEnv} {condition : Expr} {body : Core.Block}
    {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.while condition body origin) start = .ok (output, finish)) :
    ∃ conditionFinish bodyType,
      Core.tyExpr env condition start = .ok (.bool, conditionFinish) ∧
      Core.tyBlock { env with loops := env.loops + 1 } [] body conditionFinish = .ok (bodyType, finish) ∧
      output = env := by
  simp only [Core.tyStmt] at source
  inv at source
  obtain ⟨_, conditionType, conditionFinish, conditionChecked, conditionEq,
    bodyType, bodyFinish, bodyChecked, outputEq, finishEq⟩ := source
  subst conditionType
  subst finish
  exact ⟨conditionFinish, bodyType, conditionChecked, bodyChecked, outputEq⟩

theorem tyStmt_forRange_children {env output : TEnv} {x : VarId} {lo hi : Expr}
    {body : Core.Block} {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.forRange x lo hi body origin) start = .ok (output, finish)) :
    ∃ localVar integer lowerStart lowerFinish upperFinish bodyType,
      declare env x body.scope start = .ok (localVar, lowerStart) ∧
      Core.tyExpr env lo lowerStart = .ok (.int integer, lowerFinish) ∧
      Core.tyExpr env hi lowerFinish = .ok (.int integer, upperFinish) ∧
      localVar.ty = .int integer ∧
      Core.tyBlock { env with loops := env.loops + 1, visible := x :: env.visible }
        [] body upperFinish = .ok (bodyType, finish) ∧ output = env := by
  simp only [Core.tyStmt] at source
  inv at source
  simp only [beq_iff_eq] at source
  obtain ⟨_, localVar, lowerStart, declared, lowerType, lowerFinish, lowerChecked,
    integer, lowerTypeEq, upperType, upperFinish, upperChecked, upperInteger,
    upperTypeEq, integerEq, binderType, bodyType, bodyFinish, bodyChecked, outputEq, finishEq⟩ := source
  subst upperInteger
  subst lowerType
  subst upperType
  subst finish
  exact ⟨localVar, integer, lowerStart, lowerFinish, upperFinish, bodyType,
    declared, lowerChecked, upperChecked, binderType, bodyChecked, outputEq⟩

theorem tyStmt_forEach_children {env output : TEnv} {x : VarId} {index : Option VarId}
    {view : View} {byRef : Bool} {body : Core.Block} {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.forEach x index view byRef body origin) start = .ok (output, finish)) :
    ∃ localVar element writable indexStart viewStart viewFinish bodyType,
      declare env x body.scope start = .ok (localVar, indexStart) ∧
      declareIndex env body.scope index indexStart = .ok ((), viewStart) ∧
      Core.tyView env view viewStart = .ok ((element, writable), viewFinish) ∧
      loopVarOk localVar byRef element writable viewFinish = .ok ((), viewFinish) ∧
      Core.tyBlock { env with loops := env.loops + 1, visible := x :: index.toList ++ env.visible }
        [] body viewFinish = .ok (bodyType, finish) ∧ output = env := by
  simp only [Core.tyStmt] at source
  inv at source
  obtain ⟨_, localVar, indexStart, declared, viewStart, indexChecked, element, writable,
    viewFinish, viewChecked, binderFinish, binderChecked,
    bodyType, bodyFinish, bodyChecked, outputEq, finishEq⟩ := source
  have binderState : binderFinish = viewFinish := (loopVarOk_ok _ _ _ _ _ _ binderChecked).1
  subst binderFinish
  subst finish
  exact ⟨localVar, element, writable, indexStart, viewStart, viewFinish, bodyType,
    declared, indexChecked, viewChecked, binderChecked, bodyChecked, outputEq⟩

theorem tyStmt_forEach_bindings {env output : TEnv} {x : VarId} {index : Option VarId}
    {view : View} {byRef : Bool} {body : Core.Block} {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.forEach x index view byRef body origin) start = .ok (output, finish)) :
    x = start ∧ ∃ localVar,
      env.vars[x]? = some localVar ∧ localVar.scope = body.scope ∧
      (∀ i, index = some i → i = start + 1 ∧ ∃ indexVar,
        env.vars[i]? = some indexVar ∧ indexVar.scope = body.scope ∧ indexVar.ty = .int .i64) := by
  obtain ⟨localVar, element, writable, indexStart, viewStart, viewFinish, bodyType,
    declared, indexChecked, _⟩ := tyStmt_forEach_children source
  have declaration := declare_ok _ _ _ _ _ declared
  have indexFacts := declareIndex_ok _ _ _ _ _ indexChecked
  refine ⟨declaration.1, localVar, declaration.2.1, declaration.2.2.1, ?_⟩
  intro i atIndex
  obtain ⟨number, indexVar, row, indexScope, indexType⟩ := indexFacts.2 i atIndex
  exact ⟨number.trans declaration.2.2.2.2, indexVar, row, indexScope, indexType⟩

end Goose.Lower.Validation
