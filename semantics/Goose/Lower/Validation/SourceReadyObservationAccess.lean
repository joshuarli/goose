import Goose.Lower.Validation.SourceReadyObservationValues

namespace Goose.Lower.Validation.ReplacementContentFlowSource.ReadyCallObservations

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

variable {module : GIR.Module} {func : Func} {state : State} {le : LEnv} {initial : LS}

theorem recordRead (value : ValueId) (place : Place) :
    EmitsOnlyRun (ReadyCallObservations module func state) (recordReadValueRootRecipe value place) := by
  intro le before result after run
  have same : (recordReadValueRootRecipe value place le before).2.blocks = before.blocks := by
    cases place <;> simp only [recordReadValueRootRecipe_run]
    all_goals try rfl
    split <;> simp [recordValueRootSource_run]
  exact .of_blocks (by simpa only [run] using same)

theorem freeze (mutability : Mutability) (address : ValueId) :
    EmitsOnlyRun (ReadyCallObservations module func state) (freezeTo mutability address) := by
  intro le before value after run
  rcases freezeTo_cases run with same | emitted
  · exact same.2.symm ▸ .refl _ _
  · exact emitsOnly_emitDef emitted (.definition _ _ (by intros; intro same; cases same))

theorem borrow (mutability : Mutability) (address : ValueId) :
    EmitsOnlyRun (ReadyCallObservations module func state) (borrowTo mutability address) := by
  intro le before value after run
  rcases borrowTo_cases run with frozen | emitted
  · exact freeze mutability address le before value after frozen
  · exact emitsOnly_emitDef emitted (.definition _ _ (by intros; intro same; cases same))

theorem read (place : Place)
    (child : EmitsOnly (ReadyCallObservations module func state) initial (lowerPlace place le initial).2) :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerExpr (.read place) le initial).2 := by
  let addressed := lowerPlace place le initial
  have tail : EmitsOnlyRun (ReadyCallObservations module func state) (do
      let value ← emitDef (.load addressed.1)
      recordReadValueRootRecipe value place
      pure value) :=
    (emitDefinition _ (by intros; intro same; cases same)).bind fun value =>
      (recordRead value place).bind fun _ => .pure _ value
  exact child.trans (tail le addressed.2 _ _ rfl)

theorem reference (mutability : Mutability) (place : Place)
    (child : EmitsOnly (ReadyCallObservations module func state) initial (lowerPlace place le initial).2) :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerExpr (.ref mutability place) le initial).2 :=
  child.trans (borrow mutability (lowerPlace place le initial).1 le _ _ _ rfl)

theorem length (view : View)
    (child : EmitsOnly (ReadyCallObservations module func state) initial (lowerView view le initial).2) :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerExpr (.len view) le initial).2 :=
  child.trans (emitDefinition (.viewLen (lowerView view le initial).1)
    (by intros; intro same; cases same) le _ _ _ rfl)

theorem slice (mutability : Mutability) (view : View) (low high : Bound) (origin : OriginId)
    (viewChild : EmitsOnly (ReadyCallObservations module func state) initial (lowerView view le initial).2)
    (lowChild : EmitsOnly (ReadyCallObservations module func state) (lowerView view le initial).2
      (lowerBound low le (lowerView view le initial).2).2)
    (highChild : EmitsOnly (ReadyCallObservations module func state) (lowerBound low le (lowerView view le initial).2).2
      (lowerBound high le (lowerBound low le (lowerView view le initial).2).2).2) :
    EmitsOnly (ReadyCallObservations module func state) initial
      (lowerExpr (.slice mutability view low high origin) le initial).2 :=
  ((viewChild.trans lowChild).trans highChild).trans (emitDefinition
    (.viewSlice mutability (lowerView view le initial).1 (lowerBound low le (lowerView view le initial).2).1
      (lowerBound high le (lowerBound low le (lowerView view le initial).2).2).1 (some origin))
    (by intros; intro same; cases same) le _ _ _ rfl)

theorem placeVariable (variableId : VarId) :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerPlace (.var variableId) le initial).2 :=
  emitDefinition (.slotAddr variableId) (by intros; intro same; cases same) le initial _ _ rfl

theorem placeGlobal (global : GlobalId) :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerPlace (.global global) le initial).2 :=
  emitDefinition (.globalAddr global) (by intros; intro same; cases same) le initial _ _ rfl

theorem placeField (owner : Place) (field : Nat)
    (child : EmitsOnly (ReadyCallObservations module func state) initial (lowerPlace owner le initial).2) :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerPlace (.field owner field) le initial).2 :=
  child.trans (emitDefinition (.fieldAddr (lowerPlace owner le initial).1 field)
    (by intros; intro same; cases same) le _ _ _ rfl)

theorem placeDeref (expression : Expr)
    (child : EmitsOnly (ReadyCallObservations module func state) initial (lowerExpr expression le initial).2) :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerPlace (.deref expression) le initial).2 := child

theorem placeElement (view : View) (index : Expr) (origin : OriginId)
    (viewChild : EmitsOnly (ReadyCallObservations module func state) initial (lowerView view le initial).2)
    (indexChild : EmitsOnly (ReadyCallObservations module func state) (lowerView view le initial).2
      (lowerExpr index le (lowerView view le initial).2).2) :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerPlace (.elem view index origin) le initial).2 :=
  (viewChild.trans indexChild).trans (emitDefinition
    (.indexChecked (lowerView view le initial).1 (lowerExpr index le (lowerView view le initial).2).1 (some origin))
    (by intros; intro same; cases same) le _ _ _ rfl)

theorem viewOf (place : Place)
    (child : EmitsOnly (ReadyCallObservations module func state) initial (lowerPlace place le initial).2) :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerView (.of place) le initial).2 := by
  cases place <;>
    exact child.trans (emitDefinition (.snapshot _ _)
      (by intros; intro same; cases same) le _ _ _ rfl)

theorem viewValue (expression : Expr)
    (child : EmitsOnly (ReadyCallObservations module func state) initial (lowerExpr expression le initial).2) :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerView (.val expression) le initial).2 :=
  child.trans (emitDefinition (.sliceView (lowerExpr expression le initial).1)
    (by intros; intro same; cases same) le _ _ _ rfl)

theorem boundOmitted :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerBound .omitted le initial).2 := .refl _ _

theorem boundExpr (expression : Expr)
    (child : EmitsOnly (ReadyCallObservations module func state) initial (lowerExpr expression le initial).2) :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerBound (.expr expression) le initial).2 := child

theorem boundFromEnd (expression : Expr)
    (child : EmitsOnly (ReadyCallObservations module func state) initial (lowerExpr expression le initial).2) :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerBound (.fromEnd expression) le initial).2 := child

theorem argumentValue (expression : Expr)
    (child : EmitsOnly (ReadyCallObservations module func state) initial (lowerExpr expression le initial).2) :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerArg (.byVal expression) le initial).2 := child

theorem argumentReference (mutability : Mutability) (place : Place)
    (child : EmitsOnly (ReadyCallObservations module func state) initial (lowerPlace place le initial).2) :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerArg (.byRef mutability place) le initial).2 :=
  child.trans (borrow mutability (lowerPlace place le initial).1 le _ _ _ rfl)

theorem argumentsNil :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerArgs [] le initial).2 := .refl _ _

theorem argumentsCons (argument : Arg) (rest : List Arg)
    (head : EmitsOnly (ReadyCallObservations module func state) initial (lowerArg argument le initial).2)
    (tail : EmitsOnly (ReadyCallObservations module func state) (lowerArg argument le initial).2
      (lowerArgs rest le (lowerArg argument le initial).2).2) :
    EmitsOnly (ReadyCallObservations module func state) initial (lowerArgs (argument :: rest) le initial).2 :=
  head.trans tail

end Goose.Lower.Validation.ReplacementContentFlowSource.ReadyCallObservations
