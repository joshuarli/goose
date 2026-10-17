import Goose.Lower.Validation.ExpressionTypingContentsChildren
import Goose.Lower.GeneratedTargetFramesSource

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem lowerView_of_fresh_contents_of_place {place : Place} {le : LEnv}
    {before middle after : LS} {owner value : ValueId} {first : Nat} {current : BlockId}
    (placeRun : lowerPlace place le before = (owner, middle))
    (evidence : FreshContentsEvidence le first middle owner)
    (checked : middle.DenseDefinitions) (bounded : LiveBound middle) (live : middle.cur = some current)
    (run : lowerView (.of place) le before = (value, after)) :
    FreshContentsEvidence le first after value := by
  cases place <;>
    simp only [lowerView, bind_run, placeRun] at run <;>
    apply evidence.emitDef_dependency checked bounded live run
  all_goals
    intro authorized allowed
    exact allowed

theorem lowerPlace_elem_fresh_contents_of_children {view : View} {index : Expr} {origin : OriginId}
    {le : LEnv} {before viewAfter indexAfter after : LS} {viewValue indexValue value : ValueId}
    {first : Nat} {current : BlockId}
    (viewRun : lowerView view le before = (viewValue, viewAfter))
    (indexRun : lowerExpr index le viewAfter = (indexValue, indexAfter))
    (evidence : FreshContentsEvidence le first viewAfter viewValue)
    (checked : viewAfter.DenseDefinitions) (bounded : LiveBound viewAfter)
    (live : indexAfter.cur = some current)
    (run : lowerPlace (.elem view index origin) le before = (value, after)) :
    FreshContentsEvidence le first after value := by
  have retained := evidence.of_framed_run indexRun (dense_lowerExpr index) (advB_lowerExpr index)
    (types_lowerExpr index) (generatedTargetFrame_lowerExpr none index) checked bounded (by trivial)
  have indexDense := (dense_lowerExpr index le viewAfter indexValue indexAfter indexRun checked bounded).1
  have indexBounded := (dense_lowerExpr index le viewAfter indexValue indexAfter indexRun checked bounded).2.1
  have emitted : emitDef (.indexChecked viewValue indexValue (some origin)) le indexAfter = (value, after) := by
    simpa only [lowerPlace, bind_run, viewRun, indexRun] using run
  apply retained.emitDef_dependency indexDense indexBounded live emitted
  intro authorized allowed
  exact allowed

theorem lowerView_val_fresh_contents_of_child {expr : Expr} {element : Ty} {le : LEnv}
    {before middle after : LS} {child value : ValueId} {current : BlockId}
    (childRun : lowerExpr expr le before = (child, middle))
    (childTyped : middle.vals[child]? = some (some (.data (.slice .mutable element))))
    (checked : middle.DenseDefinitions) (bounded : LiveBound middle) (live : middle.cur = some current)
    (run : lowerView (.val expr) le before = (value, after)) :
    FreshContentsEvidence le middle.vals.size after value := by
  have emitted : emitDef (.sliceView child) le middle = (value, after) := by
    simpa only [lowerView, bind_run, childRun] using run
  have recorded := sliceView_typed (le := le) childTyped live
  rw [emitted] at recorded
  apply freshContentsEvidence_definition checked bounded live emitted
  simpa [ContentsOperation, typedPermissions, recorded.2]

theorem lowerPlace_deref_fresh_contents_of_child {env : Core.TEnv} {expr : Expr}
    {info : PlaceInfo} {start finish : Nat}
    (source : Core.tyPlace env (.deref expr) start = .ok (info, finish))
    (container : ContentsTarget info.ty) (contents : info.contentsWritable = true)
    {results : List Ty} {before after : LS} {value : ValueId} {first : Nat}
    (run : lowerPlace (.deref expr) (lowerEnv env.mod env.vars results) before = (value, after))
    (child : ∀ childFinish, Core.tyExpr env expr start = .ok (.ref .mutable info.ty, childFinish) →
      lowerExpr expr (lowerEnv env.mod env.vars results) before = (value, after) →
      FreshContentsEvidence (lowerEnv env.mod env.vars results) first after value) :
    FreshContentsEvidence (lowerEnv env.mod env.vars results) first after value := by
  obtain ⟨childFinish, childSource⟩ := tyPlace_deref_contents_child source container contents
  exact child childFinish childSource run

#print axioms lowerPlace_elem_fresh_contents_of_children

end Goose.Lower.Validation
