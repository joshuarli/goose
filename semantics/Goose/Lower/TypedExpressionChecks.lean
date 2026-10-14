import Goose.Lower.TypedExpressions
import Goose.GIR.Validate

namespace Goose.Lower.TypedExpressionChecks

open Goose.Core Goose.GIR Goose.Core.Sound

def sourceImpl : Impl :=
  { initImpl with body := .mk 0 [.expr (.bool true) 0] none }

def sourceModule : Core.Module :=
  { files := #["typed.goose"], types := #[], globals := #[], impls := #[sourceImpl],
    contexts := #[initContext], entry := 0, origins := #[⟨0, 1, "typed"⟩] }

def enteredState : St := { St.initial with nextAct := 1, nextScope := 1 }

def sourceEnv : Env := ⟨#[], 0, [(0, 0)], 1⟩

def typingEnv : TEnv :=
  { mod := sourceModule, impl := some sourceImpl, vars := #[], visible := [], loops := 0,
    inExpr := false, scopes := [0], globalLimit := 0, initializing := none }

def rootsEnv : PEnv := ⟨sourceModule, sourceImpl, initContext, [0]⟩

def sourceWorld : World := ⟨0, fun _ _ => False, fun _ _ => False, {}, 0,
  fun _ _ => False, fun _ _ => False⟩

theorem initial_store (demanded : RootInst → Prop) : StoreInv sourceModule 0 enteredState demanded := by
  constructor
  · simp [enteredState, St.initial, Store.empty]
  · simp [enteredState, St.initial, Store.empty]
  · simp [enteredState, St.initial, Store.empty]
  · simp
  · simp [enteredState, St.initial, Store.empty]
  · simp [enteredState, St.initial, Store.empty]

theorem initial_frame : Core.Sound.Frame sourceModule sourceWorld typingEnv rootsEnv sourceEnv
    enteredState [] := by
  constructor
  all_goals first
    | rfl
    | exact initial_store _
    | simp [sourceWorld, typingEnv, rootsEnv, sourceEnv, sourceImpl, initImpl, initContext,
        OwnerParameterShape, PEnv.cont, PRef, enteredState, St.initial, Store.empty]

def boolSource (profile : NumProfile) : ExprSource ⟨profile, sourceModule⟩ sourceEnv (.bool true)
    enteredState :=
  { accepted := (by cbv), plans := #[], path := [], context := .pilot rfl [],
    observation := .empty, world := sourceWorld, typingEnv := typingEnv, rootsEnv := rootsEnv,
    typingStart := 0, typingEnd := 0, ty := .bool, rootsStart := ⟨0, {}⟩,
    rootsEnd := ⟨0, {}⟩, roots := [], active := by simp [typingEnv, EvaluationContext.ActiveMatches], access := trivial,
    protection := by simp [ShrinkProtected, sourceWorld],
    observed := ObservedSafe.empty _ _ _ _, classified := (by intro h; cases h),
    permission := Or.inl (by exact Nat.le_refl 0),
    frame := (by simpa [EvaluationContext.inputFuture, DemandNode.variables, Expr.variables] using initial_frame), typed := rfl, rooted := rfl,
    effects := EffLe.refl _ }

theorem bool_source_result (profile : NumProfile) :
    ExprResult (boolSource profile) (.bool true) enteredState :=
  (boolSource profile).result 1 (.bool true) (by simp [evalExpr, pure_apply])

theorem bool_source_metadata (profile : NumProfile) :
    SourceResults (boolSource profile).typingEnv (boolSource profile).rootsEnv [] := by
  intro impl hi
  change some sourceImpl = some impl at hi
  cases hi
  exact ⟨rfl, rfl⟩

theorem reject_wrong_source_results : ¬ SourceResults typingEnv rootsEnv [.bool] := by
  intro h
  have := (h sourceImpl rfl).2
  cases this

#guard match Core.validate sourceModule, GIR.validate (lower sourceModule) with
  | .ok _, .ok _ => true
  | _, _ => false

end Goose.Lower.TypedExpressionChecks
