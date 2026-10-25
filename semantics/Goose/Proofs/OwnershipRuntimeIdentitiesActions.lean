import Goose.Proofs.OwnershipRuntimeIdentities

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership

open Goose.Construct
open Goose.Proofs.ExitExecution

def PreservesOwnershipBreakIdentities (action : EvalM α) : Prop :=
  ∀ state, OwnershipBreakIdentities state → OwnershipBreakIdentities (Goose.Proofs.Exit.stepState (action state))

theorem stateQuery_preservesOwnershipBreakIdentities (action : EvalM α) (query : StateQuery action) :
    PreservesOwnershipBreakIdentities action := by
  intro state valid
  rw [query state]
  exact valid

theorem preservesOwnershipBreakIdentities_fault (kind : Goose.Core.FaultKind) :
    PreservesOwnershipBreakIdentities (fault (α := α) kind) := by
  intro state valid
  exact valid

theorem preservesOwnershipBreakIdentities_pure (value : α) : PreservesOwnershipBreakIdentities (pure value) := by
  intro state fresh
  exact fresh

theorem preservesOwnershipBreakIdentities_stop (reason : Goose.Core.Stop) :
    PreservesOwnershipBreakIdentities (EvalM.stop (α := α) reason) := by
  intro state fresh
  exact fresh

theorem preservesOwnershipBreakIdentities_get : PreservesOwnershipBreakIdentities EvalM.get := by
  intro state fresh
  exact fresh

theorem preservesOwnershipBreakIdentities_get_bind (next : ExecutionState → EvalM α)
    (preserved : ∀ state, OwnershipBreakIdentities state →
      OwnershipBreakIdentities (Goose.Proofs.Exit.stepState (next state state))) :
    PreservesOwnershipBreakIdentities (EvalM.get >>= next) := preserved

theorem preservesOwnershipBreakIdentities_bind (action : EvalM α) (next : α → EvalM β)
    (first : PreservesOwnershipBreakIdentities action) (remaining : ∀ value, PreservesOwnershipBreakIdentities (next value)) :
    PreservesOwnershipBreakIdentities (action >>= next) := by
  intro state fresh
  have preserved := first state fresh
  cases result : action state with
  | ok value final =>
      simp only [result, Goose.Proofs.Exit.stepState] at preserved
      simpa only [bind, result] using remaining value final preserved
  | stop reason final => simpa only [bind, result, Goose.Proofs.Exit.stepState] using preserved
  | escape target carriers final => simpa only [bind, result, Goose.Proofs.Exit.stepState] using preserved
  | jump target kind final => simpa only [bind, result, Goose.Proofs.Exit.stepState] using preserved

theorem preservesOwnershipBreakIdentities_listMapM (action : α → EvalM β) (items : List α)
    (preserved : ∀ item, PreservesOwnershipBreakIdentities (action item)) : PreservesOwnershipBreakIdentities (items.mapM action) := by
  induction items with
  | nil => exact preservesOwnershipBreakIdentities_pure _
  | cons item rest ih =>
      rw [List.mapM_cons]
      apply preservesOwnershipBreakIdentities_bind
      · exact preserved item
      · intro value
        apply preservesOwnershipBreakIdentities_bind
        · exact ih
        · intro values; exact preservesOwnershipBreakIdentities_pure _

theorem preservesOwnershipBreakIdentities_listForIn (action : α → β → EvalM (ForInStep β)) (items : List α)
    (initial : β) (preserved : ∀ item value, PreservesOwnershipBreakIdentities (action item value)) :
    PreservesOwnershipBreakIdentities (forIn items initial action) := by
  induction items generalizing initial with
  | nil => exact preservesOwnershipBreakIdentities_pure _
  | cons item rest ih =>
      rw [List.forIn_cons]
      apply preservesOwnershipBreakIdentities_bind
      · exact preserved item initial
      · intro step
        cases step with
        | done value => exact preservesOwnershipBreakIdentities_pure _
        | yield value => exact ih value

theorem preservesOwnershipBreakIdentities_arrayForIn (action : α → β → EvalM (ForInStep β)) (items : Array α)
    (initial : β) (preserved : ∀ item value, PreservesOwnershipBreakIdentities (action item value)) :
    PreservesOwnershipBreakIdentities (forIn items initial action) := by
  rw [← Array.forIn_toList]
  exact preservesOwnershipBreakIdentities_listForIn action items.toList initial preserved

theorem preservesOwnershipBreakIdentities_rangeForIn (action : Nat → β → EvalM (ForInStep β))
    (range : Std.Legacy.Range) (initial : β)
    (preserved : ∀ index value, PreservesOwnershipBreakIdentities (action index value)) :
    PreservesOwnershipBreakIdentities (forIn range initial action) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact preservesOwnershipBreakIdentities_listForIn action _ initial preserved

theorem preservesOwnershipBreakIdentities_lift (origin : Goose.Core.OriginId) (action : ConstructionM α) :
    PreservesOwnershipBreakIdentities (liftConstruction origin action) := by
  intro state fresh
  unfold liftConstruction
  cases action state.construction <;> exact fresh

theorem preservesOwnershipBreakIdentities_freshAct : PreservesOwnershipBreakIdentities freshAct := by
  intro state valid
  exact valid

theorem preservesOwnershipBreakIdentities_freshScope : PreservesOwnershipBreakIdentities freshScope := by
  intro state valid
  exact ownershipBreakIdentities_counter valid _ (Nat.le_succ _)

theorem preservesOwnershipBreakIdentities_releaseScope (environment : RuntimeActivation) (scope scopeInst : Nat) :
    PreservesOwnershipBreakIdentities (releaseScope environment scope scopeInst) := by
  intro state valid
  exact valid


theorem preservesOwnershipBreakIdentities_setObjectOrdinal (root : Goose.Core.RootInst) (ordinal : Goose.Core.StorageId) :
    PreservesOwnershipBreakIdentities (setObjectOrdinal root ordinal) := by
  intro state fresh
  exact fresh

theorem preservesOwnershipBreakIdentities_bindStaticRoot (root : Goose.Core.RootInst) (value : Value) :
    PreservesOwnershipBreakIdentities (bindStaticRoot root value) := by
  intro state fresh
  exact fresh

theorem preservesOwnershipBreakIdentities_reserveRootObject (root : Goose.Core.RootInst) : PreservesOwnershipBreakIdentities (reserveRootObject root) := by
  unfold reserveRootObject
  apply preservesOwnershipBreakIdentities_bind
  · exact preservesOwnershipBreakIdentities_get
  · intro state
    cases state.objectOrdinals.lookup root with
    | some ordinal => exact preservesOwnershipBreakIdentities_pure _
    | none =>
        apply preservesOwnershipBreakIdentities_bind
        · exact preservesOwnershipBreakIdentities_lift _ _
        · intro ordinal
          apply preservesOwnershipBreakIdentities_bind
          · exact preservesOwnershipBreakIdentities_setObjectOrdinal root ordinal
          · intro _; exact preservesOwnershipBreakIdentities_pure _

theorem preservesOwnershipBreakIdentities_bindRoot (root : Goose.Core.RootInst) (value : Value) : PreservesOwnershipBreakIdentities (bindRoot root value) := by
  unfold bindRoot
  apply preservesOwnershipBreakIdentities_bind
  · exact preservesOwnershipBreakIdentities_get
  · intro state
    split
    · cases value <;> apply preservesOwnershipBreakIdentities_bind
      all_goals first
        | exact preservesOwnershipBreakIdentities_setObjectOrdinal _ _
        | exact preservesOwnershipBreakIdentities_reserveRootObject _
        | (intro _
           apply preservesOwnershipBreakIdentities_bind
           · exact preservesOwnershipBreakIdentities_pure _
           · intro _; exact preservesOwnershipBreakIdentities_bindStaticRoot root _)
        | (intro _; exact preservesOwnershipBreakIdentities_bindStaticRoot root _)
    · exact preservesOwnershipBreakIdentities_bindStaticRoot root value

theorem preservesOwnershipBreakIdentities_bindAll (act : Goose.Core.ActId) (scopeInst : Goose.Core.ScopeInst)
    (values : List (Goose.Core.VarId × Value)) : PreservesOwnershipBreakIdentities (bindAll act scopeInst values) := by
  unfold bindAll
  apply preservesOwnershipBreakIdentities_bind
  · apply preservesOwnershipBreakIdentities_listForIn
    intro item _
    rcases item with ⟨localVar, value⟩
    apply preservesOwnershipBreakIdentities_bind
    · exact preservesOwnershipBreakIdentities_bindRoot _ value
    · intro _; exact preservesOwnershipBreakIdentities_pure _
  · intro _; exact preservesOwnershipBreakIdentities_pure _


end Goose.Proofs.ConstructionExecutionOwnership
