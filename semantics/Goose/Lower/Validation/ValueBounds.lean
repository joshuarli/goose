import Goose.Lower.Validation.DeadFrontier
import Goose.Lower.Validation.ValueTypes

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def ValueRun (action : B ValueId) : Prop :=
  ∀ le before value after, action le before = (value, after) →
    after.cur.isSome = true → value < after.vals.size

theorem ValueRun.prepend {action : B α} {next : α → B ValueId}
    (bounded : ∀ value, ValueRun (next value)) : ValueRun (action >>= next) := by
  intro le before value after run live
  obtain ⟨input, mid, _, nextRun⟩ := bind_eq.mp run
  exact bounded input le mid value after nextRun live

theorem value_emitDef (op : Op) : ValueRun (emitDef op) := by
  intro le before value after run live
  cases current : before.cur with
  | none =>
    rw [emitDef_none op le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    simp [current] at live
  | some block =>
    rw [emitDef_run op le current] at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
    simp

theorem live_before {action : B α} (dead : DeadRun action)
    {le before value after} (run : action le before = (value, after))
    (live : after.cur.isSome = true) : before.cur.isSome = true := by
  cases current : before.cur
  · simp [dead _ _ _ _ run current] at live
  · rfl

theorem ValueRun.post {action : B ValueId} {next : ValueId → B α}
    (bounded : ValueRun action) (advances : ∀ value, AdvB (next value))
    (dead : ∀ value, DeadRun (next value)) :
    ValueRun (do let value ← action; let _ ← next value; pure value) := by
  intro le before value after run live
  obtain ⟨input, mid, firstRun, _, last, nextRun, pureRun⟩ :=
    (by simpa only [bind_eq] using run)
  obtain ⟨rfl, rfl⟩ := pure_eq.mp pureRun
  exact Nat.lt_of_lt_of_le (bounded _ _ _ _ firstRun (live_before (dead input) nextRun live))
    ((advances input) _ _ _ _ nextRun).vals

theorem value_whenLive (action : BlockId → B ValueId)
    (bounded : ∀ block, ValueRun (action block)) : ValueRun (whenLive 0 action) := by
  intro le before value after run live
  cases current : before.cur with
  | none =>
    rw [whenLive_none 0 action le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    simp [current] at live
  | some block =>
    rw [whenLive_some 0 action le current] at run
    exact bounded block _ _ _ _ run live

theorem value_freezeTo {action : B ValueId} (bounded : ValueRun action) (mu : Mutability) :
    ValueRun (do let value ← action; freezeTo mu value) := by
  intro le before value after run live
  obtain ⟨input, mid, firstRun, nextRun⟩ := bind_eq.mp run
  rcases freezeTo_cases nextRun with ⟨rfl, rfl⟩ | fresh
  · exact bounded _ _ _ _ firstRun live
  · exact value_emitDef _ _ _ _ _ fresh live

theorem value_borrowTo {action : B ValueId} (bounded : ValueRun action) (mu : Mutability) :
    ValueRun (do let value ← action; borrowTo mu value) := by
  intro le before value after run live
  obtain ⟨input, mid, firstRun, nextRun⟩ := bind_eq.mp run
  rcases borrowTo_cases nextRun with frozen | borrowed
  · exact value_freezeTo bounded mu le before value after
      (bind_eq.mpr ⟨input, mid, firstRun, frozen⟩) live
  · exact value_emitDef _ _ _ _ _ borrowed live

private theorem patchBrs_vals (target : BlockId) :
    ∀ incoming le before result after, patchBrs target incoming le before = (result, after) →
      after.vals = before.vals
  | [], le, before, result, after, run => (pure_eq.mp run).2.symm ▸ rfl
  | (block, value) :: rest, le, before, result, after, run => by
    simp only [patchBrs, bind_eq] at run
    obtain ⟨_, mid, patch, tail⟩ := run
    rw [patchTerm_run] at patch
    obtain ⟨_, rfl⟩ := Prod.mk.inj patch
    have same := patchBrs_vals target rest le _ result after tail
    exact same

theorem value_joinValue (endT : Option BlockId) (vt : ValueId)
    (endF : Option BlockId) (vf : ValueId) : ValueRun (joinValue endT vt endF vf) := by
  intro le before value after run live
  unfold joinValue at run
  cases endT <;> cases endF
  · simp only [bind_eq] at run
    obtain ⟨_, mid, change, pureRun⟩ := run
    rw [setCur_run] at change
    obtain ⟨_, rfl⟩ := Prod.mk.inj change
    obtain ⟨_, rfl⟩ := pure_eq.mp pureRun
    simp at live
  all_goals
    simp only [bind_eq] at run
    obtain ⟨ty, mid, typeRun, ⟨block, params⟩, allocated, allocation,
      _, patched, patch, _, resumed, resume, pureRun⟩ := run
    rw [newBlock1_run] at allocation
    obtain ⟨pair, rfl⟩ := Prod.mk.inj allocation
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj pair
    rw [setCur_run] at resume
    obtain ⟨_, rfl⟩ := Prod.mk.inj resume
    obtain ⟨rfl, rfl⟩ := pure_eq.mp pureRun
    have same := patchBrs_vals _ _ _ _ _ _ patch
    simp only at same ⊢
    rw [same]
    simp

theorem value_shortCircuit (isAnd : Bool) (input : ValueId) {rhs : B ValueId}
    (advances : AdvB rhs) : ValueRun (shortCircuit isAnd input rhs) := by
  unfold shortCircuit
  apply value_whenLive
  intro block le before value after run live
  simp only [bind_eq] at run
  obtain ⟨⟨right, join, param⟩, forked, forkRun, _, selected, select,
    result, evaluated, evaluate, _, closed, close, _, resumed, resume, pureRun⟩ := run
  have ids := (scFork_ids forkRun).1
  have sizes : forked.vals.size = before.vals.size + 1 := by
    cases current : before.cur with
    | none =>
      unfold scFork at forkRun
      cases isAnd <;>
        simp only [bind_run, newBlock0_run, newBlock1_run, pure_run,
          Bool.false_eq_true, ↓reduceIte] at forkRun <;>
        rw [emitTerm_none _ _ (by simpa using current)] at forkRun <;>
        obtain ⟨_, rfl⟩ := Prod.mk.inj forkRun <;> simp
    | some currentBlock =>
      rw [scFork_run _ _ _ current] at forkRun
      obtain ⟨_, rfl⟩ := Prod.mk.inj forkRun
      simp
  rw [setCur_run] at select resume
  obtain ⟨_, rfl⟩ := Prod.mk.inj select
  obtain ⟨_, rfl⟩ := Prod.mk.inj resume
  obtain ⟨rfl, rfl⟩ := pure_eq.mp pureRun
  have bound := (advances _ _ _ _ evaluate).vals
  have growth := (adv_emitTerm close).vals
  have id : param = before.vals.size := by
    exact (Prod.mk.inj (Prod.mk.inj ids).2).2
  simp only at bound growth ⊢
  rw [id]
  nat_omega

theorem ValueRun.inScope (scope : ScopeId) {action : B ValueId}
    (bounded : ValueRun action) : ValueRun (inScope scope action) := by
  intro le before value after run live
  obtain ⟨mid, actionRun, rfl⟩ := inScope_eq run
  exact bounded le _ value mid actionRun live

mutual

theorem value_lowerExpr : ∀ expr : Expr, ValueRun (lowerExpr expr)
  | .structLit _ _ => by
    simp only [lowerExpr]
    exact ValueRun.prepend fun _ => value_emitDef _
  | .lit _ _ => by
    simp only [lowerExpr]
    exact value_emitDef _
  | .bool _ => by
    simp only [lowerExpr]
    exact value_emitDef _
  | .read _ => by
    simp only [lowerExpr]
    exact ValueRun.prepend fun _ => value_emitDef _
  | .slice _ _ _ _ _ => by
    simp only [lowerExpr]
    exact ValueRun.prepend fun _ => ValueRun.prepend fun _ => ValueRun.prepend fun _ => value_emitDef _
  | .len _ => by
    simp only [lowerExpr]
    exact ValueRun.prepend fun _ => value_emitDef _
  | .un _ _ _ => by
    simp only [lowerExpr]
    exact ValueRun.prepend fun _ => ValueRun.prepend fun _ => value_emitDef _
  | .bin _ _ _ _ => by
    simp only [lowerExpr]
    exact ValueRun.prepend fun _ => ValueRun.prepend fun _ => ValueRun.prepend fun _ => value_emitDef _
  | .not _ => by
    simp only [lowerExpr]
    exact ValueRun.prepend fun _ => value_emitDef _
  | .conv _ _ _ _ => by
    simp only [lowerExpr]
    exact ValueRun.prepend fun _ => ValueRun.prepend fun _ => value_emitDef _
  | .push _ _ _ => by
    simp only [lowerExpr]
    exact ValueRun.prepend fun _ => ValueRun.prepend fun _ => value_emitDef _
  | .pop _ _ => by
    simp only [lowerExpr]
    exact ValueRun.prepend fun _ => value_emitDef _
  | .arrLit _ _ => by
    simp only [lowerExpr]
    exact ValueRun.prepend fun _ => value_emitDef _
  | .fill _ _ => by
    simp only [lowerExpr]
    exact ValueRun.prepend fun _ => value_emitDef _
  | .ref mu place => by
    simp only [lowerExpr]
    exact value_borrowTo (value_lowerPlace place) mu
  | .cmp _ _ _ => by
    simp only [lowerExpr]
    refine ValueRun.prepend fun _ => ValueRun.prepend fun _ => ValueRun.prepend fun ty => ?_
    cases ty with
    | data ty => cases ty <;> exact value_emitDef _
    | view _ _ => exact value_emitDef _
  | .and _ right => by
    simp only [lowerExpr]
    exact ValueRun.prepend fun _ => value_shortCircuit _ _ (advB_lowerExpr right)
  | .or _ right => by
    simp only [lowerExpr]
    exact ValueRun.prepend fun _ => value_shortCircuit _ _ (advB_lowerExpr right)
  | .call context args org => by
    simp only [lowerExpr]
    apply ValueRun.prepend
    intro values
    intro le before value after run live
    obtain ⟨result, emitted, emission, env, loaded, loading, remaining⟩ :=
      (by simpa only [bind_eq] using run)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj loading
    cases returns : le.mod.noReturn context
    · simp only [returns, Bool.false_eq_true, ↓reduceIte] at remaining
      obtain ⟨rfl, rfl⟩ := pure_eq.mp remaining
      exact value_emitDef _ _ _ _ _ emission live
    · simp only [returns, ↓reduceIte, bind_eq] at remaining
      obtain ⟨_, closed, closing, pureRun⟩ := remaining
      obtain ⟨rfl, rfl⟩ := pure_eq.mp pureRun
      cases current : emitted.cur with
      | none =>
        rw [emitTerm_none _ _ current] at closing
        obtain ⟨_, rfl⟩ := Prod.mk.inj closing
        simp [current] at live
      | some block =>
        rw [emitTerm_run _ _ current] at closing
        obtain ⟨_, rfl⟩ := Prod.mk.inj closing
        simp at live
  | .ifE _ _ _ => by
    simp only [lowerExpr]
    apply ValueRun.prepend
    intro condition
    apply value_whenLive
    intro block
    exact ValueRun.prepend fun ⟨_, _⟩ => ValueRun.prepend fun _ =>
      ValueRun.prepend fun _ => ValueRun.prepend fun _ => ValueRun.prepend fun _ =>
      ValueRun.prepend fun _ => ValueRun.prepend fun _ => value_joinValue _ _ _ _
  | .blockE body => by
    simp only [lowerExpr]
    exact value_lowerBlock _ _ body

theorem value_lowerPlace : ∀ place : Place, ValueRun (lowerPlace place)
  | .var _ => by
    simp only [lowerPlace]
    exact value_emitDef _
  | .global _ => by
    simp only [lowerPlace]
    exact value_emitDef _
  | .field _ _ => by
    simp only [lowerPlace]
    exact ValueRun.prepend fun _ => value_emitDef _
  | .elem _ _ _ => by
    simp only [lowerPlace]
    exact ValueRun.prepend fun _ => ValueRun.prepend fun _ => value_emitDef _
  | .deref expr => by
    simp only [lowerPlace]
    exact value_lowerExpr expr

theorem value_lowerBlock (context : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId)) :
    ∀ body : Core.Block, ValueRun (lowerBlock context pre true body)
  | .mk scope stmts value => by
    simp only [lowerBlock]
    apply ValueRun.prepend
    intro _
    apply ValueRun.inScope
    have bounded : ValueRun (do
        initSlots pre
        lowerStmts context stmts
        let result ← lowerBlockValue true value
        emitEffect (.leave scope)
        pure result) := by
      apply ValueRun.prepend
      intro _
      apply ValueRun.prepend
      intro _
      apply ValueRun.post (next := fun _ => emitEffect (.leave scope))
      · cases value with
        | none => exact value_emitDef _
        | some expr => exact value_lowerExpr expr
      · intro _; exact advB_emitEffect _
      · intro _; exact dead_emitEffect _
    exact bounded

end

theorem value_lowerView (view : View) : ValueRun (lowerView view) := by
  cases view <;> simp only [lowerView] <;>
    exact ValueRun.prepend fun _ => value_emitDef _

theorem value_lowerArg (arg : Arg) : ValueRun (lowerArg arg) := by
  cases arg with
  | byVal expr => exact value_lowerExpr expr
  | byRef mu place => exact value_borrowTo (value_lowerPlace place) mu

def ValueListRun (action : B (List ValueId)) : Prop :=
  ∀ le before values after, action le before = (values, after) →
    after.cur.isSome = true → ∀ value ∈ values, value < after.vals.size

theorem value_cons {head : B ValueId} {tail : B (List ValueId)}
    (boundedHead : ValueRun head) (boundedTail : ValueListRun tail)
    (advances : AdvB tail) (dead : DeadRun tail) :
    ValueListRun (do let value ← head; let values ← tail; pure (value :: values)) := by
  intro le before values after run live value member
  obtain ⟨first, mid, firstRun, rest, last, tailRun, pureRun⟩ :=
    (by simpa only [bind_eq] using run)
  obtain ⟨rfl, rfl⟩ := pure_eq.mp pureRun
  rcases List.mem_cons.mp member with rfl | member
  · exact Nat.lt_of_lt_of_le
      (boundedHead _ _ _ _ firstRun (live_before dead tailRun live))
      ((advances _ _ _ _ tailRun).vals)
  · exact boundedTail _ _ _ _ tailRun live value member

theorem values_lowerExprs : ∀ exprs : List Expr, ValueListRun (lowerExprs exprs)
  | [] => by
    intro le before values after run live value member
    obtain ⟨rfl, rfl⟩ := pure_eq.mp run
    simp at member
  | expr :: rest => by
    simp only [lowerExprs]
    exact value_cons (value_lowerExpr expr) (values_lowerExprs rest)
      (advB_lowerExprs rest) (dead_lowerExprs rest)

theorem values_lowerArgs : ∀ args : List Arg, ValueListRun (lowerArgs args)
  | [] => by
    intro le before values after run live value member
    obtain ⟨rfl, rfl⟩ := pure_eq.mp run
    simp at member
  | arg :: rest => by
    simp only [lowerArgs]
    exact value_cons (value_lowerArg arg) (values_lowerArgs rest)
      (advB_lowerArgs rest) (dead_lowerArgs rest)

theorem values_lowerBound (bound : Bound) {le before result after}
    (run : lowerBound bound le before = (result, after))
    (live : after.cur.isSome = true) :
    ∀ value ∈ result.uses, value < after.vals.size := by
  cases bound with
  | omitted =>
    obtain ⟨rfl, rfl⟩ := pure_eq.mp run
    simp [Bnd.uses]
  | expr expr | fromEnd expr =>
    simp only [lowerBound, bind_eq] at run
    obtain ⟨value, mid, expression, remaining⟩ := run
    obtain ⟨rfl, rfl⟩ := pure_eq.mp remaining
    intro used member
    have equality : used = value := by simpa [Bnd.uses] using member
    subst used
    exact value_lowerExpr expr _ _ _ _ expression live

end Goose.Lower.Validation
