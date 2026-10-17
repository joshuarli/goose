import Goose.Lower.Validation.SummaryPreservationSource

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound

def EffectFlagsLe (left right : Eff) : Prop :=
  (left.aborts = true → right.aborts = true) ∧
    (left.outputs = true → right.outputs = true)

theorem EffectFlagsLe.refl (effect : Eff) : EffectFlagsLe effect effect :=
  ⟨fun h => h, fun h => h⟩

theorem EffectFlagsLe.trans {left middle right : Eff}
    (first : EffectFlagsLe left middle) (second : EffectFlagsLe middle right) :
    EffectFlagsLe left right :=
  ⟨fun h => second.1 (first.1 h), fun h => second.2 (first.2 h)⟩

def PFlagsMono (x : P α) : Prop :=
  ∀ st a st', x st = .ok (a, st') → EffectFlagsLe st.eff st'.eff

theorem PFlagsMono.bind {x : P α} {f : α → P β}
    (hx : PFlagsMono x) (hf : ∀ a, PFlagsMono (f a)) :
    PFlagsMono (x >>= f) := by
  intro st b st' h
  obtain ⟨a, s1, h1, h2⟩ := (st_bind_ok _ _ _ _).1 h
  exact (hx _ _ _ h1).trans (hf a _ _ _ h2)

theorem PFlagsMono.pure (a : α) : PFlagsMono (pure a : P α) := by
  intro st b st' h
  have := (st_pure_ok _ _ _).1 h
  cases this
  exact EffectFlagsLe.refl _

theorem PFlagsMono.rej (r : Rule) (msg : String) :
    PFlagsMono (rejP r msg : P α) := by
  intro st b st' h
  exact ((rejP_ok _ _ _ _).1 h).elim

theorem PFlagsMono.liftV (x : V α) : PFlagsMono (liftV x) := by
  intro st b st' h
  obtain ⟨_, h2⟩ := (liftV_ok _ _ _).1 h
  cases h2
  exact EffectFlagsLe.refl _

theorem PFlagsMono.get : PFlagsMono (get : P RState) := by
  intro st b st' h
  have := (st_get_ok _ _).1 h
  cases this
  exact EffectFlagsLe.refl _

theorem PFlagsMono.modify (f : RState → RState)
    (hf : ∀ s, EffectFlagsLe s.eff (f s).eff) : PFlagsMono (modify f : P PUnit) := by
  intro st b st' h
  have := (st_modify_ok _ _ _).1 h
  cases this
  exact hf st

theorem PFlagsMono.ite {c : Prop} [Decidable c] {x y : P α}
    (hx : PFlagsMono x) (hy : PFlagsMono y) :
    PFlagsMono (if c then x else y) := by
  by_cases h : c <;> simp [h, hx, hy]

theorem PFlagsMono.addReads (rs : List RootRef) : PFlagsMono (addReads rs) := by
  unfold Goose.Core.addReads addRoots
  exact PFlagsMono.modify _ (fun _ => ⟨fun h => h, fun h => h⟩)

theorem PFlagsMono.addWrites (rs : List RootRef) : PFlagsMono (addWrites rs) := by
  unfold Goose.Core.addWrites addRoots
  exact PFlagsMono.modify _ (fun _ => ⟨fun h => h, fun h => h⟩)

theorem PFlagsMono.addGrows (rs : List RootRef) : PFlagsMono (addGrows rs) := by
  unfold Goose.Core.addGrows addRoots
  exact PFlagsMono.modify _ (fun _ => ⟨fun h => h, fun h => h⟩)

theorem PFlagsMono.addShrinks (rs : List RootRef) : PFlagsMono (addShrinks rs) := by
  unfold Goose.Core.addShrinks addRoots
  exact PFlagsMono.modify _ (fun _ => ⟨fun h => h, fun h => h⟩)

theorem PFlagsMono.rpCall (env : PEnv) (c : ContextId)
    (ar : List (List RootRef)) : PFlagsMono (rpCall env c ar) := by
  unfold Goose.Core.rpCall
  repeat' (first
    | exact PFlagsMono.pure _ | exact PFlagsMono.rej _ _ | exact PFlagsMono.liftV _
    | refine PFlagsMono.bind ?_ (fun _ => ?_)
    | split)
  refine PFlagsMono.modify _ ?_
  intro s
  simp only [callEffects]
  split
  · exact ⟨fun h => h, fun h => h⟩
  · exact ⟨fun h => by simp [h], fun h => by simp [h]⟩

theorem PFlagsMono.readRoots (env : PEnv) (p : Place) :
    PFlagsMono (readRoots env p) := by
  unfold Goose.Core.readRoots
  repeat' (first | exact PFlagsMono.pure _ | exact PFlagsMono.rej _ _ | split)

macro "pflags" : tactic => `(tactic| repeat' (first
    | exact PFlagsMono.pure _ | exact PFlagsMono.rej _ _ | exact PFlagsMono.liftV _ | exact PFlagsMono.get
    | exact PFlagsMono.addReads _ | exact PFlagsMono.addWrites _ | exact PFlagsMono.addGrows _
    | exact PFlagsMono.addShrinks _ | exact PFlagsMono.rpCall _ _ _
    | exact PFlagsMono.readRoots _ _
    | exact PFlagsMono.modify _ (fun s => by constructor <;> intro h <;> simp_all)
    | with_reducible apply_assumption
    | refine PFlagsMono.bind ?_ (fun _ => ?_)
    | refine PFlagsMono.ite ?_ ?_
    | split))

theorem rp_flags_mono_all :
    (∀ env p, PFlagsMono (rpPlace env p)) ∧ (∀ env v, PFlagsMono (rpView env v)) ∧
    (∀ env e, PFlagsMono (rpExpr env e)) ∧ (∀ env es, PFlagsMono (rpExprs env es)) ∧
    (∀ env pre b, PFlagsMono (rpBlockValue env pre b)) ∧
    (∀ env ss, PFlagsMono (rpStmts env ss)) ∧ (∀ env s, PFlagsMono (rpStmt env s)) ∧
    (∀ env as, PFlagsMono (rpPrintArgs env as)) ∧ (∀ env as, PFlagsMono (rpArgs env as)) ∧
    (∀ env b, PFlagsMono (rpBound env b)) := by
  apply rpPlace.mutual_induct
    (motive_1 := fun env p => PFlagsMono (rpPlace env p))
    (motive_2 := fun env v => PFlagsMono (rpView env v))
    (motive_3 := fun env e => PFlagsMono (rpExpr env e))
    (motive_4 := fun env es => PFlagsMono (rpExprs env es))
    (motive_5 := fun env pre b => PFlagsMono (rpBlockValue env pre b))
    (motive_6 := fun env ss => PFlagsMono (rpStmts env ss))
    (motive_7 := fun env s => PFlagsMono (rpStmt env s))
    (motive_8 := fun env as => PFlagsMono (rpPrintArgs env as))
    (motive_9 := fun env as => PFlagsMono (rpArgs env as))
    (motive_10 := fun env b => PFlagsMono (rpBound env b))
  case case34 =>
    intros
    simp only [rpStmt]
    pflags
  case case36 =>
    intros
    simp only [rpStmt]
    pflags
  all_goals (intros; (try cases ‹Option Expr›); (try cases ‹Option Block›); simp only [rpPlace, rpView, rpExpr, rpExprs, rpBlockValue, rpStmts, rpStmt, rpPrintArgs, rpArgs, rpBound, bindRoots, checkResult, noteAborts, noteOutputs]; pflags)


theorem rpExpr_flags_mono {env : PEnv} {expr : Expr} {before after : RState}
    {roots : List RootRef} (checked : rpExpr env expr before = .ok (roots, after)) :
    EffectFlagsLe before.eff after.eff :=
  rp_flags_mono_all.2.2.1 env expr _ _ _ checked

theorem rpBlockValue_flags_mono {env : PEnv} {block : Block} {pre : List VarId}
    {before after : RState} {result : List RootRef × (Nat × Nat)}
    (checked : rpBlockValue env pre block before = .ok (result, after)) :
    EffectFlagsLe before.eff after.eff :=
  rp_flags_mono_all.2.2.2.2.1 env pre block _ _ _ checked

theorem rpStmt_flags_mono {env : PEnv} {stmt : Stmt} {before after : RState}
    (checked : rpStmt env stmt before = .ok ((), after)) : EffectFlagsLe before.eff after.eff :=
  rp_flags_mono_all.2.2.2.2.2.2.1 env stmt _ _ _ checked

end Goose.Lower.Validation.SummaryPreservation
