import Goose.Lower.Validation.CallTyping

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

inductive OwnerPlace : Place → Prop where
  | var (id : VarId) : OwnerPlace (.var id)
  | global (id : GlobalId) : OwnerPlace (.global id)
  | derefVariable (id : VarId) : OwnerPlace (.deref (.read (.var id)))
  | derefCall (context : ContextId) (origin : OriginId) :
      OwnerPlace (.deref (.call context [] origin))
  | field {owner : Place} (index : Nat) : OwnerPlace owner → OwnerPlace (.field owner index)

theorem lowerPlace_owner_typed {place : Place} (family : OwnerPlace place)
    {env : Core.TEnv} {info : PlaceInfo} {start finish : Nat}
    (source : Core.tyPlace env place start = .ok (info, finish))
    {results : List Ty} {before after : LS} {value : ValueId}
    (run : lowerPlace place (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true) :
    ∃ mu, after.vals[value]? = some (some (.data (.ref mu info.ty))) := by
  induction family generalizing info start finish before after value with
  | var id =>
    have initial := (dead_lowerPlace (.var id)).live_before run live
    cases current : before.cur with
    | none => simp [current] at initial
    | some block =>
      have typed := lowerPlace_var_exact source results before current
      rw [run] at typed
      exact ⟨_, by simpa only [referenceType] using typed.2⟩
  | global id =>
    have initial := (dead_lowerPlace (.global id)).live_before run live
    cases current : before.cur with
    | none => simp [current] at initial
    | some block =>
      have typed := lowerPlace_global_exact source env.vars results before current
      rw [run] at typed
      exact ⟨_, by simpa only [referenceType] using typed.2⟩
  | derefVariable id =>
    have initial := (dead_lowerPlace (.deref (.read (.var id)))).live_before run live
    cases current : before.cur with
    | none => simp [current] at initial
    | some block =>
      have typed := lowerPlace_deref_read_variable_exact source results before current
      rw [run] at typed
      obtain ⟨mu, _, typed⟩ := typed
      exact ⟨mu, typed⟩
  | derefCall context origin =>
    have typed := lowerPlace_deref_call_nil_typed source env.vars results before
    rw [run] at typed
    exact typed live
  | @field owner index family inductionHypothesis =>
    have children := source
    simp only [Core.tyPlace] at children
    obtain ⟨ownerInfo, ownerFinish, ownerSource, _⟩ := (st_bind_ok _ _ _ _).mp children
    have lowering := run
    simp only [lowerPlace] at lowering
    obtain ⟨ownerValue, middle, ownerRun, emitted⟩ := bind_eq.mp lowering
    have middleLive := (dead_emitDef (.fieldAddr ownerValue index)).live_before emitted live
    obtain ⟨mu, ownerTyped⟩ := inductionHypothesis ownerSource ownerRun middleLive
    cases current : middle.cur with
    | none => simp [current] at middleLive
    | some block =>
      have typed := lowerPlace_field_typed_of_owner ownerSource source ownerRun ownerTyped current
      rw [run] at typed
      obtain ⟨resultMu, _, resultTyped⟩ := typed
      exact ⟨resultMu, resultTyped⟩

end Goose.Lower.Validation
