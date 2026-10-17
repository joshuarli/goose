import Goose.Core.Typing

namespace Goose.Lower.Validation

open Goose.Core

def CoreNoReturnLE (left right : ContextId → Bool) : Prop :=
  ∀ callee, left callee = true → right callee = true

mutual

theorem core_stmt_stops_mono {left right : ContextId → Bool} (order : CoreNoReturnLE left right)
    (stmt : Stmt) (stopped : stmt.stops left = true) : stmt.stops right = true := by
  cases stmt <;> try first | exact stopped | contradiction
  case expr expression origin =>
    cases expression <;> first | exact order _ stopped | contradiction
  case ifS condition yes no origin =>
    cases no with
    | none => contradiction
    | some no =>
      have both := Bool.and_eq_true_iff.mp stopped
      exact Bool.and_eq_true_iff.mpr ⟨core_block_stops_mono order yes both.1,
        core_block_stops_mono order no both.2⟩

theorem core_block_stops_mono {left right : ContextId → Bool} (order : CoreNoReturnLE left right)
    (block : Block) (stopped : block.stops left = true) : block.stops right = true := by
  cases block with
  | mk scope stmts value => exact core_stmts_stops_mono order stmts stopped

theorem core_stmts_stops_mono {left right : ContextId → Bool} (order : CoreNoReturnLE left right)
    (stmts : List Stmt) (stopped : stmtsStop left stmts = true) : stmtsStop right stmts = true := by
  cases stmts with
  | nil => contradiction
  | cons stmt rest =>
    simp only [stmtsStop, Bool.or_eq_true, Bool.and_eq_true] at stopped ⊢
    rcases stopped with first | ⟨plain, later⟩
    · exact Or.inl (core_stmt_stops_mono order stmt first)
    · exact Or.inr ⟨plain, core_stmts_stops_mono order rest later⟩

end

theorem core_neverReturns_step (module : Module) (round : Nat) :
    CoreNoReturnLE (neverReturns module round) (neverReturns module (round + 1)) := by
  induction round with
  | zero => intro callee stopped; contradiction
  | succ round ih =>
    intro callee stopped
    simp only [neverReturns] at stopped ⊢
    cases contextRow : module.contexts[callee]? with
    | none => simp [contextRow] at stopped
    | some context =>
      simp only [contextRow] at stopped ⊢
      cases implementation : module.impls[context.impl]? with
      | none => simp [implementation] at stopped
      | some impl =>
        simp only [implementation] at stopped ⊢
        exact core_block_stops_mono ih impl.body stopped

theorem core_neverReturns_mono (module : Module) {first last : Nat} (rounds : first ≤ last) :
    CoreNoReturnLE (neverReturns module first) (neverReturns module last) := by
  induction rounds with
  | refl => intro callee stopped; exact stopped
  | @step next rounds ih =>
    intro callee stopped
    exact core_neverReturns_step module next callee (ih callee stopped)

theorem core_noReturn_body_stops (module : Module) (callee : ContextId)
    (stopped : module.noReturn callee = true) :
    ∃ context impl, module.contexts[callee]? = some context ∧ module.impls[context.impl]? = some impl ∧
      impl.body.stops module.noReturn = true := by
  unfold Module.noReturn at stopped
  cases rounds : module.contexts.size with
  | zero => simp [rounds, neverReturns] at stopped
  | succ previous =>
    rw [rounds, neverReturns] at stopped
    cases context : module.contexts[callee]? with
    | none => simp [context] at stopped
    | some ctx =>
      simp only [context] at stopped
      cases implementation : module.impls[ctx.impl]? with
      | none => simp [implementation] at stopped
      | some impl =>
        simp only [implementation] at stopped
        refine ⟨ctx, impl, rfl, implementation, ?_⟩
        exact core_block_stops_mono (core_neverReturns_mono module (by omega)) impl.body stopped

theorem core_noReturn_bounded (module : Module) (callee : ContextId)
    (stopped : module.noReturn callee = true) : callee < module.contexts.size := by
  obtain ⟨context, impl, row, _, _⟩ := core_noReturn_body_stops module callee stopped
  exact (Array.getElem?_eq_some_iff.mp row).1

end Goose.Lower.Validation
