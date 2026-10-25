import Goose.Lower.DemandSlotStorage

namespace Goose.Lower.DemandSlotStorageChecks

open Goose.Core Goose.GIR Goose.Core.Sound

private def holderType : Ty := .ref .mutable (.int .i64)
private def holder : Loc := ⟨.local 0 0 0, []⟩
private def removed : Loc := ⟨.local 99 9 0, []⟩
private def replacement : Loc := ⟨.global 1, []⟩
private def environment : Env := ⟨#[⟨"reference", holderType, .mutable, 0, 0⟩], 0, [(0, 0)], 0⟩
private def before : St :=
  ⟨(Store.empty.introduce holder.root (.ref removed)).introduce replacement.root (.int .i64 9), "", 1, 1⟩
private def frame : GIR.Frame :=
  ((⟨0, [(0, 0)], {}, 0⟩ : GIR.Frame).set 0 (.val (.ref holder))).set 1 (.val (.ref replacement))
private def function : Func :=
  { name := "rebind", params := [], results := [], slots := #[], scopes := #[], blocks := #[], summary := .unknown, org := none }
private def module : Core.Module :=
  { files := #[], types := #[], globals := #[], impls := #[], contexts := #[], entry := 0, origins := #[], profile := .shrink }
private def context : FnCtx := ⟨⟨.release, lower module⟩, function⟩

theorem raw_holder_storage : SlotStorageAt environment before.store frame 0 0 := by
  refine ⟨⟨"reference", holderType, .mutable, 0, 0⟩, 0, .ref removed, ?_, ?_, ?_, ?_⟩ <;> cbv

theorem holder_read_returns_stale_reference : execPure context frame (.load 0) before = .ok (.val (.ref removed)) before := by cbv

theorem old_pointee_read_fails : readLoc removed before = .stop (.fault .danglingRoot) before := by cbv

theorem raw_holder_has_no_reference_to_reference_alias (source : Core.Module) (world : World) (env : Env) :
    ¬ ValueAliasAt source world env before.store frame 0 ⟨.ref .mutable holderType, [], .operand []⟩ := by
  rintro ⟨value, cell, typed, rooted⟩
  simp only [holderType, HasTy, Ty.refTarget, Ty.isSlice, Bool.false_eq_true, false_and, or_self] at typed
  obtain ⟨location, _, impossible⟩ := typed
  exact impossible

theorem rebind_replaces_stale_reference :
    ∃ after, execEff function frame (.store 0 1 (some 0)) before = .ok frame after ∧
      SlotStorageAt environment after.store frame 0 0 ∧
      execPure context frame (.load 0) after = .ok (.val (.ref replacement)) after := by
  obtain ⟨after, written, storage, binding, scope, variableAt, scopeAt, valueAt⟩ :=
    raw_holder_storage.store (value := 1) (new := .ref replacement) (by cbv) function (some 0)
  refine ⟨after, written, storage, ?_⟩
  have bindingEq : binding = ⟨"reference", holderType, .mutable, 0, 0⟩ := Option.some.inj (by simpa [environment] using variableAt.symm)
  subst binding
  have scopeEq : scope = 0 := Option.some.inj (by simpa [environment] using scopeAt.symm)
  subst scope
  have read : readLoc holder after = .ok (.ref replacement) after := by
    have rootAt : after.store.roots[holder.root]? = some (.ref replacement) := valueAt
    dsimp only [holder] at rootAt
    simp [readLoc, Store.read, holder, Val.get?, rootAt]
  simp only [execPure, getVal_of (show frame.vals[0]? = some (.val (.ref holder)) by cbv), pure_bind, expectRef]
  simp [bind_apply, pure_apply, read]

private def sourceModule (readOld : Bool) : Core.Module :=
  let owner : Ty := .growshrink (.int .i64)
  let use : Expr := .read (.deref (.read (.var 0)))
  let body : Core.Block := .mk 0
    ([.letS 0 (.ref .mutable (.elem (.of (.global 0)) (.lit .i64 0) 0)) 0,
      .clear (.global 0) 0] ++
      (if readOld then [.expr use 0] else []) ++
      [.rebind 0 (.ref .mutable (.global 1)) 0]) none
  { files := #["holder.goose"], types := #[],
    globals := #[⟨"owner", owner, .mutable, .arrLit owner [.lit .i64 7], 0⟩,
      ⟨"replacement", .int .i64, .mutable, .lit .i64 9, 0⟩],
    impls := #[{ name := "main", params := #[], results := #[], vars := environment.vars, body := body, summary := .unknown }],
    contexts := #[⟨0, "main", [(0, [.global 0, .global 1])], [], []⟩], entry := 0, origins := #[⟨0, 1, "expr"⟩], profile := .shrink }

#guard match Core.validate (sourceModule false) with
  | .ok () => true
  | .error _ => false

#guard match Core.validate (sourceModule true) with
  | .error rejection => rejection.rule == .shrink
  | .ok () => false

end Goose.Lower.DemandSlotStorageChecks
