import Goose.Proofs.Core

namespace Goose.Core.WellFormedChecks
open Goose.Core.Declarative

private def wrongStoreImpl : Impl := {
  name := "wrongStore"
  params := #[]
  results := #[]
  vars := #[⟨"number", .int .i64, .mutable, 0, 0⟩]
  body := .mk 0 [.letS 0 (.lit .i64 1) 0, .assign (.var 0) (.bool true) 0] none
  summary := .unknown }

private def wrongStoreModule : Module := {
  files := #["wrong_store.goose"]
  types := #[]
  globals := #[]
  impls := #[wrongStoreImpl]
  contexts := #[⟨0, "wrongStore", [], [], []⟩]
  entry := 0
  origins := #[⟨0, 1, "assign"⟩] }

theorem mistyped_store_has_no_derivation (type : Ty) (after : Nat) :
    ¬ BlockTyping (Sound.implEnv wrongStoreModule wrongStoreImpl) [] wrongStoreImpl.body 0 type after := by
  intro derivation
  have accepted := (blockTyping_iff _ _ _ _ _ _).mp derivation
  have rejected : tyBlock (Sound.implEnv wrongStoreModule wrongStoreImpl) []
      wrongStoreImpl.body 0 =
        .error ⟨.type, "assigned value of another type than the place"⟩ := by rfl
  rw [rejected] at accepted
  cases accepted

#guard match validate wrongStoreModule with
  | .error rejection => rejection.rule == .type
  | .ok _ => false

theorem mistyped_store_not_wellFormed : ¬ WellFormed wrongStoreModule := by
  intro wellFormed
  obtain ⟨type, after, derivation, _⟩ :=
    (wellFormed.implementationTyping 0 wrongStoreImpl (by rfl)).body
  exact mistyped_store_has_no_derivation type after derivation

private def forgedImpl : Impl :=
  ⟨"forged", #[], #[],
    #[⟨"owner", .int .i64, .mutable, 0, 0⟩,
      ⟨"reference", .ref .mutable (.int .i64), .mutable, 0, 0⟩],
    .mk 0 [.letS 0 (.lit .i64 1) 0,
      .letS 1 (.ref .mutable (.var 0)) 0] none, .unknown⟩
private def forgedContext : Context := ⟨0, "forged", [(1, [.local 1])], [], []⟩
private def forgedModule : Module := {
  files := #["forged.goose"], types := #[], globals := #[],
  impls := #[forgedImpl], contexts := #[forgedContext], entry := 0,
  origins := #[⟨0, 1, "let"⟩] }

#guard (checkImpl forgedModule forgedImpl).isOk
#guard match checkContext forgedModule forgedContext with
  | .error rejection => rejection.rule == .root
  | .ok _ => false

theorem forged_roots_not_wellFormed : ¬ WellFormed forgedModule := by
  intro wellFormed
  obtain ⟨impl, lookup, roots⟩ := wellFormed.contextRoots 0 forgedContext (by rfl)
  have same : impl = forgedImpl := by simpa [forgedModule, forgedContext] using lookup.symm
  subst impl
  obtain ⟨lv, _, _, declared⟩ := roots.annotations.1 1 [.local 1] (by simp [forgedContext])
  have forged := declared (.local 1) (by simp)
  simp [RootDeclared, forgedImpl, Ty.isRefLike] at forged

private def clearSummary (shrinks : List Target) : Summary :=
  ⟨[.global 0], [], [], shrinks, [], false, false⟩
private def clearImpl (shrinks : List Target) : Impl := {
  name := "clear", params := #[], results := #[], vars := #[],
  body := .mk 0 [.clear (.global 0) 0] none,
  summary := .known (clearSummary shrinks) }
private def clearModule (shrinks : List Target) : Module := {
  files := #["clear.goose"], types := #[],
  globals := #[⟨"owner", .growshrink (.int .i64), .mutable,
    .arrLit (.growshrink (.int .i64)) [.lit .i64 1], 0⟩],
  impls := #[clearImpl shrinks], contexts := #[⟨0, "clear", [], [], []⟩],
  entry := 0, origins := #[⟨0, 1, "let"⟩], profile := .shrink }

theorem omitted_shrink_not_wellFormed : ¬ WellFormed (clearModule []) := by
  intro wellFormed
  obtain ⟨impl, lookup, roots⟩ := wellFormed.contextRoots 0 ⟨0, "clear", [], [], []⟩ (by rfl)
  have same : impl = clearImpl [] := by simpa [clearModule] using lookup.symm
  subst impl
  obtain ⟨rho, range, after, traversal, _, summary⟩ := roots.body
  have effects : after.eff.shrinks = [.global 0] := by
    simp [clearImpl, RootBlockValue, RootStmts, RootStmt, RootPlace,
      rootReads, rootShrinks, requireRoot, bind, pure, get, getThe, MonadStateOf.get, modify, modifyGet, MonadStateOf.modifyGet,
      addTargets, rootsTargets, BlockRoots] at traversal
    rcases traversal with ⟨s0, v0, ⟨rfl, rfl⟩, s2,
      ⟨s1, r1, ⟨rfl, rfl⟩, rfl⟩, s3, r2, ⟨rfl, rfl⟩,
      s4, v4, ⟨rfl, rfl⟩, ⟨_, rfl⟩, _, _⟩
    rfl
  obtain ⟨_, _, _, _, _, shrinks, _, _, _⟩ := summary (clearSummary []) rfl
  have missing := shrinks (.global 0) (by rw [effects]; simp)
  simp [expandTargets, clearSummary] at missing

#guard match validate (clearModule []) with
  | .error rejection => rejection.rule == .summary
  | .ok _ => false

#guard (validate (clearModule [.global 0])).isOk

private def pilotModule : Module := {
  files := #[], types := #[], globals := #[],
  impls := #[⟨"pilot", #[], #[], #[], .mk 0 [] none, .unknown⟩],
  contexts := #[⟨0, "pilot", [], [], []⟩], entry := 0, origins := #[] }

#guard (validate pilotModule).isOk

#print axioms Goose.Proofs.Core.validate_wellFormed
#print axioms mistyped_store_not_wellFormed
#print axioms forged_roots_not_wellFormed
#print axioms omitted_shrink_not_wellFormed

end Goose.Core.WellFormedChecks
