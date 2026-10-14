import Goose.Construct.Exit
import Goose.Proofs.Memory

namespace Goose.Proofs.Exit
open Goose.Core Goose.Construct Goose.Proofs.Memory

theorem plan_nearest (target : NonlocalTarget) (stack : List Activation)
    (plan : ExitPlan) (found : planExit? target stack = some plan) :
    stack = plan.discarded ++ plan.catcher :: plan.outer ∧
    target.contains plan.catcher.implementation = true ∧
    ∀ activation ∈ plan.discarded, target.contains activation.implementation = false := by
  induction stack generalizing plan with
  | nil => simp [planExit?] at found
  | cons activation outer ih =>
      simp only [planExit?] at found
      split at found
      · cases found
        exact ⟨rfl, by assumption, by simp⟩
      · rename_i notMember
        cases next : planExit? target outer with
        | none => simp [next] at found
        | some tail =>
          simp only [next, Option.map_some, Option.some.injEq] at found
          subst plan
          obtain ⟨shape, catcher, excluded⟩ := ih tail next
          refine ⟨by simp [shape], catcher, ?_⟩
          intro frame member
          rcases List.mem_cons.mp member with equal | member
          · subst frame
            exact Bool.eq_false_iff.mpr notMember
          · exact excluded frame member

def ActivationRoots (activation : Activation) (root : RootInst) : Prop :=
  ∃ scope scopeInst, (scope, scopeInst) ∈ activation.scopes ∧
    ScopeRoots activation.vars activation.act scope scopeInst root

theorem releaseActivation_frame (activation : Activation) (store : Store)
    (root : RootInst) (outside : ¬ ActivationRoots activation root) :
    (releaseActivation activation store).roots[root]? = store.roots[root]? := by
  unfold releaseActivation
  have frame : ∀ scopes : List (Nat × ScopeInst),
      (∀ pair ∈ scopes, pair ∈ activation.scopes) →
      ∀ store : Store,
        (scopes.foldl (fun current (scope, scopeInst) =>
          releaseVars activation.vars activation.act scope scopeInst activation.vars.size current)
          store).roots[root]? = store.roots[root]? := by
    intro scopes
    induction scopes with
    | nil => intro _ _; rfl
    | cons pair rest ih =>
        intro included current
        rw [List.foldl_cons]
        rw [ih (fun p hp => included p (by simp [hp]))]
        apply (releaseScope_roots activation.vars activation.act pair.1 pair.2 current).1
        intro owned
        exact outside ⟨pair.1, pair.2, included pair (by simp), owned⟩
  exact frame activation.scopes (fun _ h => h) store

theorem unwind_frame (plan : ExitPlan) (store : Store) (root : RootInst)
    (outside : ¬ ActivationRoots plan.catcher root)
    (intermediate : ∀ activation ∈ plan.discarded, ¬ ActivationRoots activation root) :
    (unwindStore plan store).roots[root]? = store.roots[root]? := by
  unfold unwindStore
  rw [releaseActivation_frame plan.catcher _ root outside]
  have frame : ∀ stack : List Activation,
      (∀ activation ∈ stack, ¬ ActivationRoots activation root) →
      ∀ store : Store,
        (stack.foldl (fun current activation => releaseActivation activation current)
          store).roots[root]? = store.roots[root]? := by
    intro stack
    induction stack with
    | nil => intro _ _; rfl
    | cons activation rest ih =>
        intro excluded current
        rw [List.foldl_cons, ih (fun a ha => excluded a (by simp [ha]))]
        exact releaseActivation_frame activation current root (excluded activation (by simp))
  exact frame plan.discarded intermediate store

theorem releaseActivation_absent (activation : Activation) (store : Store) (root : RootInst)
    (absent : store.roots[root]? = none) :
    (releaseActivation activation store).roots[root]? = none := by
  unfold releaseActivation
  have preserved : ∀ scopes : List (Nat × ScopeInst), ∀ store : Store,
      store.roots[root]? = none →
      (scopes.foldl (fun current (scope, scopeInst) =>
        releaseVars activation.vars activation.act scope scopeInst activation.vars.size current)
        store).roots[root]? = none := by
    intro scopes
    induction scopes with
    | nil => intro _ absent; exact absent
    | cons pair rest ih =>
        intro current absent
        rw [List.foldl_cons]
        apply ih
        rw [releaseVars_roots]
        split
        · rfl
        · exact absent
  exact preserved activation.scopes store absent

theorem releaseActivation_removed (activation : Activation) (store : Store) (root : RootInst)
    (owned : ActivationRoots activation root) :
    (releaseActivation activation store).roots[root]? = none := by
  have absent : ∀ scopes : List (Nat × ScopeInst), ∀ store : Store,
      store.roots[root]? = none →
      (scopes.foldl (fun current (scope, scopeInst) =>
        releaseVars activation.vars activation.act scope scopeInst activation.vars.size current)
        store).roots[root]? = none := by
    intro scopes current missing
    exact releaseActivation_absent { activation with scopes := scopes } current root missing
  have removed : ∀ scopes : List (Nat × ScopeInst),
      (∃ scope scopeInst, (scope, scopeInst) ∈ scopes ∧
        ScopeRoots activation.vars activation.act scope scopeInst root) →
      ∀ store : Store,
        (scopes.foldl (fun current (scope, scopeInst) =>
          releaseVars activation.vars activation.act scope scopeInst activation.vars.size current)
          store).roots[root]? = none := by
    intro scopes
    induction scopes with
    | nil => intro owned; simp at owned
    | cons pair rest ih =>
        rintro ⟨scope, scopeInst, member, owned⟩ current
        rw [List.foldl_cons]
        rcases List.mem_cons.mp member with same | member
        · cases same
          apply absent
          exact (releaseScope_roots activation.vars activation.act scope scopeInst current).2 root owned
        · exact ih ⟨scope, scopeInst, member, owned⟩ _
  exact removed activation.scopes owned store

theorem unwind_removes (plan : ExitPlan) (store : Store) (root : RootInst)
    (owned : ActivationRoots plan.catcher root ∨
      ∃ activation ∈ plan.discarded, ActivationRoots activation root) :
    (unwindStore plan store).roots[root]? = none := by
  unfold unwindStore
  rcases owned with catcher | intermediate
  · exact releaseActivation_removed plan.catcher _ root catcher
  · apply releaseActivation_absent
    have removed : ∀ stack : List Activation,
        (∃ activation ∈ stack, ActivationRoots activation root) →
        ∀ store : Store,
          (stack.foldl (fun current activation => releaseActivation activation current)
            store).roots[root]? = none := by
      intro stack
      induction stack with
      | nil => intro owned; simp at owned
      | cons activation rest ih =>
          rintro ⟨owner, member, owned⟩ current
          rw [List.foldl_cons]
          rcases List.mem_cons.mp member with same | member
          · subst owner
            have preserved : ∀ remaining : List Activation, ∀ store : Store,
                store.roots[root]? = none →
                (remaining.foldl (fun current activation => releaseActivation activation current)
                  store).roots[root]? = none := by
              intro remaining
              induction remaining with
              | nil => intro _ missing; exact missing
              | cons frame tail ih =>
                  intro state missing
                  rw [List.foldl_cons]
                  exact ih _ (releaseActivation_absent frame state root missing)
            exact preserved rest _ (releaseActivation_removed activation current root owned)
          · exact ih ⟨owner, member, owned⟩ _
    exact removed plan.discarded intermediate store

theorem unwind_preserves_output (plan : ExitPlan) (state : St) :
    (unwindState plan state).trace = state.trace := rfl

end Goose.Proofs.Exit
