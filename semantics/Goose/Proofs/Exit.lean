import Goose.Construct.Exit
import Goose.Construct.Eval
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


def runtimeScopeRoots (activation : RuntimeActivation) (scope : Nat) (scopeInst : ScopeInst) : List RootInst :=
  (activation.vars.toList.zipIdx).filterMap fun (localVar, index) =>
    if localVar.scope == scope then some (.local activation.act scopeInst index) else none

theorem runtime_select_nearest (target : NonlocalTarget) (stack : List RuntimeActivation)
    (catcher : RuntimeActivation) (found : selectTarget? target stack = some catcher) :
    ∃ discarded outer, stack = discarded ++ catcher :: outer ∧
      target.contains catcher.implementation = true ∧
      ∀ activation ∈ discarded, target.contains activation.implementation = false := by
  induction stack with
  | nil => simp [selectTarget?] at found
  | cons activation rest ih =>
      simp only [selectTarget?, List.find?_cons] at found
      split at found
      · cases found
        exact ⟨[], rest, rfl, by assumption, by simp⟩
      · rename_i excluded
        obtain ⟨discarded, outer, shape, member, earlier⟩ := ih found
        refine ⟨activation :: discarded, outer, by simp [shape], member, ?_⟩
        intro frame inDiscarded
        rcases List.mem_cons.mp inDiscarded with equal | inDiscarded
        · subst frame; exact excluded
        · exact earlier frame inDiscarded

theorem runtime_release_scope_members (activation : RuntimeActivation) (scope : Nat)
    (scopeInst : ScopeInst) (state : ExecutionState) (entry : RootInst × Value) :
    entry ∈ (releaseScopeState activation scope scopeInst state).objects ↔
      entry ∈ state.objects ∧ (runtimeScopeRoots activation scope scopeInst).contains entry.1 = false := by
  simp [releaseScopeState, runtimeScopeRoots, List.mem_filter]

theorem runtime_release_scope_outside (activation : RuntimeActivation) (scope : Nat)
    (scopeInst : ScopeInst) (state : ExecutionState) (entry : RootInst × Value)
    (outside : (runtimeScopeRoots activation scope scopeInst).contains entry.1 = false) :
    entry ∈ (releaseScopeState activation scope scopeInst state).objects ↔ entry ∈ state.objects := by
  rw [runtime_release_scope_members]
  constructor
  · exact And.left
  · intro member; exact ⟨member, outside⟩

theorem runtime_release_scope_construction (activation : RuntimeActivation) (scope : Nat)
    (scopeInst : ScopeInst) (state : ExecutionState) :
    (releaseScopeState activation scope scopeInst state).construction = state.construction := rfl

theorem runtime_release_scope_stdout (activation : RuntimeActivation) (scope : Nat)
    (scopeInst : ScopeInst) (state : ExecutionState) :
    (releaseScopeState activation scope scopeInst state).construction.stdout = state.construction.stdout := rfl


def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

theorem runtime_lift_frames_objects (origin : OriginId) (action : ConstructionM α) (state : ExecutionState) :
    (stepState (liftConstruction origin action state)).objects = state.objects := by
  unfold liftConstruction
  cases action state.construction <;> rfl

theorem runtime_protected_cleanup_storage (origin : OriginId) (state : ExecutionState)
    (id replacementId : DestinationId) :
    (stepState (liftConstruction origin (abandonPreservingExit id replacementId) state)).construction.storage =
      state.construction.storage := by
  have preserved := abandonPreservingExit_storage state.construction id replacementId
  unfold liftConstruction
  cases result : abandonPreservingExit id replacementId state.construction <;>
    simpa [result, ConstructionResult.finalState, stepState] using preserved

theorem runtime_protected_cleanup_stdout (origin : OriginId) (state : ExecutionState)
    (id replacementId : DestinationId) :
    (stepState (liftConstruction origin (abandonPreservingExit id replacementId) state)).construction.stdout =
      state.construction.stdout := by
  have preserved := abandonPreservingExit_stdout state.construction id replacementId
  unfold liftConstruction
  cases result : abandonPreservingExit id replacementId state.construction <;>
    simpa [result, ConstructionResult.finalState, stepState] using preserved

def runtimeReleaseScopes (scopes : List (RuntimeActivation × Nat × ScopeInst))
    (state : ExecutionState) : ExecutionState :=
  scopes.foldl (fun current (activation,scope,scopeInst) => releaseScopeState activation scope scopeInst current) state

theorem runtime_unwind_construction (scopes : List (RuntimeActivation × Nat × ScopeInst)) (state : ExecutionState) :
    (runtimeReleaseScopes scopes state).construction = state.construction := by
  induction scopes generalizing state with
  | nil => rfl
  | cons scope rest ih =>
      simpa [runtimeReleaseScopes, List.foldl_cons, releaseScopeState] using
        ih (releaseScopeState scope.1 scope.2.1 scope.2.2 state)

theorem runtime_unwind_outside (scopes : List (RuntimeActivation × Nat × ScopeInst))
    (state : ExecutionState) (entry : RootInst × Value)
    (outside : ∀ scope ∈ scopes, (runtimeScopeRoots scope.1 scope.2.1 scope.2.2).contains entry.1 = false) :
    entry ∈ (runtimeReleaseScopes scopes state).objects ↔ entry ∈ state.objects := by
  induction scopes generalizing state with
  | nil => rfl
  | cons scope rest ih =>
      change entry ∈ (runtimeReleaseScopes rest (releaseScopeState scope.1 scope.2.1 scope.2.2 state)).objects ↔
        entry ∈ state.objects
      rw [show entry ∈ (runtimeReleaseScopes rest (releaseScopeState scope.1 scope.2.1 scope.2.2 state)).objects ↔
        entry ∈ (releaseScopeState scope.1 scope.2.1 scope.2.2 state).objects from
        ih _ (fun s hs => outside s (by simp [hs]))]
      exact runtime_release_scope_outside scope.1 scope.2.1 scope.2.2 state entry (outside scope (by simp))


theorem runtime_with_scope_escape (activation : RuntimeActivation) (scope scopeInst : Nat)
    (action : EvalM α) (state afterOperands : ExecutionState) (target : ActId) (carriers : List Goose.Construct.Carrier)
    (escaped : action state = .escape target carriers afterOperands) :
    withScope activation scope scopeInst action state =
      .escape target carriers (releaseScopeState activation scope scopeInst afterOperands) := by
  simp [withScope, escaped, Goose.Construct.releaseScope, EvalM.get, EvalM.set, bind]

def runtimeWithScopes : List (RuntimeActivation × Nat × ScopeInst) → EvalM α → EvalM α
  | [], action => action
  | (activation,scope,scopeInst) :: rest, action =>
      runtimeWithScopes rest (withScope activation scope scopeInst action)

theorem runtime_with_scopes_escape (scopes : List (RuntimeActivation × Nat × ScopeInst))
    (action : EvalM α) (state afterOperands : ExecutionState) (target : ActId) (carriers : List Goose.Construct.Carrier)
    (escaped : action state = .escape target carriers afterOperands) :
    runtimeWithScopes scopes action state =
      .escape target carriers (runtimeReleaseScopes scopes afterOperands) := by
  induction scopes generalizing action afterOperands with
  | nil => exact escaped
  | cons scope rest ih =>
      simp only [runtimeWithScopes]
      exact ih (withScope scope.1 scope.2.1 scope.2.2 action)
        (releaseScopeState scope.1 scope.2.1 scope.2.2 afterOperands)
        (runtime_with_scope_escape scope.1 scope.2.1 scope.2.2 action state afterOperands target carriers escaped)


theorem runtime_unwind_subset (scopes : List (RuntimeActivation × Nat × ScopeInst))
    (state : ExecutionState) (entry : RootInst × Value) :
    entry ∈ (runtimeReleaseScopes scopes state).objects → entry ∈ state.objects := by
  induction scopes generalizing state with
  | nil => exact id
  | cons scope rest ih =>
      intro member
      have retained := ih (releaseScopeState scope.1 scope.2.1 scope.2.2 state) member
      exact (runtime_release_scope_members scope.1 scope.2.1 scope.2.2 state entry).mp retained |>.1

theorem runtime_unwind_removes (scopes : List (RuntimeActivation × Nat × ScopeInst))
    (state : ExecutionState) (entry : RootInst × Value)
    (owned : ∃ scope ∈ scopes, (runtimeScopeRoots scope.1 scope.2.1 scope.2.2).contains entry.1 = true) :
    entry ∉ (runtimeReleaseScopes scopes state).objects := by
  induction scopes generalizing state with
  | nil => simp at owned
  | cons scope rest ih =>
      obtain ⟨owner, member, owns⟩ := owned
      rcases List.mem_cons.mp member with same | member
      · subst owner
        intro retained
        have inReleased := runtime_unwind_subset rest
          (releaseScopeState scope.1 scope.2.1 scope.2.2 state) entry retained
        have notOwned := (runtime_release_scope_members scope.1 scope.2.1 scope.2.2 state entry).mp inReleased |>.2
        have impossible : false = true := notOwned.symm.trans owns
        cases impossible
      · exact ih (releaseScopeState scope.1 scope.2.1 scope.2.2 state) ⟨owner,member,owns⟩


theorem runtime_activation_propagates (layout : LayoutEnv) (activation : RuntimeActivation)
    (resultTypes : List Goose.Construct.Ty) (origin : OriginId) (action : EvalM (List Goose.Construct.Carrier))
    (state afterOperands : ExecutionState) (target : ActId) (carriers : List Goose.Construct.Carrier)
    (escaped : action state = .escape target carriers afterOperands) (other : target ≠ activation.act) :
    finishActivation layout activation resultTypes origin action state =
      .escape target carriers { afterOperands with
        activations := afterOperands.activations.filter (fun current => current.act != activation.act) } := by
  simp [finishActivation, escaped, other]

theorem runtime_activation_catches (layout : LayoutEnv) (activation : RuntimeActivation)
    (resultTypes : List Goose.Construct.Ty) (origin : OriginId) (action : EvalM (List Goose.Construct.Carrier))
    (state afterOperands landed : ExecutionState) (carriers : List Goose.Construct.Carrier)
    (escaped : action state = .escape activation.act carriers afterOperands)
    (completed : finishChannels layout resultTypes carriers origin { afterOperands with
      activations := afterOperands.activations.filter (fun current => current.act != activation.act) } = .ok () landed) :
    finishActivation layout activation resultTypes origin action state = .ok carriers landed := by
  simp [finishActivation, escaped, completed]


def runtimeDropActivations (discarded : List RuntimeActivation) (state : ExecutionState) : ExecutionState :=
  discarded.foldl (fun current activation => { current with
    activations := current.activations.filter (fun active => active.act != activation.act) }) state

def runtimeDiscardHandlers (layout : LayoutEnv) (results : ImplId → List Goose.Construct.Ty)
    (origin : OriginId) : List RuntimeActivation → EvalM (List Goose.Construct.Carrier) → EvalM (List Goose.Construct.Carrier)
  | [], action => action
  | activation :: rest, action =>
      runtimeDiscardHandlers layout results origin rest
        (finishActivation layout activation (results activation.implementation) origin action)

theorem runtime_discard_handlers_escape (layout : LayoutEnv) (results : ImplId → List Goose.Construct.Ty)
    (origin : OriginId) (discarded : List RuntimeActivation)
    (action : EvalM (List Goose.Construct.Carrier)) (state afterOperands : ExecutionState)
    (target : ActId) (carriers : List Goose.Construct.Carrier)
    (escaped : action state = .escape target carriers afterOperands)
    (other : ∀ activation ∈ discarded, target ≠ activation.act) :
    runtimeDiscardHandlers layout results origin discarded action state =
      .escape target carriers (runtimeDropActivations discarded afterOperands) := by
  induction discarded generalizing action afterOperands with
  | nil => exact escaped
  | cons activation rest ih =>
      apply ih _ _
      · exact runtime_activation_propagates layout activation (results activation.implementation) origin action
          state afterOperands target carriers escaped (other activation (by simp))
      · intro frame member; exact other frame (by simp [member])

theorem runtime_nearest_activation_dispatch (layout : LayoutEnv) (results : ImplId → List Goose.Construct.Ty)
    (origin : OriginId) (target : NonlocalTarget) (stack : List RuntimeActivation) (catcher : RuntimeActivation)
    (distinct : (stack.map (·.act)).Nodup) (selected : selectTarget? target stack = some catcher)
    (action : EvalM (List Goose.Construct.Carrier)) (state afterOperands : ExecutionState)
    (carriers : List Goose.Construct.Carrier) (escaped : action state = .escape catcher.act carriers afterOperands) :
    ∃ discarded outer, stack = discarded ++ catcher :: outer ∧
      target.contains catcher.implementation = true ∧
      (∀ activation ∈ discarded, target.contains activation.implementation = false) ∧
      finishActivation layout catcher (results catcher.implementation) origin
        (runtimeDiscardHandlers layout results origin discarded action) state =
      finishActivation layout catcher (results catcher.implementation) origin
        (fun _ => .escape catcher.act carriers (runtimeDropActivations discarded afterOperands)) state := by
  obtain ⟨discarded, outer, shape, member, excluded⟩ := runtime_select_nearest target stack catcher selected
  have different : ∀ activation ∈ discarded, catcher.act ≠ activation.act := by
    intro activation inDiscarded
    have separated : (discarded.map (·.act) ++ (catcher :: outer).map (·.act)).Nodup := by
      simpa [shape] using distinct
    exact ((List.nodup_append.mp separated).2.2 activation.act (List.mem_map.mpr ⟨activation,inDiscarded,rfl⟩)
      catcher.act (by simp)).symm
  refine ⟨discarded, outer, shape, member, excluded, ?_⟩
  have forwarded := runtime_discard_handlers_escape layout results origin discarded action state afterOperands
    catcher.act carriers escaped different
  simp only [finishActivation, forwarded]


theorem runtime_nearest_scope_dispatch (layout : LayoutEnv)
    (results : ImplId → List Goose.Construct.Ty) (origin : OriginId)
    (target : NonlocalTarget) (stack : List RuntimeActivation) (catcher : RuntimeActivation)
    (distinct : (stack.map (·.act)).Nodup) (selected : selectTarget? target stack = some catcher)
    (scopes : List (RuntimeActivation × Nat × ScopeInst))
    (action : EvalM (List Goose.Construct.Carrier)) (state afterOperands : ExecutionState)
    (carriers : List Goose.Construct.Carrier)
    (escaped : action state = .escape catcher.act carriers afterOperands) :
    ∃ discarded outer, stack = discarded ++ catcher :: outer ∧
      target.contains catcher.implementation = true ∧
      (∀ activation ∈ discarded, target.contains activation.implementation = false) ∧
      finishActivation layout catcher (results catcher.implementation) origin
        (runtimeDiscardHandlers layout results origin discarded (runtimeWithScopes scopes action)) state =
      finishActivation layout catcher (results catcher.implementation) origin
        (fun _ => .escape catcher.act carriers
          (runtimeDropActivations discarded (runtimeReleaseScopes scopes afterOperands))) state ∧
      (runtimeReleaseScopes scopes afterOperands).construction = afterOperands.construction ∧
      (∀ entry : RootInst × Value,
        (∀ scope ∈ scopes, (runtimeScopeRoots scope.1 scope.2.1 scope.2.2).contains entry.1 = false) →
        (entry ∈ (runtimeReleaseScopes scopes afterOperands).objects ↔ entry ∈ afterOperands.objects)) ∧
      (∀ entry : RootInst × Value,
        (∃ scope ∈ scopes, (runtimeScopeRoots scope.1 scope.2.1 scope.2.2).contains entry.1 = true) →
        entry ∉ (runtimeReleaseScopes scopes afterOperands).objects) := by
  have unwound := runtime_with_scopes_escape scopes action state afterOperands catcher.act carriers escaped
  obtain ⟨discarded, outer, shape, member, excluded, dispatched⟩ :=
    runtime_nearest_activation_dispatch layout results origin target stack catcher distinct selected
      (runtimeWithScopes scopes action) state (runtimeReleaseScopes scopes afterOperands) carriers unwound
  exact ⟨discarded,outer,shape,member,excluded,dispatched,
    runtime_unwind_construction scopes afterOperands,
    fun entry outside => runtime_unwind_outside scopes afterOperands entry outside,
    fun entry owned => runtime_unwind_removes scopes afterOperands entry owned⟩


theorem target_activation_success (config : EvalConfig) (targetId : Nat) (target : NonlocalTarget)
    (activation : RuntimeActivation) (state : ExecutionState)
    (present : config.module.targets[targetId]? = some target)
    (selected : selectTarget? target state.activations = some activation) :
    targetActivation config targetId state = .ok activation state := by
  simp [targetActivation, present, selected, EvalM.get, bind, pure]

theorem return_from_after_operands (fuel : Nat) (config : EvalConfig)
    (environment activation : RuntimeActivation) (targetId : Nat) (target : NonlocalTarget)
    (operands : List Goose.Construct.Expr) (origin : OriginId) (channels : List Channel) (carriers : List Goose.Construct.Carrier)
    (state prepared afterOperands : ExecutionState)
    (present : config.module.targets[targetId]? = some target)
    (selected : selectTarget? target state.activations = some activation)
    (preparedChannels : exitChannels activation operands origin state = .ok channels prepared)
    (evaluated : evalOperands fuel config environment channels operands prepared = .ok carriers afterOperands) :
    Goose.Construct.execStmt (fuel + 1) config environment (.returnFrom targetId operands origin) state =
      .escape activation.act carriers afterOperands := by
  simp [Goose.Construct.execStmt, target_activation_success config targetId target activation state present selected,
    preparedChannels, evaluated, returned, bind]

theorem return_from_nearest_scope_dispatch (fuel : Nat) (config : EvalConfig)
    (environment catcher : RuntimeActivation) (targetId : Nat) (target : NonlocalTarget)
    (results : ImplId → List Goose.Construct.Ty) (operands : List Goose.Construct.Expr) (origin : OriginId)
    (channels : List Channel) (carriers : List Goose.Construct.Carrier)
    (state prepared afterOperands : ExecutionState) (scopes : List (RuntimeActivation × Nat × ScopeInst))
    (present : config.module.targets[targetId]? = some target)
    (selected : selectTarget? target state.activations = some catcher)
    (distinct : (state.activations.map (·.act)).Nodup)
    (preparedChannels : exitChannels catcher operands origin state = .ok channels prepared)
    (evaluated : evalOperands fuel config environment channels operands prepared = .ok carriers afterOperands) :
    ∃ discarded outer, state.activations = discarded ++ catcher :: outer ∧
      target.contains catcher.implementation = true ∧
      (∀ activation ∈ discarded, target.contains activation.implementation = false) ∧
      finishActivation config.layout catcher (results catcher.implementation) origin
        (runtimeDiscardHandlers config.layout results origin discarded
          (runtimeWithScopes scopes (Goose.Construct.execStmt (fuel + 1) config environment (.returnFrom targetId operands origin) >>= fun _ => pure []))) state =
      finishActivation config.layout catcher (results catcher.implementation) origin
        (fun _ => .escape catcher.act carriers
          (runtimeDropActivations discarded (runtimeReleaseScopes scopes afterOperands))) state := by
  have returned := return_from_after_operands fuel config environment catcher targetId target operands origin
    channels carriers state prepared afterOperands present selected preparedChannels evaluated
  obtain ⟨discarded,outer,shape,member,excluded,dispatched,_,_,_⟩ :=
    runtime_nearest_scope_dispatch config.layout results origin target state.activations catcher distinct selected
      scopes (Goose.Construct.execStmt (fuel + 1) config environment (.returnFrom targetId operands origin) >>= fun _ => pure [])
      state afterOperands carriers (by simp [returned, bind])
  exact ⟨discarded,outer,shape,member,excluded,dispatched⟩

end Goose.Proofs.Exit
