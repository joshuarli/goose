import Goose.Core.Sound.StepAux
import Goose.Core.Sound.AccessTyping
import Goose.Core.Sound.AccessReplay

/-!
One step of the induction on fuel for calls: the call expression, which
evaluates its arguments and checks the callee context's assumptions, and
entering the callee's body.
-/

namespace Goose.Core.Sound
open Goose.Core Goose.Proofs.Memory

variable {m : Module} {prof : NumProfile} {n : Nat}

/-! ### Summary targets through a call -/

theorem mapCall_global (callee : Impl) (cctx : Context) (ars : List (List RootRef)) :
    ∀ (ds : List Target) (g : GlobalId), Target.global g ∈ ds →
      Target.global g ∈ mapCallTargets callee cctx ars ds
  | [], g, h => by cases h
  | .global g' :: rest, g, h => by
    simp only [mapCallTargets, List.mem_cons]
    rcases List.mem_cons.1 h with e | h
    · exact Or.inl e
    · exact Or.inr (mapCall_global callee cctx ars rest g h)
  | .param j :: rest, g, h => by
    simp only [mapCallTargets, List.mem_append]
    rcases List.mem_cons.1 h with e | h
    · cases e
    · exact Or.inr (mapCall_global callee cctx ars rest g h)

theorem mapCall_param (callee : Impl) (cctx : Context) (ars : List (List RootRef)) :
    ∀ (ds : List Target) (j : Nat), Target.param j ∈ ds → ∀ t,
      (t ∈ rootsTargets (ars[j]?.getD []) ∨ t ∈ paramGlobals callee cctx j) →
      t ∈ mapCallTargets callee cctx ars ds
  | [], j, h, _, _ => by cases h
  | .global g' :: rest, j, h, t, ht => by
    simp only [mapCallTargets, List.mem_cons]
    rcases List.mem_cons.1 h with e | h
    · cases e
    · exact Or.inr (mapCall_param callee cctx ars rest j h t ht)
  | .param j' :: rest, j, h, t, ht => by
    simp only [mapCallTargets, List.mem_append]
    rcases List.mem_cons.1 h with e | h
    · cases e
      exact Or.inl ht
    · exact Or.inr (mapCall_param callee cctx ars rest j h t ht)

/-- If every target a call charges to the caller is allowed there, every
target the callee's own check lets its summary stand for is allowed in the
callee. -/
theorem expand_ok {env : Env} {G : Nat} {P Pc : Nat → RootInst → Prop} {callee : Impl}
    {cctx : Context} {ars : List (List RootRef)}
    (hPc : ∀ j r, Pc j r → Gam env P (ars[j]?.getD []) r) (hctx : CtxOk m callee cctx)
    (ds : List Target) (hpar : ∀ j, Target.param j ∈ ds → j < callee.params.size)
    (hmap : ∀ t, t ∈ mapCallTargets callee cctx ars ds → TargetOk G P t) :
    ∀ t, t ∈ expandTargets callee cctx ds → TargetOk G Pc t := by
  intro t ht
  simp only [expandTargets, List.mem_flatMap] at ht
  obtain ⟨d, hd, ht⟩ := ht
  cases d with
  | global g =>
    simp only [List.mem_singleton] at ht
    subst ht
    exact hmap _ (mapCall_global callee cctx ars ds g hd)
  | param j =>
    have hpj : TargetOk G Pc (.param j) := by
      intro r hr g hrg
      obtain ⟨q, hq, hrq⟩ := hPc j r hr
      subst hrg
      cases q with
      | «local» y => obtain ⟨_, _, _, _, e⟩ := hrq; cases e
      | global g' =>
        have e : RootInst.global g = RootInst.global g' := hrq
        cases e
        exact hmap _ (mapCall_param callee cctx ars ds j hd _ (Or.inl (mem_rootsTargets_global hq)))
      | param k =>
        exact hmap _ (mapCall_param callee cctx ars ds j hd _ (Or.inl (mem_rootsTargets_param hq)))
          _ hrq g rfl
    cases hv : callee.vars[j]? with
    | none =>
      simp only [hv, List.mem_singleton] at ht
      subst ht; exact hpj
    | some lv =>
      cases hf : cctx.varRoots.find? (·.1 == j) with
      | none =>
        simp only [hv, hf, List.mem_singleton] at ht
        subst ht; exact hpj
      | some pr =>
        obtain ⟨x, rs⟩ := pr
        simp only [hv, hf] at ht
        by_cases hrl : lv.ty.isRefLike = true
        · simp only [hrl, if_true, rootsTargets, List.mem_filterMap] at ht
          obtain ⟨q, hq, hqt⟩ := ht
          cases q with
          | «local» y => simp [rootTarget] at hqt
          | global g =>
            simp only [rootTarget, Option.some.injEq] at hqt
            subst hqt
            have hmem : Target.global g ∈ paramGlobals callee cctx j := by
              simp only [paramGlobals, hv, hf, hrl, if_true, List.mem_filterMap]
              exact ⟨_, hq, rfl⟩
            exact hmap _ (mapCall_param callee cctx ars ds j hd _ (Or.inr hmem))
          | param k =>
            simp only [rootTarget, Option.some.injEq] at hqt
            subst hqt
            rcases hctx.paramAnn j rs (hpar j hd) (by simp [hf]) _ hq with e | ⟨g, e⟩
            · cases e; exact hpj
            · cases e
        · simp only [hrl, Bool.false_eq_true, if_false, List.mem_singleton] at ht
          subst ht; exact hpj

/-! ### Arguments -/

variable {W : World} {tenv : TEnv} {penv : PEnv} {env : Env}

private theorem HasTy.nonRef_store {source target : Store} {v : Val} {T : Ty}
    (typed : HasTy m W.G source v T) (nonref : T.isRefLike = false) :
    HasTy m W.G target v T := by
  cases T <;> simp only [Ty.isRefLike] at nonref
  all_goals first | exact typed | cases nonref

private theorem hasTy_ref_mu {G : Nat} {store : Store} {v : Val}
    {mu mu' : Mutability} {T : Ty} (typed : HasTy m G store v (.ref mu T)) :
    HasTy m G store v (.ref mu' T) := typed

private theorem HasTy.sliceHeader_present {source target : Store} {l : Loc}
    {mu mu' : Mutability} {E : Ty}
    (typed : HasTy m W.G source (.ref l) (.ref mu (.slice mu' E)))
    (present : target.roots[l.root]? ≠ none) :
    HasTy m W.G target (.ref l) (.ref mu (.slice mu' E)) := by
  obtain ⟨location, equal, ordinary | header⟩ := typed
  all_goals cases Val.ref.inj equal
  · simp [Ty.refTarget] at ordinary
  · exact ⟨_, rfl, Or.inr ⟨header.1, header.2.1, present⟩⟩

/-- Argument contexts keep their index in the complete source argument list;
evaluating a suffix must not restart its paths at zero. -/
noncomputable def callArgContext {plans : Array (Array DemandPoint)} {path : List Nat}
    {c : ContextId} {all : List Arg} {origin : OriginId}
    (context : EvaluationContext m plans path (.expression (.call c all origin)) .expression)
    (index : Nat) (arg : Arg) (harg : all[index]? = some arg) :
    ArgContext m plans (path ++ [index]) arg := by
  cases arg with
  | byVal e =>
    exact .byVal (context.child rfl index (.expression e) .expression
      (by simp [DemandNode.child?, DemandNode.children, harg])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]))
  | byRef mu p =>
    exact .byRef (context.child rfl index (.place p) .place
      (by simp [DemandNode.child?, DemandNode.children, harg])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]))

theorem callArgContext_activeMatches {plans path c all origin}
    (context : EvaluationContext m plans path (.expression (.call c all origin)) .expression)
    (index : Nat) (arg : Arg) (harg : all[index]? = some arg)
    (hactive : context.ActiveMatches tenv) :
    (callArgContext context index arg harg).ActiveMatches tenv := by
  cases arg with
  | byVal e =>
    exact context.child_activeMatches rfl index (.expression e) .expression
      (by simp [DemandNode.child?, DemandNode.children, harg])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) tenv tenv hactive
      (by intro x; rfl)
  | byRef mu p =>
    exact context.child_activeMatches rfl index (.place p) .place
      (by simp [DemandNode.child?, DemandNode.children, harg])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) tenv tenv hactive
      (by intro x; rfl)

theorem callArgContext_accessMatches {plans path c all origin}
    (context : EvaluationContext m plans path (.expression (.call c all origin)) .expression)
    (index : Nat) (arg : Arg) (harg : all[index]? = some arg)
    (haccess : context.AccessMatches tenv penv) :
    (callArgContext context index arg harg).AccessMatches tenv penv := by
  cases arg with
  | byVal e =>
    exact (context.child_accessMatches_iff rfl index (.expression e) .expression
      (by simp [DemandNode.child?, DemandNode.children, harg])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) tenv penv).2 haccess
  | byRef mu p =>
    exact (context.child_accessMatches_iff rfl index (.place p) .place
      (by simp [DemandNode.child?, DemandNode.children, harg])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) tenv penv).2 haccess

theorem callArgContext_mayShrink_iff {plans path c all origin}
    (context : EvaluationContext m plans path (.expression (.call c all origin)) .expression)
    (index : Nat) (arg : Arg) (harg : all[index]? = some arg)
    (P : Nat → RootInst → Prop) (observation : Observation) (r : RootInst) :
    (callArgContext context index arg harg).mayShrink P observation r ↔ context.mayShrink P observation r := by
  cases arg with
  | byVal e =>
    exact context.child_mayShrink_iff rfl index (.expression e) .expression
      (by simp [DemandNode.child?, DemandNode.children, harg])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) P observation r
  | byRef mu p =>
    exact context.child_mayShrink_iff rfl index (.place p) .place
      (by simp [DemandNode.child?, DemandNode.children, harg])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) P observation r

private theorem callArgContext_forbidden_subset {plans path c all origin}
    (context : EvaluationContext m plans path (.expression (.call c all origin)) .expression)
    (index : Nat) (arg : Arg) (harg : all[index]? = some arg) :
    ∀ owner, owner ∈ context.forbiddenOwners →
      owner ∈ (callArgContext context index arg harg).forbiddenOwners := by
  cases arg with
  | byVal e =>
    simpa only [callArgContext, ArgContext.forbiddenOwners] using
      context.child_forbidden_subset rfl index (.expression e) .expression
      (by simp [DemandNode.child?, DemandNode.children, harg])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])
  | byRef mu p =>
    simpa only [callArgContext, ArgContext.forbiddenOwners] using
      context.child_forbidden_subset rfl index (.place p) .place
      (by simp [DemandNode.child?, DemandNode.children, harg])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])

theorem callArgContext_retained_subset {plans path c all origin}
    (context : EvaluationContext m plans path (.expression (.call c all origin)) .expression)
    (index : Nat) (arg : Arg) (harg : all[index]? = some arg)
    {alias : RetainedAlias} (hmem : alias ∈ context.retained) :
    alias ∈ (callArgContext context index arg harg).retained := by
  cases arg with
  | byVal e =>
    exact context.child_retained_subset rfl index (.expression e) .expression
      (by simp [DemandNode.child?, DemandNode.children, harg])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) hmem
  | byRef mu p =>
    exact context.child_retained_subset rfl index (.place p) .place
      (by simp [DemandNode.child?, DemandNode.children, harg])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) hmem

theorem NodeContext.call_argument_alias {plans : Array (Array DemandPoint)}
    {pc : PlanContext m plans} {path : List Nat} {c : ContextId}
    {all : List Arg} {origin : OriginId}
    (context : NodeContext pc path (.expression (.call c all origin)) .expression)
    (index : Nat) (arg : Arg) (harg : all[index]? = some arg) :
    ∃ aliases, pc.approvals.access.aliasArg (path ++ [index]) arg = .ok aliases := by
  let transition := context.phase rfl .call
    (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])
  exact DemandNode.call_phase_alias_argument transition.phaseFrameEq
    (List.getElem?_eq_some_iff.mp harg).1 harg

theorem callArgContext_prefix_alias {plans : Array (Array DemandPoint)}
    {pc : PlanContext m plans} {path : List Nat} {c : ContextId}
    {all : List Arg} {origin : OriginId}
    (context : NodeContext pc path (.expression (.call c all origin)) .expression)
    (profile : m.profile = .shrink) (index : Nat) (arg : Arg)
    (harg : all[index]? = some arg) {earlier : Nat} {source : Arg}
    (before : earlier < index) (hsource : all[earlier]? = some source)
    {aliases : List RetainedAlias} {alias : RetainedAlias}
    (haliases : pc.approvals.access.aliasArg (path ++ [earlier]) source = .ok aliases)
    (member : alias ∈ aliases) :
    alias ∈ (callArgContext (.shrink profile context) index arg harg).retained := by
  cases arg with
  | byVal e =>
    let transition := context.child rfl index (.expression e) .expression
      (by simp [DemandNode.child?, DemandNode.children, harg])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])
    have childRetained := DemandNode.call_child_retains_argument transition.childFrameEq
      before hsource haliases member
    have retained := DemandNode.phaseFrame_retains transition.phaseFrameEq childRetained
    change alias ∈ transition.context.expected.frame.retained
    rw [transition.expectedFrameEq]
    exact retained
  | byRef mu p =>
    let transition := context.child rfl index (.place p) .place
      (by simp [DemandNode.child?, DemandNode.children, harg])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])
    have childRetained := DemandNode.call_child_retains_argument transition.childFrameEq
      before hsource haliases member
    have retained := DemandNode.phaseFrame_retains transition.phaseFrameEq childRetained
    change alias ∈ transition.context.expected.frame.retained
    rw [transition.expectedFrameEq]
    exact retained

/-- An argument suffix keeps prior slice holders, remaining argument uses and
the continuation. Its offset counts arguments in the complete source list. -/
def callArgsFuture {plans : Array (Array DemandPoint)} {path : List Nat}
    {c : ContextId} {all : List Arg} {origin : OriginId}
    (context : EvaluationContext m plans path (.expression (.call c all origin)) .expression)
    (offset : Nat) (args : List Arg) : List VarId :=
  match context with
  | .pilot _ active => args.flatMap Arg.variables ++ active
  | .shrink (pc := pc) _ context =>
    (all.take offset).flatMap (Arg.sliceHolderVariables pc.approvals.access) ++
      args.flatMap Arg.variables ++ context.outputFuture

/-- The final argument frame keeps exactly the local slice headers needed by
the continuation or passed directly by reference. -/
theorem callArgsFuture_sliceHolder {plans path c all origin}
    (context : EvaluationContext m plans path (.expression (.call c all origin)) .expression)
    (active : context.ActiveMatches tenv) (access : context.AccessMatches tenv penv)
    (variables : tenv.vars = env.vars) {x : VarId} {lv : LocalVar}
    {mu : Mutability} {E : Ty} (hvar : env.vars[x]? = some lv)
    (htype : lv.ty = .slice mu E) (visible : x ∈ tenv.visible)
    (needed : x ∈ context.outputFuture ∨ ∃ passingMu, Arg.byRef passingMu (.var x) ∈ all) :
    x ∈ callArgsFuture context all.length [] := by
  cases context with
  | pilot profile activeVariables =>
    exact (active x).2 visible
  | @shrink pc profile context =>
    rcases needed with continuation | ⟨passingMu, passed⟩
    · simp only [callArgsFuture, List.flatMap_nil, List.append_nil, List.mem_append]
      exact Or.inr continuation
    · have haccessVar : pc.approvals.access.impl.vars[x]? = some lv := by
        rw [access.2.1, variables]
        exact hvar
      have hlookup : pc.approvals.access.placeType? (.var x) = some (.slice mu E) := by
        simp [AccessEnv.placeType?, haccessVar, htype]
      simp only [callArgsFuture, List.take_length, List.flatMap_nil, List.append_nil,
        List.mem_append, List.mem_flatMap]
      exact Or.inl ⟨.byRef passingMu (.var x), passed, by
        simp [Arg.sliceHolderVariables, hlookup, Place.variables]⟩

theorem callArgContext_input_output {plans path c all origin}
    (context : EvaluationContext m plans path (.expression (.call c all origin)) .expression)
    (index : Nat) (arg : Arg) (harg : all[index]? = some arg) :
    (callArgContext context index arg harg).inputFuture =
      arg.variables ++ (callArgContext context index arg harg).outputFuture := by
  cases arg <;> cases context <;>
    simp [callArgContext, ArgContext.inputFuture, ArgContext.outputFuture,
      EvaluationContext.child, EvaluationContext.inputFuture, EvaluationContext.outputFuture,
      DemandNode.variables, Arg.variables, DemandNode.visibleAfter, DemandNode.visibleForChild,
      NodeContext.inputFuture, NodeContext.outputFuture]

theorem callArgContext_shrinkOutputFuture {plans : Array (Array DemandPoint)}
    {pc : PlanContext m plans} {path : List Nat} {c : ContextId}
    {all : List Arg} {origin : OriginId}
    (context : NodeContext pc path (.expression (.call c all origin)) .expression)
    (profile : m.profile = .shrink) (index : Nat) (arg : Arg) (rest : List Arg)
    (harg : all[index]? = some arg) (hrest : rest = all.drop (index + 1)) :
    (callArgContext (.shrink profile context) index arg harg).outputFuture =
      callArgsFuture (.shrink profile context) (index + 1) rest := by
  have hbound : index < all.length := (List.getElem?_eq_some_iff.mp harg).1
  cases arg with
  | byVal e =>
    let transition := context.child rfl index (.expression e) .expression
      (by simp [DemandNode.child?, DemandNode.children, harg])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])
    have child : (DemandNode.expression (.call c all origin)).child? index =
        some (.expression e) := by simp [DemandNode.child?, DemandNode.children, harg]
    have expected : (DemandNode.expression (.call c all origin)).childExpectation?
        pc.approvals.access
        ⟨path, .expression, context.expected.frame.active,
          context.expected.frame.future, context.expected.frame.retained⟩ index =
        some ⟨context.expected.frame.active,
          (all.take (index + 1)).flatMap (Arg.sliceHolderVariables pc.approvals.access) ++
            rest.flatMap Arg.variables ++ context.expected.frame.future⟩ := by
      simp [DemandNode.childExpectation?, child,
        DemandNode.childFuture, DemandNode.visibleForChild, hbound, hrest,
        List.append_assoc]
    have future := DemandNode.childFrame_future transition.childFrameEq expected
    change transition.context.expected.frame.future = _
    rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
    simpa [callArgsFuture, NodeContext.outputFuture, DemandNode.phaseFuture] using future
  | byRef mu p =>
    let transition := context.child rfl index (.place p) .place
      (by simp [DemandNode.child?, DemandNode.children, harg])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])
    have child : (DemandNode.expression (.call c all origin)).child? index =
        some (.place p) := by simp [DemandNode.child?, DemandNode.children, harg]
    have expected : (DemandNode.expression (.call c all origin)).childExpectation?
        pc.approvals.access
        ⟨path, .expression, context.expected.frame.active,
          context.expected.frame.future, context.expected.frame.retained⟩ index =
        some ⟨context.expected.frame.active,
          (all.take (index + 1)).flatMap (Arg.sliceHolderVariables pc.approvals.access) ++
            rest.flatMap Arg.variables ++ context.expected.frame.future⟩ := by
      simp [DemandNode.childExpectation?, child,
        DemandNode.childFuture, DemandNode.visibleForChild, hbound, hrest,
        List.append_assoc]
    have future := DemandNode.childFrame_future transition.childFrameEq expected
    change transition.context.expected.frame.future = _
    rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
    simpa [callArgsFuture, NodeContext.outputFuture, DemandNode.phaseFuture] using future

private theorem sliceHolderVariables_subset (access : AccessEnv) (arg : Arg) {x : VarId}
    (member : x ∈ arg.sliceHolderVariables access) : x ∈ arg.variables := by
  cases arg with
  | byVal e => simp [Arg.sliceHolderVariables] at member
  | byRef mu p =>
    cases ty : access.placeType? p with
    | none => simp [Arg.sliceHolderVariables, ty] at member
    | some T => cases T <;> simp_all [Arg.sliceHolderVariables, Arg.variables]

theorem callArgContext_inputFuture_subset {plans path c all origin}
    (context : EvaluationContext m plans path (.expression (.call c all origin)) .expression)
    (index : Nat) (arg : Arg) (rest : List Arg) (harg : all[index]? = some arg)
    (hrest : rest = all.drop (index + 1)) {x : VarId}
    (member : x ∈ (callArgContext context index arg harg).inputFuture) :
    x ∈ callArgsFuture context index (arg :: rest) := by
  rw [callArgContext_input_output] at member
  cases context with
  | pilot profile active =>
    have output : (callArgContext (plans := plans) (path := path) (c := c) (origin := origin)
      (.pilot profile active) index arg harg).outputFuture = active := by
      cases arg <;> simp [callArgContext, ArgContext.outputFuture,
        EvaluationContext.child, EvaluationContext.outputFuture, DemandNode.visibleAfter,
        DemandNode.visibleForChild]
    rw [output] at member
    simp only [callArgsFuture, List.flatMap_cons, List.append_assoc, List.mem_append] at member ⊢
    rcases member with current | active
    · exact Or.inl current
    · exact Or.inr (Or.inr active)
  | shrink profile context =>
    rw [callArgContext_shrinkOutputFuture context profile index arg rest harg hrest] at member
    have prefixEq : all.take (index + 1) = all.take index ++ [arg] := by
      simpa [harg] using (List.take_succ (l := all) (i := index))
    simp only [callArgsFuture, prefixEq, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc, List.mem_append] at member ⊢
    rcases member with current | previous | holder | later | continuation
    · exact Or.inr (Or.inl current)
    · exact Or.inl previous
    · exact Or.inr (Or.inl (sliceHolderVariables_subset _ arg holder))
    · exact Or.inr (Or.inr (Or.inl later))
    · exact Or.inr (Or.inr (Or.inr continuation))

theorem callArgFrame_rest {plans path c all origin}
    (context : EvaluationContext m plans path (.expression (.call c all origin)) .expression)
    (index : Nat) (arg : Arg) (rest : List Arg) (harg : all[index]? = some arg)
    (hrest : rest = all.drop (index + 1)) (active : context.ActiveMatches tenv) {s : St}
    (frame : Frame m W tenv penv env s (callArgContext context index arg harg).outputFuture) :
    Frame m W tenv penv env s (callArgsFuture context (index + 1) rest) := by
  cases context with
  | pilot profile variables =>
    have output : (callArgContext (plans := plans) (path := path) (c := c) (origin := origin)
      (.pilot profile variables) index arg harg).outputFuture =
        variables := by
      cases arg <;> simp [callArgContext, ArgContext.outputFuture,
        EvaluationContext.child, EvaluationContext.outputFuture, DemandNode.visibleAfter,
        DemandNode.visibleForChild]
    rw [output] at frame
    exact frame.changeFuture (fun x visible _ => (active x).2 visible)
  | shrink profile context =>
    simpa [callArgContext_shrinkOutputFuture context profile index arg rest harg hrest] using frame

private theorem argument_sliceHeader_present {future : List VarId} {s : St}
    {path : List Nat} {p : Place} {mu mu' : Mutability} {E : Ty}
    {tn tn' : Nat} {rst rst' : RState} {rho : List RootRef} {aliases : List RetainedAlias}
    (frame : Frame m W tenv penv env s future)
    (typing : ArgTy tenv (.byRef mu p) tn (.ref mu (.slice mu' E)) tn')
    (replay : ArgRp penv (.byRef mu p) rst rho rst')
    (lookup : penv.access.aliasArg path (.byRef mu p) = .ok aliases)
    (flat : E.flat = true) {root : RootInst} (roots : Gam env W.P rho root) :
    s.store.roots[root]? ≠ none := by
  obtain ⟨T, caps, placeTy, allowed, equal⟩ := typing
  obtain ⟨_, rfl⟩ := Ty.ref.inj equal
  have initialPlaceTy := placeTy
  have sliceArg : p.sliceArg = true := by
    have permitted : caps.1 = true ∧ p.sliceArg = true := by
      simpa [Ty.refTarget, Ty.isSlice, flat] using allowed
    exact permitted.2
  cases p with
  | var x =>
    simp only [tyPlace] at placeTy; inv at placeTy
    obtain ⟨visible, lv, hvariable, typeEq, _, _⟩ := placeTy
    simp only [ArgRp, rpPlace] at replay; inv at replay
    obtain ⟨rfl, _⟩ := replay
    obtain ⟨q, member, denoted⟩ := roots
    simp only [List.mem_singleton] at member
    subst q
    obtain ⟨other, scopeId, hvariable', scope, rfl⟩ := denoted
    rw [frame.vars_t] at hvariable
    rw [hvariable] at hvariable'
    cases hvariable'
    obtain ⟨lv', si', value, hvar, hscope, _, present, _⟩ := frame.bindings x visible
    rw [hvariable] at hvar
    cases hvar
    rw [scope] at hscope
    cases hscope
    simp [present]
  | deref e =>
    obtain ⟨x, sourceEq⟩ : ∃ x, e = .read (.var x) := by
      cases e <;> simp [Place.sliceArg, Place.derefVar?] at sliceArg
      rename_i source
      cases source <;> simp at sliceArg
      exact ⟨_, rfl⟩
    subst e
    cases hs : sliceRefTy tenv (.read (.var x)) with
    | none =>
      simp only [tyPlace, hs] at placeTy; inv at placeTy
      obtain ⟨te, next, ⟨te', before, expressionTy, notSlice, rfl, rfl⟩, tail⟩ := placeTy
      cases te <;> inv at tail
      obtain ⟨rfl, _, _⟩ := tail
      simp [Ty.isRefSlice, flat] at notSlice
    | some sourceTy =>
      obtain ⟨x', lv, outerMu, sliceMu, element, sourceEq, visible, hvariable, typeEq,
        elementFlat, rfl⟩ := sliceRefTy_some hs
      cases sourceEq
      simp only [tyPlace, hs] at placeTy
      rw [typeEq] at placeTy; inv at placeTy
      obtain ⟨typeEqual, _, _⟩ := placeTy
      cases typeEqual
      have accessType : penv.access.placeType? (.deref (.read (.var x))) =
          some (.slice mu' E) :=
        tyPlace_accessType (frame.mod_t.trans frame.mod_p.symm)
          (frame.vars_t.trans frame.vars_p.symm) initialPlaceTy
      have content : ∃ cont, penv.cont x = some cont := by
        simp only [AccessEnv.aliasArg, accessType] at lookup
        obtain ⟨contentRoots, contentLookup, _⟩ := (ex_bind_ok _ _ _).mp lookup
        have variableP : penv.impl.vars[x]? = some lv := by
          rw [frame.vars_p]
          exact frame.vars_t ▸ hvariable
        simp only [AccessEnv.exprRoots, PEnv.access, variableP, Option.map_some,
          typeEq, Ty.isRefSlice, flat, ite_true] at contentLookup
        cases hc : penv.cont x with
        | none =>
          simp only [PEnv.cont] at hc
          simp [AccessEnv.contentRoots, hc, reject] at contentLookup
        | some cont => exact ⟨cont, rfl⟩
      obtain ⟨cont, contentLookup⟩ := content
      obtain ⟨_, annotation, prefProtect⟩ := frame.pref x cont contentLookup
      simp only [ArgRp, rpPlace, rpExpr] at replay; inv at replay
      obtain ⟨state1, _, readLookup⟩ := replay
      have actualRoots : rho = [.param x] := by
        obtain ⟨_, casesRead⟩ := readRoots_ok penv (.var x) _ _ readLookup
        rcases casesRead with ⟨y, other, equal, variableP, _, ann⟩ | ⟨y, equal, _⟩ |
          ⟨_, noReference, _⟩
        · cases equal
          rw [annotation] at ann
          exact Option.some.inj ann.symm
        · cases equal
        · have variableP : penv.impl.vars[x]? = some lv := by
            rw [frame.vars_p]
            exact frame.vars_t ▸ hvariable
          have := noReference x lv rfl variableP
          simp [typeEq, Ty.isRefLike] at this
      rw [actualRoots] at roots
      obtain ⟨q, member, denoted⟩ := roots
      simp only [List.mem_singleton] at member
      subst q
      have variableEnv : env.vars[x]? = some lv := frame.vars_t ▸ hvariable
      obtain ⟨sliceProtected, _, _⟩ := prefProtect lv outerMu mu' E variableEnv typeEq root denoted
      obtain ⟨value, present, _⟩ := frame.sa root E sliceProtected
      simp [present]
  | global _ => simp [Place.sliceArg, Place.derefVar?] at sliceArg
  | elem _ _ _ => simp [Place.sliceArg, Place.derefVar?] at sliceArg
  | field _ _ => simp [Place.sliceArg, Place.derefVar?] at sliceArg

private theorem argument_byRef_type_preserved {future : List VarId} {source : Store} {s : St}
    {path : List Nat} {p : Place} {mu : Mutability} {T : Ty} {v : Val}
    {tn tn' : Nat} {rst rst' : RState} {rho : List RootRef} {aliases : List RetainedAlias}
    (frame : Frame m W tenv penv env s future)
    (typing : ArgTy tenv (.byRef mu p) tn (.ref mu T) tn')
    (replay : ArgRp penv (.byRef mu p) rst rho rst')
    (lookup : penv.access.aliasArg path (.byRef mu p) = .ok aliases)
    (retained : RetainsAliases m W env source s.store aliases)
    (typed : HasTy m W.G source v (.ref mu T))
    (roots : ∀ root, Targets v root → Gam env W.P rho root) :
    HasTy m W.G s.store v (.ref mu T) := by
  by_cases slice : ∃ sliceMu element, T = .slice sliceMu element
  · obtain ⟨sliceMu, element, rfl⟩ := slice
    obtain ⟨location, rfl, ordinary | header⟩ := typed
    · simp [Ty.refTarget] at ordinary
    · have flat : element.flat = true := by simpa [Ty.isSlice] using header.1
      exact HasTy.sliceHeader_present ⟨location, rfl, Or.inr header⟩
        (argument_sliceHeader_present frame typing replay lookup flat (roots location.root rfl))
  · obtain ⟨placeType, caps, placeTy, _, equal⟩ := typing
    obtain ⟨_, rfl⟩ := Ty.ref.inj equal
    have accessType := tyPlace_accessType (frame.mod_t.trans frame.mod_p.symm)
      (frame.vars_t.trans frame.vars_p.symm) placeTy
    have placeAlias : penv.access.aliasPlace path p = .ok aliases := by
      cases T <;> simp_all [AccessEnv.aliasArg]
    have records : ((Ty.ref .mutable T).interiorTarget?.isSome || T.ownerElem?.isSome) = true := by
      cases owner : T.ownerElem?.isSome <;> simp [Ty.interiorTarget?, owner]
    simp only [AccessEnv.aliasPlace, accessType, records, ite_true] at placeAlias
    obtain ⟨accessRoots, accessLookup, equal⟩ := (ex_bind_ok _ _ _).mp placeAlias
    have aliasesEq : aliases = [⟨.ref .mutable T, accessRoots, .operand path⟩] :=
      (ex_pure_ok _ _).mp equal
    rw [aliasesEq] at retained
    have included := rpPlace_accessRoots penv p rst rho rst' accessRoots replay accessLookup
    have realized : AliasAt m W env source ⟨.ref .mutable T, accessRoots, .operand path⟩ v :=
      ⟨hasTy_ref_mu typed, fun root target => (roots root target).subset included⟩
    exact hasTy_ref_mu ((retained _ List.mem_cons_self).typed v realized).1

private theorem argument_byVal_type_preserved {source target : Store}
    {path : List Nat} {e : Expr} {T : Ty} {v : Val}
    {rst rst' : RState} {rho : List RootRef} {aliases : List RetainedAlias}
    (typeLookup : penv.access.exprType? e = some T)
    (copyable : T.isRefLike = false ∨ T.interiorTarget?.isSome = true)
    (replay : ArgRp penv (.byVal e) rst rho rst')
    (lookup : penv.access.aliasArg path (.byVal e) = .ok aliases)
    (retained : RetainsAliases m W env source target aliases)
    (typed : HasTy m W.G source v T)
    (roots : ∀ root, Targets v root → Gam env W.P rho root) :
    HasTy m W.G target v T := by
  rcases copyable with nonref | interior
  · exact typed.nonRef_store nonref
  · simp only [AccessEnv.aliasArg, AccessEnv.aliasExpr, typeLookup, interior, ite_true] at lookup
    obtain ⟨accessRoots, accessLookup, equal⟩ := (ex_bind_ok _ _ _).mp lookup
    have aliasesEq : aliases = [⟨T, accessRoots, .operand path⟩] :=
      (ex_pure_ok _ _).mp equal
    rw [aliasesEq] at retained
    have included := rpExpr_accessRoots penv e rst rho rst' accessRoots replay accessLookup
    have realized : AliasAt m W env source ⟨T, accessRoots, .operand path⟩ v :=
      ⟨typed, fun root target => (roots root target).subset included⟩
    exact ((retained _ List.mem_cons_self).typed v realized).1

/- A by-value argument can weaken reference mutability, but it cannot change the
underlying resizable owner type that justifies owner authority. -/
private theorem OwnerRefTy.of_passable {source target : Ty}
    (passable : source.passableTo target = true) (targetOwner : OwnerRefTy target) :
    OwnerRefTy source := by
  cases target with
  | ref targetMu targetType =>
    rcases targetOwner with ⟨ownerMu, element, ownerGrow | ownerGrowshrink⟩
    · cases ownerGrow
      cases source with
      | ref sourceMu sourceType =>
        simp only [Ty.passableTo, Bool.and_eq_true, beq_iff_eq] at passable
        obtain ⟨sourceEq, _⟩ := passable
        subst sourceType
        exact ⟨sourceMu, element, Or.inl rfl⟩
      | _ => simp [Ty.passableTo] at passable
    · cases ownerGrowshrink
      cases source with
      | ref sourceMu sourceType =>
        simp only [Ty.passableTo, Bool.and_eq_true, beq_iff_eq] at passable
        obtain ⟨sourceEq, _⟩ := passable
        subst sourceType
        exact ⟨sourceMu, element, Or.inr rfl⟩
      | _ => simp [Ty.passableTo] at passable
  | _ => simp [OwnerRefTy] at targetOwner

private theorem OwnerRooted.passable {env : Env} {ownerP : Nat → RootInst → Prop}
    {roots : List RootRef} {v : Val} {source target : Ty}
    (rooted : OwnerRooted env ownerP roots v source)
    (passable : source.passableTo target = true) :
    OwnerRooted env ownerP roots v target := by
  intro targetOwner r targetOf
  exact rooted (OwnerRefTy.of_passable passable targetOwner) r targetOf

private def callPrefixRetained {plans path c all origin}
    (context : EvaluationContext m plans path (.expression (.call c all origin)) .expression)
    (offset : Nat) (source target : Store) : Prop :=
  match context with
  | .pilot _ _ => True
  | .shrink (pc := pc) _ _ => ∀ index arg aliases, index < offset → all[index]? = some arg →
      pc.approvals.access.aliasArg (path ++ [index]) arg = .ok aliases →
      RetainsAliases m W env source target aliases

/-- A checked by-value parameter cannot accept a sampled reference value. -/
theorem ImplOk.byValue_not_ref {impl : Impl} (checked : ImplOk m impl)
    (p : Param) (membership : p ∈ impl.params.toList) (mode : p.mode = .byValue)
    (pv : LocalVar) (mu : Mutability) (T : Ty) (variableAt : impl.vars[p.var]? = some pv) :
    pv.ty ≠ .ref mu T := by
  obtain ⟨index, bound, parameterEq⟩ := List.mem_iff_getElem.mp membership
  have parameterAt : impl.params[index]? = some p := by
    simpa using (List.getElem?_eq_some_iff.mpr ⟨bound, parameterEq⟩)
  obtain ⟨variableEq, _⟩ := checked.params index p parameterAt
  have shape := checked.parameterShape index (by simpa using bound)
  intro referenceType
  rw [variableEq] at variableAt
  simp only [checkParam, parameterAt, variableAt, mode, referenceType] at shape
  inv at shape

set_option maxHeartbeats 1600000 in
 theorem args_spec {plans path c all origin}
    (ec : EvaluationContext m plans path (.expression (.call c all origin)) .expression)
    (observation : Observation) (ihA : ArgSpec m prof plans n) (hp : Perm m W)
    (active : ec.ActiveMatches tenv) (access : ec.AccessMatches tenv penv)
    (protectedSlices : ShrinkProtected W.D W.A (ec.mayShrink W.ownerP observation))
    (callee : Impl) (calleeChecked : ImplOk m callee) :
    ∀ (args : List Arg) (ps : List Param) (offset : Nat) (s : St)
      (tn tn' : Nat) (rst rst' : RState) (ars : List (List RootRef)),
    args = all.drop offset → offset ≤ all.length →
    (∀ p, p ∈ ps → p ∈ callee.params.toList) →
    Frame m W tenv penv env s (callArgsFuture ec offset args) →
    ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s.store →
    (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s.store) →
    ps.length = args.length →
    tyArgs tenv callee ps args tn = .ok ((), tn') →
    rpArgs penv args rst = .ok (ars, rst') → EffLe rst'.eff W.E →
    Sat (mapList (evalArg n ⟨prof, m⟩ env) args) s (fun vals s' =>
      Frame m W tenv penv env s' (callArgsFuture ec all.length []) ∧
      Footprint (insts env) (Dset W) s s' ∧
      PreservesRootTypes m W.G observation.roots s.store s'.store ∧
      PreservesValues m W.G observation.values s.store s'.store ∧
      ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s'.store ∧
      RetainsAliases m W env s.store s'.store ec.retained ∧
      PilotStoreLe m s s' ∧ callPrefixRetained (W := W) (env := env) ec offset s.store s'.store ∧
      vals.length = args.length ∧
      (∀ (i : Nat) (v : Val), vals[i]? = some v → ∃ (p : Param) (pv : LocalVar)
          (ar : List RootRef) (a : Arg) (ty : Ty) (tn0 tn1 : Nat) (rst0 rst1 : RState),
        ps[i]? = some p ∧ callee.vars[p.var]? = some pv ∧
        ars[i]? = some ar ∧ HasTy m W.G s'.store v pv.ty ∧
        (∀ r, Targets v r → Gam env W.P ar r) ∧ OwnerRooted env W.ownerP ar v pv.ty ∧
        args[i]? = some a ∧
        ArgTy tenv a tn0 ty tn1 ∧ ty.passableTo pv.ty = true ∧ ArgRp penv a rst0 ar rst1) ∧
      (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s'.store) ∧
      PreservesForbiddenOwnerRoots (m := m) (G := W.G) (env := env) (P := W.P)
        ec.forbiddenOwners s s' ∧
      MutationFootprint env W.P W.base (effectMutationRoots m penv.impl rst'.eff) s s')
  | [], ps, offset, s, tn, tn', rst, rst', ars, sourceEq, bound, _, frame, observed, classified,
      _, _, _, _ => by
    have offsetEq : offset = all.length := by
      have := List.drop_eq_nil_iff.mp sourceEq.symm
      omega
    simp only [mapList, sat_pure]
    refine ⟨by simpa [offsetEq] using frame, Footprint.refl _ _ _,
      PreservesRootTypes.refl _, PreservesValues.refl _, observed, RetainsAliases.refl,
      fun _ => StoreLe.refl _, ?_, rfl, fun i v lookup => by simp at lookup, classified,
      PreservesForbiddenOwnerRoots.refl _, MutationFootprint.refl _ _ _ _ _⟩
    cases ec with
    | pilot _ _ => trivial
    | shrink _ _ => exact fun _ _ _ _ _ _ => RetainsAliases.refl
  | a :: as, [], offset, s, tn, tn', rst, rst', ars, _, _, _, _, _, _, size, _, _, _ => by
    simp at size
  | a :: as, p :: ps, offset, s, tn, tn', rst, rst', ars, sourceEq, bound, psSubset,
      frame, observed, classified, size, ht, hr, effects => by
    have hl' : ps.length = as.length := by simpa using size
    have harg : all[offset]? = some a := by
      have first : (all.drop offset)[0]? = some a := by rw [← sourceEq]; rfl
      simpa using first
    have hrest : as = all.drop (offset + 1) := by
      rw [List.drop_add_one_eq_tail_drop, ← sourceEq]
      rfl
    have nextBound : offset + 1 ≤ all.length := by
      have := (List.getElem?_eq_some_iff.mp harg).1
      omega
    cases hv : callee.vars[p.var]? with
    | none => cases a <;> (simp only [tyArgs, hv] at ht; inv at ht)
    | some pv =>
      have key : ∃ ty t1 rho r1 ars', argMode a = p.mode ∧ ArgTy tenv a tn ty t1 ∧ ty.passableTo pv.ty = true ∧
          tyArgs tenv callee ps as t1 = .ok ((), tn') ∧ ArgRp penv a rst rho r1 ∧
          rpArgs penv as r1 = .ok (ars', rst') ∧ ars = rho :: ars' := by
        cases a with
        | byVal e =>
          simp only [tyArgs, hv] at ht; inv at ht
          simp only [rpArgs] at hr; inv at hr
          obtain ⟨modeEq, te, t1, hte, hpass, tailTyping⟩ := ht
          obtain ⟨rho, r1, hre, ars', r2, hra, rfl, rfl⟩ := hr
          exact ⟨te, t1, rho, r1, ars', by simpa using modeEq, hte, hpass, tailTyping, hre, hra, rfl⟩
        | byRef mu p' =>
          simp only [tyArgs, hv] at ht; inv at ht
          simp only [rpArgs] at hr; inv at hr
          obtain ⟨modeEq, t, b, contents, t1, htp, hallowed, hrt, ht⟩ := ht
          obtain ⟨rho, r1, hre, ars', r2, hra, rfl, rfl⟩ := hr
          have h2 : (Ty.ref mu t).passableTo pv.ty = true ∧
              tyArgs tenv callee ps as t1 = .ok ((), tn') := by
            rcases ht with ⟨_, _, h1, h2⟩ | ⟨_, h1, h2⟩ <;> exact ⟨h1, h2⟩
          have hrt' : t.refTarget = true ∨ (t.isSlice = true ∧ b = true ∧ p'.sliceArg = true) := by
            cases t <;> simpa [PlaceInfo.referenceWritable, Ty.refTarget, Ty.isSlice,
              Bool.or_eq_true, Bool.and_eq_true, and_assoc] using hrt
          exact ⟨.ref mu t, t1, rho, r1, ars', by simpa using modeEq, ⟨t, (b, contents), htp, hrt', rfl⟩, h2.1, h2.2, hre, hra, rfl⟩
      obtain ⟨ty, t1, rho, r1, ars', modeEq, hat, hpass, tailTyping, har, hra, rfl⟩ := key

      let ac := callArgContext ec offset a harg
      have shrinkEq : ac.mayShrink W.ownerP observation = ec.mayShrink W.ownerP observation := by
        funext root
        exact propext (callArgContext_mayShrink_iff ec offset a harg W.ownerP observation root)
      have childFrame : Frame m W tenv penv env s ac.inputFuture :=
        frame.changeFuture (fun x _ member =>
          callArgContext_inputFuture_subset ec offset a as harg hrest member)
      have childProtected : ShrinkProtected W.D W.A (ac.mayShrink W.ownerP observation) := by
        rw [shrinkEq]
        exact protectedSlices
      have childObserved : ObservedSafe m W (ac.mayShrink W.ownerP observation) observation s.store := by
        rw [shrinkEq]
        exact observed
      simp only [mapList]
      refine Sat.bind (ihA (path ++ [offset]) a ac observation W tenv penv env s _ _ _ _ _ _
        (callArgContext_activeMatches ec offset a harg active)
        (callArgContext_accessMatches ec offset a harg access)
        childProtected childObserved classified hp childFrame hat har
        ((rpArgs_mono hra).2.trans effects)) ?_
      rintro v s1 ⟨frame1, footprint1, types1, values1, observed1, retained1, pilot1,
        typed1, roots1, classified1, ownerRooted1, forbidden1, mutations1⟩
      rw [shrinkEq] at observed1
      have parentForbidden1 : PreservesForbiddenOwnerRoots (m := m) (G := W.G)
          (env := env) (P := W.P) ec.forbiddenOwners s s1 :=
        forbidden1.subset (fun owner member =>
          callArgContext_forbidden_subset ec offset a harg owner member)
      have parentRetained1 := retained1.subset (fun alias member =>
        callArgContext_retained_subset ec offset a harg member)
      have prefix1 : callPrefixRetained (W := W) (env := env) ec offset s.store s1.store := by
        cases ec with
        | pilot _ _ => trivial
        | shrink profile context =>
          intro earlier source aliases before sourceLookup aliasesLookup
          exact retained1.subset (fun alias member =>
            callArgContext_prefix_alias context profile offset a harg before sourceLookup aliasesLookup member)
      refine Sat.bind (args_spec ec observation ihA hp active access protectedSlices callee
        calleeChecked as ps (offset + 1) s1 _ _ _ _ _ hrest nextBound
        (fun p hp => psSubset p (List.mem_cons_of_mem _ hp))
        (callArgFrame_rest ec offset a as harg hrest active frame1)
        observed1 classified1 hl' tailTyping hra effects) ?_
      rintro vals s2 ⟨frame2, footprint2, types2, values2, observed2, retained2, pilot2,
        prefix2, length2, hall, classified2, forbidden2, mutations2⟩
      simp only [sat_pure]
      refine ⟨frame2, footprint1.trans footprint2, types1.trans types2, values1.trans values2,
        observed2, parentRetained1.trans retained2, fun hpilot => (pilot1 hpilot).trans (pilot2 hpilot),
        ?_, by simp [length2], ?_, classified2, parentForbidden1.trans forbidden2,
        (mutations1.weaken (effectMutationRoots.mono m penv.impl
          (rpArgs_mono hra).2 (rpArgs_rebinds_mono hra))).trans mutations2⟩
      · cases ec with
        | pilot _ _ => trivial
        | shrink _ _ =>
          intro earlier source aliases before sourceLookup aliasesLookup
          exact (prefix1 earlier source aliases before sourceLookup aliasesLookup).trans
            (prefix2 earlier source aliases (by omega) sourceLookup aliasesLookup)
      · intro i value valueLookup
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at valueLookup
          subst value
          have typed2 : HasTy m W.G s2.store v ty := by
            cases ec with
            | pilot profile _ => exact typed1.mono (pilot2 profile)
            | @shrink pc profile context =>
              obtain ⟨aliases, aliasLookup⟩ := context.call_argument_alias offset a harg
              have aliasLookupP : penv.access.aliasArg (path ++ [offset]) a = .ok aliases := by
                have accessEq : pc.approvals.access = penv.access := by
                  rcases access with ⟨_, _, hmod, himpl, hctx⟩
                  have rebuild : pc.approvals.access =
                      ⟨pc.approvals.access.mod, pc.approvals.access.impl, pc.approvals.access.ctx⟩ := by
                    cases pc.approvals.access
                    rfl
                  exact rebuild.trans (by rw [hmod, himpl, hctx]; rfl)
                simpa [accessEq] using aliasLookup
              have retainedArg := prefix2 offset a aliases (by omega) harg aliasLookup
              cases a with
              | byVal e =>
                have copyable : ty.isRefLike = false ∨ ty.interiorTarget?.isSome = true := by
                  cases ty with
                  | ref mu T =>
                    cases hpv : pv.ty <;> simp only [Ty.passableTo, hpv] at hpass <;>
                      first | contradiction | skip
                    exact False.elim (calleeChecked.byValue_not_ref p (psSubset p List.mem_cons_self)
                      (by simpa [argMode] using modeEq.symm) pv _ _ hv hpv)
                  | slice _ _ => exact Or.inr rfl
                  | _ => exact Or.inl rfl
                exact argument_byVal_type_preserved (tyExpr_accessType (frame.mod_t.trans frame.mod_p.symm)
                  (frame.vars_t.trans frame.vars_p.symm) hat) copyable har
                  aliasLookupP retainedArg typed1 roots1
              | byRef mu place =>
                obtain ⟨T, caps, placeTy, allowed, rfl⟩ := hat
                exact argument_byRef_type_preserved frame2 ⟨T, caps, placeTy, allowed, rfl⟩
                  har aliasLookupP retainedArg typed1 roots1
          exact ⟨p, pv, rho, a, ty, _, _, _, _, rfl, hv, rfl,
            hasTy_passable typed2 hpass, roots1, ownerRooted1.passable hpass,
            rfl, hat, hpass, har⟩
        | succ i =>
          simp only [List.getElem?_cons_succ] at valueLookup
          obtain ⟨p', pv', ar, a', ty', n0, n1, q0, q1,
            g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩ :=
            hall i value valueLookup
          exact ⟨p', pv', ar, a', ty', n0, n1, q0, q1, by simpa using g1, g2, by simpa using g3,
            g4, g5, g6, by simpa using g7, g8, g9, g10⟩

/-! ### The caller's slice variables, as the callee sees them -/

variable {s : St} {future continuation : List VarId} {args : List Arg}

/-- Inherited slice holders stay protected even when this call cannot rebind
them. A local holder stays live while its continuation or a reference argument
needs it, including a reference argument whose holder is dead after the call. -/
def callD (W : World) (tenv : TEnv) (env : Env) (continuation : List VarId)
    (args : List Arg) : RootInst → Ty → Prop := fun r E =>
  W.D r E ∨ ∃ x lv si mu, env.vars[x]? = some lv ∧ env.scopes.lookup lv.scope = some si ∧
    r = RootInst.local env.act si x ∧ lv.ty = .slice mu E ∧ x ∈ tenv.visible ∧
      (x ∈ continuation ∨ ∃ passingMu, Arg.byRef passingMu (.var x) ∈ args)

theorem callD_inherited {holder : RootInst} {element : Ty}
    (h : W.D holder element) : callD W tenv env continuation args holder element :=
  Or.inl h

/-- What a slice stored in such a variable may point into: for a variable of
the caller, what its annotation denotes and outlives it. -/
def callA (W : World) (penv : PEnv) (env : Env) : RootInst → RootInst → Prop := fun r t =>
  (Dset W r ∧ W.A r t) ∨ ∃ x lv si ann, env.vars[x]? = some lv ∧
    env.scopes.lookup lv.scope = some si ∧ r = RootInst.local env.act si x ∧
    penv.ann x = some ann ∧ Gam env W.P ann t ∧ Older t r

theorem Frame.not_outer (hF : Frame m W tenv penv env s future) {x : VarId} {sc si : Nat}
    (hl : env.scopes.lookup sc = some si) : ¬ Dset W (RootInst.local env.act si x) := by
  rintro ⟨E, hd⟩
  obtain ⟨a, si', x', e, hlt⟩ := hF.dOut _ E hd
  cases e
  exact absurd (hF.inst_lt hl).1 (Nat.not_le.2 hlt)

theorem callA_older (hF : Frame m W tenv penv env s future) :
    ∀ r t, callA W penv env r t → Older t r := by
  rintro r t (⟨_, h⟩ | ⟨x, lv, si, ann, _, _, _, _, _, h⟩)
  · exact hF.aOlder r t h
  · exact h

theorem callD_out (hF : Frame m W tenv penv env s future) :
    ∀ r E, callD W tenv env continuation args r E →
      ∃ a si x, r = RootInst.local a si x ∧ si < s.nextScope := by
  rintro r E (h | ⟨x, lv, si, mu, _, hl, rfl, _⟩)
  · obtain ⟨a, si, x, e, hlt⟩ := hF.dOut r E h
    exact ⟨a, si, x, e, Nat.lt_of_lt_of_le hlt hF.base_le⟩
  · exact ⟨_, _, _, rfl, (hF.inst_lt hl).2⟩

theorem callD_fun (hF : Frame m W tenv penv env s future) :
    ∀ r E E', callD W tenv env continuation args r E →
      callD W tenv env continuation args r E' → E = E' := by
  rintro r E E' (h | ⟨x, lv, si, mu, hx, hl, rfl, hty, _⟩) (h' | ⟨x', lv', si', mu', hx', hl', e, hty', _⟩)
  · exact hF.dFun r E E' h h'
  · subst e; exact absurd ⟨E, h⟩ (hF.not_outer hl')
  · exact absurd ⟨E', h'⟩ (hF.not_outer hl)
  · cases e
    rw [hx] at hx'; cases hx'
    rw [hty] at hty'; cases hty'; rfl

theorem callOuterOk (hF : Frame m W tenv penv env s future)
    (hdemand : ∀ x lv mu E, env.vars[x]? = some lv → lv.ty = .slice mu E →
      x ∈ tenv.visible →
      (x ∈ continuation ∨ ∃ mu, Arg.byRef mu (.var x) ∈ args) → x ∈ future) :
    OuterOk m W.G (callD W tenv env continuation args) (callA W penv env) s := by
  rintro r E (h | ⟨x, lv, si, mu, hx, hl, rfl, hty, hvis, hneeded⟩)
  · obtain ⟨v, h1, h2, h3⟩ := hF.sa r E h
    exact ⟨v, h1, h2, fun t ht => Or.inl ⟨⟨E, h⟩, h3 t ht⟩⟩
  · obtain ⟨lv', si', v, g1, g2, _, g4, g5⟩ :=
      hF.vis x hvis (hdemand x lv mu E hx hty hvis hneeded)
    rw [hx] at g1; cases g1
    rw [hl] at g2; cases g2
    refine ⟨v, g4, by rw [hty] at g5; exact hasTy_slice_mu g5, fun t ht => Or.inr ?_⟩
    obtain ⟨ann, ha, hg⟩ := hF.rooted x lv si v hx hl g4 t ht
    exact ⟨x, lv, si, ann, hx, hl, rfl, ha, hg, hF.inv.age _ v g4 t ht⟩

/-- What the callee may have done to a slice variable, read back in the caller. -/
theorem callD_back (hF : Frame m W tenv penv env s future) :
    ∀ r E, callD W tenv env continuation args r E →
      (W.D r E ∧ ∀ t, callA W penv env r t → W.A r t) ∨
      (∃ x lv si mu, env.vars[x]? = some lv ∧ env.scopes.lookup lv.scope = some si ∧
        r = RootInst.local env.act si x ∧ lv.ty = .slice mu E ∧
        ∀ t, callA W penv env r t → ∃ ann, penv.ann x = some ann ∧ Gam env W.P ann t) := by
  rintro r E (h | ⟨x, lv, si, mu, hx, hl, rfl, hty, _⟩)
  · refine Or.inl ⟨h, ?_⟩
    rintro t (⟨_, g⟩ | ⟨x, lv, si, ann, _, hl, rfl, _⟩)
    · exact g
    · exact absurd ⟨E, h⟩ (hF.not_outer hl)
  · refine Or.inr ⟨x, lv, si, mu, hx, hl, rfl, hty, ?_⟩
    rintro t (⟨g, _⟩ | ⟨x', lv', si', ann, _, _, e, ha, hg, _⟩)
    · exact absurd g (hF.not_outer hl)
    · cases e
      exact ⟨ann, ha, hg⟩

theorem footprint_of_call (_hF : Frame m W tenv penv env s future) {s2 : St}
    (h : Footprint [] (fun r => ∃ E, callD W tenv env continuation args r E) s s2) :
    Footprint (insts env) (Dset W) s s2 := by
  refine h.weaken ?_
  intro r hnd hn
  refine ⟨?_, fun _ _ _ _ h' => by cases h'⟩
  rintro ⟨E, (hd | ⟨x, lv, si, mu, _, hl, rfl, _⟩)⟩
  · exact hnd ⟨E, hd⟩
  · exact hn _ _ _ rfl (lookup_inst hl)

/-- The callee context's content roots, read through the arguments, denote in
the callee what their instantiation denotes in the caller. -/
theorem gam_inst {P : Nat → RootInst → Prop} {ars : List (List RootRef)} {cont inst : List RootRef}
    (hmap : mapResultRoots ars [] cont = .ok inst) (t : RootInst) :
    Gam env P inst t ↔ Gam noEnv (fun j r => Gam env P (ars[j]?.getD []) r) cont t := by
  constructor
  · rintro ⟨q, hq, hrq⟩
    rcases mapResultRoots_sub ars cont [] inst hmap q hq with h | ⟨r', hr', hf⟩
    · cases h
    · cases r' with
      | «local» y => exact hf.elim
      | global g =>
        have e : q = RootRef.global g := hf
        subst e
        exact ⟨.global g, hr', hrq⟩
      | param j =>
        obtain ⟨a, ha, hqa⟩ := hf
        exact ⟨.param j, hr', q, by simpa [ha] using hqa, hrq⟩
  · rintro ⟨q', hq', hrq'⟩
    have hm := (mapResultRoots_ok ars cont [] inst hmap).2 q' hq'
    cases q' with
    | «local» y => exact hm.elim
    | global g => exact ⟨.global g, hm, hrq'⟩
    | param j =>
      obtain ⟨a, ha, hsub⟩ := hm
      obtain ⟨q, hq, hrq⟩ := (hrq' : Gam env P (ars[j]?.getD []) t)
      exact ⟨q, hsub q (by simpa [ha] using hq), hrq⟩

end Goose.Core.Sound
