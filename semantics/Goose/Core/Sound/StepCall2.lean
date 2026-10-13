import Goose.Core.Sound.StepCall
import Goose.Core.Sound.ShrinkBridge
import Goose.Core.Sound.ArgumentRoots
import Goose.Core.Sound.ArgumentRootSyntax

/-!
The steps for a call expression and for entering a callee.
-/

namespace Goose.Core.Sound
open Goose.Core Goose.Proofs.Memory

variable {m : Module} {prof : NumProfile} {n : Nat}

/-- Content roots keep the broad argument interpretation. Owner authority
flows through caller owner roots only into declared owner-reference slots. -/
private def callOwnerP (W : World) (callee : Impl) (env : Env) (ars : List (List RootRef))
    (index : Nat) (root : RootInst) : Prop :=
  OwnerRefParam callee index ∧ Gam env W.ownerP (ars[index]?.getD []) root

private theorem callOwnerP.shape (W : World) (callee : Impl) (env : Env) (ars : List (List RootRef)) :
    OwnerParameterShape callee (callOwnerP W callee env ars) :=
  fun _ _ owner => owner.1

private theorem Frame.callOwnerP_subset {W : World} {tenv : TEnv} {penv : PEnv} {env : Env}
    {s : St} {future : List VarId} (frame : Frame m W tenv penv env s future)
    (callee : Impl) (ars : List (List RootRef)) :
    ∀ index root, callOwnerP W callee env ars index root →
      Gam env W.P (ars[index]?.getD []) root :=
  fun _ _ owner => owner.2.mono frame.ownerSubset

/-- A content root reached through owner authority has the invalidating kind
used by the checked caller's owner request. Current locals get that kind from
the boundary's declared root types, while parameter slots carry owner shape. -/
private theorem Frame.callOwner_invalidates {W : World} {tenv : TEnv} {penv : PEnv} {env : Env}
    {s : St} {future continuation : List VarId} {observation : Observation}
    {retained : List RetainedAlias} {reference : RootRef} {root : RootInst}
    (frame : Frame m W tenv penv env s future)
    (inheritedOlder : ∀ holder type, observation.roots holder type → BeforeBase W.base holder)
    (denotes : RootIn env W.ownerP root reference)
    (capability : OwnerCap m
      (callObservation (m := m) observation W tenv env continuation retained s.store) root) :
    (⟨penv.access.rootType? reference, [reference]⟩ : DemandOwner).invalidates = true := by
  cases reference with
  | param index =>
    obtain ⟨parameter, parameterVariable, parameterAt, _, variableAt, mu, element, grow | shrink⟩ :=
      frame.ownerShape index root denotes
    · simp [DemandOwner.invalidates, AccessEnv.rootType?, PEnv.access,
        parameterAt, variableAt, grow]
    · simp [DemandOwner.invalidates, AccessEnv.rootType?, PEnv.access,
        parameterAt, variableAt, shrink]
  | global global =>
    subst root
    obtain ⟨declaration, declared, element, grow | shrink⟩ := capability
    · simp [DemandOwner.invalidates, AccessEnv.rootType?, PEnv.access,
        frame.mod_p, declared, grow]
    · simp [DemandOwner.invalidates, AccessEnv.rootType?, PEnv.access,
        frame.mod_p, declared, shrink]
  | «local» variableId =>
    obtain ⟨localDeclaration, instanceId, variableAt, scope, rfl⟩ := denotes
    have currentLower : W.base ≤ instanceId := by
      obtain ⟨before, after, equal, _⟩ := List.lookup_eq_some_iff.mp scope
      apply (frame.below (localDeclaration.scope, instanceId) ?_).1
      rw [equal]
      exact List.mem_append_right _ List.mem_cons_self
    have checkedVariable : penv.impl.vars[variableId]? = some localDeclaration := by
      rw [frame.vars_p]
      exact variableAt
    obtain ⟨type, rootObserved, element, kind⟩ := capability
    have declared : type = localDeclaration.ty := by
      rcases rootObserved with inherited | (current | demanded)
      · exact False.elim (Nat.not_lt_of_ge currentLower
          (inheritedOlder _ _ inherited))
      · rcases current with ⟨x, lv, si, _, _, lookup, _, equal, rfl⟩ |
          ⟨⟨x, lv, si, lookup, _, equal, _, rfl⟩, _⟩
        all_goals
          cases equal
          rw [variableAt] at lookup
          cases lookup
          rfl
      · obtain ⟨element, demanded, _⟩ := demanded
        obtain ⟨activation, instanceId', variableId', equal, older⟩ := frame.dOut _ element demanded
        cases equal
        exact False.elim (Nat.not_lt_of_ge currentLower older)
    rw [declared] at kind
    rcases kind with grow | shrink
    · simp [DemandOwner.invalidates, AccessEnv.rootType?, PEnv.access,
        checkedVariable, grow]
    · simp [DemandOwner.invalidates, AccessEnv.rootType?, PEnv.access,
        checkedVariable, shrink]

private theorem initContext_checked (m : Module) : CtxOk m initImpl initContext := by
  constructor
  · simp [checkAnnotationShape, initImpl, initContext, forAll]
    rfl
  · rfl
  · rfl
  · intro i annotation bound
    simp [initImpl] at bound
  · rfl
  · intro x content found
    simp [initContext] at found
  · exact ⟨[], (0, 0), ⟨0, {}⟩, rfl, (by intro impossible; cases impossible), rfl⟩

/-- A call selects the callee body from the same checked plan array as its
caller. Pilot bodies start with parameter activity and require no demand plan. -/
private noncomputable def EvaluationContext.calleeContext {plans path c args origin}
    (caller : EvaluationContext m plans path (.expression (.call c args origin)) .expression)
    {ctx : Context} (impl : Impl) (contextAt : m.contexts[c]? = some ctx)
    (implementationAt : m.impls[ctx.impl]? = some impl) :
    EvaluationContext m plans [] (.block impl.body) .block := by
  cases caller with
  | pilot profile _ => exact .pilot profile (impl.params.toList.map Param.var)
  | @shrink pc profile _ =>
    let selection := PlanContext.forContext pc.derived pc.wellFormed
      (by rw [profile]; intro h; cases h) contextAt impl implementationAt
    exact .shrink profile selection.rootContext

private theorem EvaluationContext.calleeContext_owner {plans path c args origin}
    (caller : EvaluationContext m plans path (.expression (.call c args origin)) .expression)
    {ctx : Context} (impl : Impl) (contextAt : m.contexts[c]? = some ctx)
    (implementationAt : m.impls[ctx.impl]? = some impl) :
    (caller.calleeContext impl contextAt implementationAt).OwnerMatches c := by
  cases caller with
  | pilot profile _ => trivial
  | @shrink pc profile _ =>
    exact (PlanContext.forContext pc.derived pc.wellFormed
      (by rw [profile]; intro h; cases h) contextAt impl implementationAt).ownerEq

/-- Returned call observations restore demanded caller bindings and all
initialized value storage; inherited slice holders use the returned outer facts. -/
private theorem Frame.callObservation_return {W : World} {tenv : TEnv} {penv : PEnv} {env : Env}
    {s s' : St} {future continuation : List VarId} {args : List Arg}
    {retained : List RetainedAlias} {inherited : Observation}
    (frame : Frame m W tenv penv env s future)
    (transition : CallTransition m W.G
      (callObservation (m := m) inherited W tenv env continuation retained s.store).roots
      (callObservation (m := m) inherited W tenv env continuation retained s.store).values
      (fun r => ∃ element, callD W tenv env continuation args r element) s s')
    (invariant : StoreInv m W.G s'
      (ObservationDemand (callObservation (m := m) inherited W tenv env continuation retained s.store)))
    (outer : OuterOk m W.G (callD W tenv env continuation args) (callA W penv env) s')
    (futureSubset : ∀ x, x ∈ continuation → x ∈ future) :
    Frame m W tenv penv env s' continuation := by
  apply frame.outerPreserved transition.footprint
    (transition.rootsTyped.restrict (fun _ _ membership => Or.inr membership))
  · apply invariant.changeDemand
    intro root demanded
    cases root with
    | global _ => exact Or.inl trivial
    | «local» a si x =>
      obtain ⟨rfl, visible, needed, lv, hvar, hscope⟩ := demanded
      exact Or.inl ⟨lv.ty, Or.inr (Or.inl (Or.inl
        ⟨x, lv, si, visible, needed, hvar, hscope, rfl, rfl⟩))⟩
  · exact futureSubset
  · exact outer
  · exact callD_back frame
  · exact fun _ _ hd => Or.inl hd

private theorem callOuterOk_inherited {W : World} {tenv : TEnv} {penv : PEnv} {env : Env}
    {s s' : St} {future continuation : List VarId} {args : List Arg}
    (frame : Frame m W tenv penv env s future)
    (outer : OuterOk m W.G (callD W tenv env continuation args) (callA W penv env) s') :
    OuterOk m W.G W.D W.A s' := by
  intro root element demanded
  obtain ⟨value, present, typed, allowed⟩ := outer root element (Or.inl demanded)
  refine ⟨value, present, typed, ?_⟩
  intro target realized
  rcases allowed target realized with ⟨_, admitted⟩ |
    ⟨x, lv, si, ann, _, scope, rootEq, _⟩
  · exact admitted
  · subst root
    exact False.elim (frame.not_outer scope ⟨element, demanded⟩)

/-- The caller recovers its whole-plan observation safety from returned typing,
its own protection and inherited slice facts. No relation between whole callee
and caller shrink plans is needed on return. -/
private theorem Frame.callBoundary_return {W : World} {tenv : TEnv} {penv : PEnv} {env : Env}
    {s s' : St} {future continuation : List VarId} {args : List Arg}
    {retained parentRetained : List RetainedAlias} {inherited : Observation}
    {shrinking : RootInst → Prop}
    (frame : Frame m W tenv penv env s future)
    (sourceSafe : ObservedSafe m W shrinking inherited s.store)
    (sourceClassified : m.profile = .shrink →
      ClassifiedParameters m W.P W.D inherited s.store)
    (protectedSlices : ShrinkProtected W.D W.A shrinking)
    (transition : CallTransition m W.G
      (callObservation (m := m) inherited W tenv env continuation retained s.store).roots
      (callObservation (m := m) inherited W tenv env continuation retained s.store).values
      (fun r => ∃ element, callD W tenv env continuation args r element) s s')
    (invariant : StoreInv m W.G s'
      (ObservationDemand (callObservation (m := m) inherited W tenv env continuation retained s.store)))
    (outer : OuterOk m W.G (callD W tenv env continuation args) (callA W penv env) s')
    (futureSubset : ∀ x, x ∈ continuation → x ∈ future)
    (retainedSubset : ∀ alias, alias ∈ parentRetained → alias ∈ retained) :
    Frame m W tenv penv env s' continuation ∧
    Footprint (insts env) (Dset W) s s' ∧
    PreservesRootTypes m W.G inherited.roots s.store s'.store ∧
    PreservesValues m W.G inherited.values s.store s'.store ∧
    ObservedSafe m W shrinking inherited s'.store ∧
    RetainsAliases m W env s.store s'.store parentRetained ∧
    (m.profile = .shrink → ClassifiedParameters m W.P W.D inherited s'.store) := by
  have callerFootprint := footprint_of_call frame transition.footprint
  have callerRoots := transition.rootsTyped.restrict (fun _ _ membership => Or.inl membership)
  have callerValues := transition.valuesTyped.restrict (fun _ _ membership => Or.inl membership)
  refine ⟨frame.callObservation_return transition invariant outer futureSubset, callerFootprint,
    callerRoots, callerValues,
    frame.observedSafe_outerPreserved protectedSlices sourceSafe callerFootprint callerRoots
      callerValues (callOuterOk_inherited frame outer),
    (callObservation_retainsAliases transition.valuesTyped).subset retainedSubset, ?_⟩
  intro profile
  exact frame.classifiedParameters_advance (sourceClassified profile) callerFootprint

/-- Caller permissions cover every initialized global the callee's declared
summary may touch, including shrink targets. Unknown callees require all globals. -/
private theorem callPermission {W : World} {env : Env} {callee : Impl} {ctx : Context}
    {ars : List (List RootRef)} {initial : Eff}
    (permission : Perm m W) (contextChecked : CtxOk m callee ctx)
    (effects : EffLe (callEffects callee ctx ars initial) W.E) :
    m.globals.size ≤ W.G ∨
      SumOk W.G (fun i root => Gam env W.P (ars[i]?.getD []) root) callee ctx := by
  rcases permission with initialized | ⟨known, targetsAllowed⟩
  · exact Or.inl initialized
  · right
    have charged := callEffects_ok callee ctx ars initial
    cases summary : callee.summary with
    | unknown =>
      rw [summary] at charged
      have unknown := effects.2.2.2.2 charged.1
      rw [known] at unknown
      cases unknown
    | known sm =>
      rw [summary] at charged
      obtain ⟨reads, writes, grows⟩ := charged
      obtain ⟨_, _, state, _, _, summaryChecked⟩ := contextChecked.body
      obtain ⟨_, _, _, _, parameterBounds⟩ :=
        checkSummary_ok m callee ctx state.eff summaryChecked sm summary
      have shrinkBounds := checkSummary_shrinkParams_ok m callee ctx state.eff
        summaryChecked sm summary
      refine ⟨sm, summary, ?_⟩
      intro target request
      rcases request with read | write | grow | shrink
      · exact expand_ok (env := env) (P := W.P) (fun _ _ denoted => denoted)
          contextChecked sm.reads (fun i member => parameterBounds i (Or.inl member))
          (fun t member => targetsAllowed t (Or.inl (effects.1 t (reads t member)))) target read
      · exact expand_ok (env := env) (P := W.P) (fun _ _ denoted => denoted)
          contextChecked sm.writes (fun i member => parameterBounds i (Or.inr (Or.inl member)))
          (fun t member => targetsAllowed t (Or.inr (Or.inl
            (effects.2.1 t (writes t member))))) target write
      · exact expand_ok (env := env) (P := W.P) (fun _ _ denoted => denoted)
          contextChecked sm.grows (fun i member => parameterBounds i (Or.inr (Or.inr member)))
          (fun t member => targetsAllowed t (Or.inr (Or.inr (Or.inl
            (effects.2.2.1 t (grows t member)))))) target grow
      · exact expand_ok (env := env) (P := W.P) (fun _ _ denoted => denoted)
          contextChecked sm.shrinks shrinkBounds
          (fun t member => targetsAllowed t (Or.inr (Or.inr (Or.inr
            (effects.2.2.2.1 t
              (callShrinkTargets_ok callee ctx ars initial sm summary t member)))))) target shrink

/-- Effect permission initializes every declared owner global it may shrink. -/
private theorem callGlobal_initialized {W : World} {observation : Observation} {global : GlobalId}
    (permission : Perm m W) (capability : OwnerCap m observation (.global global))
    (shrinking : MayShrinkEff W.P W.E (.global global)) : global < W.G := by
  rcases permission with initialized | ⟨known, allowed⟩
  · obtain ⟨declaration, declared, _⟩ := capability
    exact Nat.lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp declared).1 initialized
  · obtain ⟨target, explicit | unknown, denotes⟩ := shrinking
    · have targetAllowed := allowed target (Or.inr (Or.inr (Or.inr explicit)))
      cases target with
      | global targetGlobal =>
        change RootInst.global global = RootInst.global targetGlobal at denotes
        cases denotes
        exact targetAllowed
      | param parameter => exact targetAllowed _ denotes global rfl
    · rw [known] at unknown
      cases unknown

/-- The checked context interprets each sampled argument in the broad callee
parameter relation. Extra declared roots remain available for result typing. -/
private theorem callValues_ok {W : World} {env : Env} {store : Store} {callee : Impl} {ctx : Context}
    {ars : List (List RootRef)} {vals : List Val}
    (implementationChecked : ImplOk m callee) (contextChecked : CtxOk m callee ctx)
    (argumentsChecked : ∀ i, i < callee.params.size → checkArgRoots callee ctx ars i = .ok ())
    (sampled : ∀ (i : Nat) (value : Val), vals[i]? = some value →
      ∃ (p : Param) (pv : LocalVar) (ar : List RootRef),
      callee.params.toList[i]? = some p ∧ callee.vars[p.var]? = some pv ∧
      ars[i]? = some ar ∧ HasTy m W.G store value pv.ty ∧
      ∀ root, Targets value root → Gam env W.P ar root) :
    ∀ i value, vals[i]? = some value → ∃ lv,
      callee.vars[i]? = some lv ∧ HasTy m W.G store value lv.ty ∧
      ∀ root, Targets value root → ∃ annotation,
        (ctx.varRoots.find? (·.1 == i)).map (·.2) = some annotation ∧
        Gam noEnv (fun j root => Gam env W.P (ars[j]?.getD []) root) annotation root := by
  intro i value valueAt
  obtain ⟨p, pv, ar, parameterAt, variableAt, rootsAt, typed, targets⟩ := sampled i value valueAt
  have parameterArray : callee.params[i]? = some p := by simpa using parameterAt
  have bound : i < callee.params.size := (Array.getElem?_eq_some_iff.1 parameterArray).1
  obtain ⟨variableEq, _⟩ := implementationChecked.params i p parameterArray
  rw [variableEq] at variableAt
  refine ⟨pv, variableAt, typed, ?_⟩
  intro root target
  have refLike : pv.ty.isRefLike = true := by
    cases typeRef : pv.ty.isRefLike with
    | true => rfl
    | false => exact False.elim (typed.not_ref typeRef target.isRef)
  obtain ⟨other, otherVariable, annotationCheck⟩ :=
    checkArgRoots_ok callee ctx ars i p (argumentsChecked i bound) parameterArray
  rw [variableEq, variableAt] at otherVariable
  cases otherVariable
  obtain ⟨annotation, annotationAt, annotationCase⟩ := annotationCheck refLike
  rw [variableEq] at annotationAt
  refine ⟨annotation, annotationAt, ?_⟩
  have actual := targets root target
  have parameter : Gam env W.P (ars[i]?.getD []) root := by rw [rootsAt]; exact actual
  rcases annotationCase with rfl | included
  · exact ⟨.param i, by simp, parameter⟩
  · obtain ⟨q, member, denoted⟩ := actual
    have declared : q ∈ annotation := included q (by rw [rootsAt]; exact member)
    rcases contextChecked.paramAnn i annotation bound annotationAt q declared with equal |
      ⟨global, equal⟩
    · subst q
      exact ⟨.param i, declared, parameter⟩
    · subst q
      exact ⟨.global global, declared, denoted⟩

/-- Actual owner-reference arguments populate only owner-capable parameter
slots. Ordinary content annotations continue to use the broad interpretation. -/
private theorem callValues_ownerRooted {W : World} {env : Env} {callee : Impl}
    {ars : List (List RootRef)} {vals : List Val}
    (implementationChecked : ImplOk m callee)
    (sampled : ∀ (index : Nat) (value : Val), vals[index]? = some value →
      ∃ (parameter : Param) (declaration : LocalVar) (roots : List RootRef),
        callee.params.toList[index]? = some parameter ∧
        callee.vars[parameter.var]? = some declaration ∧ ars[index]? = some roots ∧
        OwnerRooted env W.ownerP roots value declaration.ty) :
    ∀ index value declaration, vals[index]? = some value →
      callee.vars[index]? = some declaration → OwnerRefParam callee index →
      OwnerRooted noEnv (callOwnerP W callee env ars) [.param index] value declaration.ty := by
  intro index value declaration valueAt variableAt ownerSlot ownerType root targeted
  obtain ⟨parameter, actualVariable, roots, parameterAt, actualAt, rootsAt, rooted⟩ :=
    sampled index value valueAt
  have parameterArray : callee.params[index]? = some parameter := by simpa using parameterAt
  obtain ⟨parameterId, _⟩ := implementationChecked.params index parameter parameterArray
  rw [parameterId, variableAt] at actualAt
  cases actualAt
  refine ⟨.param index, by simp, ownerSlot, ?_⟩
  rw [rootsAt]
  exact rooted ownerType root targeted

/-- A returned callee value uses the declared result roots instantiated with
all argument annotations, including their harmless extra roots. -/
private theorem callResult_ok {W : World} {env : Env} {store : Store} {callee : Impl} {ctx : Context}
    {ars : List (List RootRef)} {rho : List RootRef} {value : Val} {ty : Ty}
    (resultType : (callee.results.toList = [] ∧ ty = .unit) ∨ callee.results.toList = [ty])
    (resultReplay : callResultRoots callee ctx ars = .ok rho)
    (returned : (callee.results.toList = [] ∧ value = .unit) ∨
      ∃ T, callee.results.toList = [T] ∧ HasTy m W.G store value T)
    (declaredRoots : ∀ root, Targets value root → ∃ declared,
      ctx.resultRoots = [declared] ∧
      Gam noEnv (fun j root => Gam env W.P (ars[j]?.getD []) root) declared root) :
    HasTy m W.G store value ty ∧ ∀ root, Targets value root → Gam env W.P rho root := by
  have typed : HasTy m W.G store value ty := by
    rcases resultType with ⟨empty, rfl⟩ | single
    · rcases returned with ⟨_, rfl⟩ | ⟨T, single, _⟩
      · rfl
      · rw [empty] at single
        cases single
    · rcases returned with ⟨empty, _⟩ | ⟨T, other, typed⟩
      · rw [single] at empty
        cases empty
      · rw [single] at other
        cases other
        exact typed
  refine ⟨typed, ?_⟩
  intro root target
  obtain ⟨declared, resultAt, denoted⟩ := declaredRoots root target
  rcases returned with ⟨_, rfl⟩ | ⟨T, resultTypes, typed⟩
  · exact False.elim target
  · have refLike : T.isRefLike = true := by
      cases htype : T.isRefLike with
      | true => rfl
      | false => exact False.elim (typed.not_ref htype target.isRef)
    have mapped : mapResultRoots ars [] declared = .ok rho := by
      simpa only [callResultRoots, resultTypes, resultAt, refLike, ite_true] using resultReplay
    exact (gam_inst mapped root).mpr denoted

/-- Declared owner-reference results map through the filtered owner arguments;
their broader content annotations remain available to ordinary result typing. -/
private theorem callResult_ownerRooted {W : World} {env : Env} {callee : Impl} {ctx : Context}
    {ars : List (List RootRef)} {value : Val} {type : Ty} {rho : List RootRef}
    (resultType : (callee.results.toList = [] ∧ type = .unit) ∨ callee.results.toList = [type])
    (resultReplay : callResultRoots callee ctx ars = .ok rho)
    (returned : OwnerRefTy type → ∀ root, Targets value root →
      ∃ declared, ctx.resultRoots = [declared] ∧
        Gam noEnv (callOwnerP W callee env ars) declared root) :
    OwnerRooted env W.ownerP rho value type := by
  intro ownerType root targeted
  have reference : type.isRefLike = true := by
    obtain ⟨mu, element, rfl | rfl⟩ := ownerType <;> rfl
  have singleton : callee.results.toList = [type] := by
    rcases resultType with ⟨_, unit⟩ | singleton
    · rw [unit] at ownerType
      obtain ⟨mu, element, impossible | impossible⟩ := ownerType <;> cases impossible
    · exact singleton
  obtain ⟨declared, declaredAt, denoted⟩ := returned ownerType root targeted
  have mapped : mapResultRoots ars [] declared = .ok rho := by
    simpa only [callResultRoots, singleton, declaredAt, reference, ite_true] using resultReplay
  exact (gam_inst mapped root).mpr (denoted.mono (fun _ _ owner => owner.2))

/-- Deterministic replay identifies the supplied body effect with the effect
validated by this context. -/
private theorem ContextEff.checkedSummary {callee : Impl} {ctx : Context} {E : Eff}
    (checked : CtxOk m callee ctx) (effect : ContextEff m callee ctx E) :
    checkSummary m callee ctx E = .ok () := by
  obtain ⟨roots, range, state, replay, _, summary⟩ := checked.body
  obtain ⟨otherRoots, otherRange, otherState, otherReplay, equal⟩ := effect
  rw [replay] at otherReplay
  have stateEqual := (Prod.mk.inj (Except.ok.inj otherReplay)).2
  cases stateEqual
  subst E
  exact summary

private theorem checkSummary_mutations {callee : Impl} {ctx : Context} {E : Eff}
    {summary : Summary} (checked : checkSummary m callee ctx E = .ok ())
    (known : callee.summary = .known summary) :
    E.unknown = false ∧
    (∀ target, target ∈ E.writes → target ∈ expandTargets callee ctx summary.writes) ∧
    (∀ target, target ∈ E.grows → target ∈ expandTargets callee ctx summary.grows) ∧
    (∀ target, target ∈ E.shrinks → target ∈ expandTargets callee ctx summary.shrinks) ∧
    (∀ target, target ∈ E.rebinds → target ∈ summary.rebinds) ∧
    (∀ index, (Target.param index ∈ summary.writes ∨
      Target.param index ∈ summary.grows ∨ Target.param index ∈ summary.shrinks ∨
      Target.param index ∈ summary.rebinds) → index < callee.params.size) := by
  unfold checkSummary at checked
  simp only [known] at checked
  inv at checked
  obtain ⟨_, writes, grows, shrinks, rebinds, notUnknown, _, foundWrites, foundGrows,
    foundShrinks, foundRebinds, _, _⟩ := checked
  refine ⟨by simpa using notUnknown, effWithin_ok _ _ _ _ foundWrites,
    effWithin_ok _ _ _ _ foundGrows, effWithin_ok _ _ _ _ foundShrinks,
    effWithin_ok _ _ _ _ foundRebinds, ?_⟩
  intro index member
  rcases member with write | grow | shrink | rebind
  · exact checkSummaryTargets_param_ok m callee "writes" summary.writes writes index write
  · exact checkSummaryTargets_param_ok m callee "grows" summary.grows grows index grow
  · exact checkSummaryTargets_param_ok m callee "shrinks" summary.shrinks shrinks index shrink
  · exact checkSummaryTargets_param_ok m callee "rebinds" summary.rebinds rebinds index rebind

private theorem effectMutationRoots_of_target (impl : Impl) (E : Eff) (target : Target)
    (member : target ∈ effectMutationTargets E) :
    effectTargetRoot target ∈ effectMutationRoots m impl E := by
  have mapped : effectTargetRoot target ∈ effectTargetRoots (effectMutationTargets E) :=
    List.mem_map.mpr ⟨target, member, rfl⟩
  unfold effectMutationRoots
  split
  · exact List.mem_append_left _ mapped
  · exact mapped

private theorem callEffects_mutations {callee : Impl} {ctx : Context}
    {ars : List (List RootRef)} {initial : Eff} {summary : Summary}
    (known : callee.summary = .known summary) :
    ∀ target, (target ∈ mapCallTargets callee ctx ars summary.writes ∨
      target ∈ mapCallTargets callee ctx ars summary.grows ∨
      target ∈ mapCallTargets callee ctx ars summary.shrinks ∨
      target ∈ mapCallTargets callee ctx ars summary.rebinds) →
      target ∈ effectMutationTargets (callEffects callee ctx ars initial) := by
  intro target member
  simp only [callEffects, known, effectMutationTargets, List.mem_append]
  rcases member with write | grow | shrink | rebind
  · exact Or.inl (Or.inl (Or.inl (addTargets_right _ _ target write)))
  · exact Or.inl (Or.inl (Or.inr (addTargets_right _ _ target grow)))
  · exact Or.inl (Or.inr (addTargets_right _ _ target shrink))
  · exact Or.inr (addTargets_right _ _ target rebind)

/-- Argument roots belonging to the caller's current activation are already
inside its mutation budget. External roots must be charged by the call replay. -/
private theorem Frame.callArgumentMutationRoot {W : World} {tenv : TEnv} {penv : PEnv}
    {env : Env} {s : St} {future : List VarId} {callee : Impl} {ctx : Context}
    {ars : List (List RootRef)} {targets : List Target} {callerRoots : List RootRef}
    {index : Nat} {root : RootInst}
    (frame : Frame m W tenv penv env s future)
    (parameter : Target.param index ∈ targets)
    (charged : ∀ target, target ∈ mapCallTargets callee ctx ars targets →
      effectTargetRoot target ∈ callerRoots)
    (argument : Gam env W.P (ars[index]?.getD []) root) :
    MutationRoots env W.P W.base callerRoots root := by
  obtain ⟨reference, member, denotes⟩ := argument
  cases reference with
  | «local» variableId =>
    obtain ⟨lv, instanceId, _, scope, rootEq⟩ := denotes
    obtain ⟨before, after, scopesEq, _⟩ := List.lookup_eq_some_iff.mp scope
    have scopeMember : (lv.scope, instanceId) ∈ env.scopes := by
      rw [scopesEq]
      exact List.mem_append_right _ List.mem_cons_self
    exact Or.inr ⟨env.act, instanceId, variableId, rootEq, (frame.below _ scopeMember).1⟩
  | global global =>
    exact Or.inl ⟨.global global, charged (.global global)
      (mapCall_param callee ctx ars targets index parameter _
        (Or.inl (mem_rootsTargets_global member))), denotes⟩
  | param callerIndex =>
    exact Or.inl ⟨.param callerIndex, charged (.param callerIndex)
      (mapCall_param callee ctx ars targets index parameter _
        (Or.inl (mem_rootsTargets_param member))), denotes⟩

private theorem callTargetMutationRoot {W : World} {tenv : TEnv} {penv : PEnv} {env : Env}
    {s : St} {future : List VarId} {callee : Impl} {ctx : Context}
    {ars : List (List RootRef)} {targets : List Target} {callerRoots : List RootRef}
    {target : Target} {root : RootInst}
    (frame : Frame m W tenv penv env s future) (member : target ∈ targets)
    (charged : ∀ target, target ∈ mapCallTargets callee ctx ars targets →
      effectTargetRoot target ∈ callerRoots)
    (denotes : RootIn noEnv (fun index root => Gam env W.P (ars[index]?.getD []) root)
      root (effectTargetRoot target)) :
    MutationRoots env W.P W.base callerRoots root := by
  cases target with
  | global global =>
    exact Or.inl ⟨.global global,
      charged (.global global) (mapCall_global callee ctx ars targets global member), denotes⟩
  | param index => exact frame.callArgumentMutationRoot member charged denotes

/-- Expansion may replace a formal effect with its checked annotation. The
call charges that annotation's globals and its actual argument roots. -/
private theorem callExpandedMutationRoot {W : World} {tenv : TEnv} {penv : PEnv} {env : Env}
    {s : St} {future : List VarId} {callee : Impl} {ctx : Context}
    {ars : List (List RootRef)} {targets : List Target} {callerRoots : List RootRef}
    {target : Target} {root : RootInst}
    (frame : Frame m W tenv penv env s future) (checked : CtxOk m callee ctx)
    (parameters : ∀ index, Target.param index ∈ targets → index < callee.params.size)
    (charged : ∀ target, target ∈ mapCallTargets callee ctx ars targets →
      effectTargetRoot target ∈ callerRoots)
    (member : target ∈ expandTargets callee ctx targets)
    (denotes : RootIn noEnv (fun index root => Gam env W.P (ars[index]?.getD []) root)
      root (effectTargetRoot target)) :
    MutationRoots env W.P W.base callerRoots root := by
  simp only [expandTargets, List.mem_flatMap] at member
  obtain ⟨declared, declaredMember, expandedMember⟩ := member
  cases declared with
  | global global =>
    simp only [List.mem_singleton] at expandedMember
    subst target
    exact callTargetMutationRoot frame declaredMember charged denotes
  | param index =>
    have formal : RootIn noEnv
        (fun index root => Gam env W.P (ars[index]?.getD []) root)
        root (.param index) → MutationRoots env W.P W.base callerRoots root :=
      frame.callArgumentMutationRoot declaredMember charged
    cases variableAt : callee.vars[index]? with
    | none =>
      simp only [variableAt, List.mem_singleton] at expandedMember
      subst target
      exact formal denotes
    | some lv =>
      cases annotationAt : ctx.varRoots.find? (·.1 == index) with
      | none =>
        simp only [variableAt, annotationAt, List.mem_singleton] at expandedMember
        subst target
        exact formal denotes
      | some pair =>
        obtain ⟨variableId, roots⟩ := pair
        by_cases referenceType : lv.ty.isRefLike = true
        · simp only [variableAt, annotationAt, referenceType, if_true,
            rootsTargets, List.mem_filterMap] at expandedMember
          obtain ⟨reference, rootMember, targetEq⟩ := expandedMember
          cases reference with
          | «local» _ => simp [rootTarget] at targetEq
          | global global =>
            simp only [rootTarget, Option.some.injEq] at targetEq
            subst target
            have globalMember : Target.global global ∈ paramGlobals callee ctx index := by
              simp only [paramGlobals, variableAt, annotationAt, referenceType,
                if_true, List.mem_filterMap]
              exact ⟨.global global, rootMember, rfl⟩
            exact Or.inl ⟨.global global,
              charged (.global global) (mapCall_param callee ctx ars targets index
                declaredMember _ (Or.inr globalMember)), denotes⟩
          | param actualIndex =>
            simp only [rootTarget, Option.some.injEq] at targetEq
            subst target
            rcases checked.paramAnn index roots (parameters index declaredMember)
              (by simp [annotationAt]) (.param actualIndex) rootMember with equal | ⟨_, equal⟩
            · cases equal
              exact formal denotes
            · cases equal
        · simp only [variableAt, annotationAt, referenceType, Bool.false_eq_true,
            if_false, List.mem_singleton] at expandedMember
          subst target
          exact formal denotes

/-- A checked known summary charges every externally interpreted body
mutation; caller-local argument roots are covered by the caller's scope budget. -/
private theorem callKnownMutationRoot {W : World} {tenv : TEnv} {penv : PEnv} {env : Env}
    {s : St} {future : List VarId} {callee : Impl} {ctx : Context} {E initial : Eff}
    {ars : List (List RootRef)} {summary : Summary} {root : RootInst}
    (frame : Frame m W tenv penv env s future) (checked : CtxOk m callee ctx)
    (effect : ContextEff m callee ctx E) (known : callee.summary = .known summary)
    (denoted : Gam noEnv (fun index root => Gam env W.P (ars[index]?.getD []) root)
      (effectMutationRoots m callee E) root) :
    MutationRoots env W.P W.base
      (effectMutationRoots m penv.impl (callEffects callee ctx ars initial)) root := by
  obtain ⟨notUnknown, writes, grows, shrinks, rebinds, parameters⟩ :=
    checkSummary_mutations (effect.checkedSummary checked) known
  obtain ⟨reference, member, realization⟩ := denoted
  simp only [effectMutationRoots, notUnknown, Bool.false_eq_true, if_false,
    effectTargetRoots, List.mem_map] at member
  obtain ⟨target, targetMember, rfl⟩ := member
  simp only [effectMutationTargets, List.mem_append] at targetMember
  rcases targetMember with ((write | grow) | shrink) | rebind
  · apply callExpandedMutationRoot frame checked
      (fun index member => parameters index (Or.inl member))
      (fun target member => effectMutationRoots_of_target penv.impl _ target
        (callEffects_mutations known target (Or.inl member))) (writes target write) realization
  · apply callExpandedMutationRoot frame checked
      (fun index member => parameters index (Or.inr (Or.inl member)))
      (fun target member => effectMutationRoots_of_target penv.impl _ target
        (callEffects_mutations known target (Or.inr (Or.inl member)))) (grows target grow) realization
  · apply callExpandedMutationRoot frame checked
      (fun index member => parameters index (Or.inr (Or.inr (Or.inl member))))
      (fun target member => effectMutationRoots_of_target penv.impl _ target
        (callEffects_mutations known target (Or.inr (Or.inr (Or.inl member)))))
      (shrinks target shrink) realization
  · exact callTargetMutationRoot frame (rebinds target rebind)
      (fun target member => effectMutationRoots_of_target penv.impl _ target
        (callEffects_mutations known target (Or.inr (Or.inr (Or.inr member))))) realization

private theorem effectMutationRoots_globalIndex {impl : Impl} {E : Eff} {global : Nat}
    (globals : ∀ index, Target.global index ∈ effectMutationTargets E → index < m.globals.size)
    (member : RootRef.global global ∈ effectMutationRoots m impl E) : global < m.globals.size := by
  have knownBound : RootRef.global global ∈ effectTargetRoots (effectMutationTargets E) →
      global < m.globals.size := by
    intro knownMember
    obtain ⟨target, targetMember, targetEq⟩ := List.mem_map.mp knownMember
    cases target with
    | global index =>
      have equal : index = global := RootRef.global.inj targetEq
      subst index
      exact globals global targetMember
    | param _ => cases targetEq
  unfold effectMutationRoots at member
  split at member
  · rcases List.mem_append.mp member with knownMember | declared
    · exact knownBound knownMember
    · rcases List.mem_append.mp declared with declaredGlobal | declaredParameter
      · obtain ⟨index, indexMember, equal⟩ := List.mem_map.mp declaredGlobal
        cases equal
        exact List.mem_range.mp indexMember
      · obtain ⟨_, _, impossible⟩ := List.mem_map.mp declaredParameter
        cases impossible
  · exact knownBound member

/-- Unknown calls explicitly charge their actual argument roots. This also
covers harmless unchecked annotations in the generic pilot frame. -/
private theorem callUnknownArgumentMutationRoot {W : World} {tenv : TEnv} {penv : PEnv}
    {env : Env} {s : St} {future : List VarId} {callee : Impl} {ctx : Context}
    {ars : List (List RootRef)} {initial : Eff} {index : Nat} {root : RootInst}
    (frame : Frame m W tenv penv env s future) (unknown : callee.summary = .unknown)
    (argument : Gam env W.P (ars[index]?.getD []) root) :
    MutationRoots env W.P W.base
      (effectMutationRoots m penv.impl (callEffects callee ctx ars initial)) root := by
  have charged := callEffects_ok callee ctx ars initial
  rw [unknown] at charged
  obtain ⟨reference, member, denotes⟩ := argument
  have flattened : reference ∈ ars.flatten := by
    cases rootsAt : ars[index]? with
    | none => simp [rootsAt] at member
    | some roots =>
      exact List.mem_flatten.mpr ⟨roots, List.mem_of_getElem? rootsAt, by simpa [rootsAt] using member⟩
  have chargeTarget : ∀ target, target ∈ rootsTargets ars.flatten →
      effectTargetRoot target ∈ effectMutationRoots m penv.impl (callEffects callee ctx ars initial) := by
    intro target targetMember
    exact effectMutationRoots_of_target penv.impl _ target
      (by
        simp only [effectMutationTargets, List.mem_append]
        exact Or.inl (Or.inl (Or.inl (charged.2 target targetMember))))
  cases reference with
  | «local» variableId =>
    obtain ⟨lv, instanceId, _, scope, equal⟩ := denotes
    obtain ⟨before, after, scopesEq, _⟩ := List.lookup_eq_some_iff.mp scope
    have scopeMember : (lv.scope, instanceId) ∈ env.scopes := by
      rw [scopesEq]
      exact List.mem_append_right _ List.mem_cons_self
    exact Or.inr ⟨env.act, instanceId, variableId, equal, (frame.below _ scopeMember).1⟩
  | global global =>
    exact Or.inl ⟨.global global, chargeTarget (.global global)
      (mem_rootsTargets_global flattened), denotes⟩
  | param callerIndex =>
    exact Or.inl ⟨.param callerIndex, chargeTarget (.param callerIndex)
      (mem_rootsTargets_param flattened), denotes⟩

private theorem callUnknownMutationRoot {W : World} {tenv : TEnv} {penv : PEnv} {env : Env}
    {s : St} {future : List VarId} {callee : Impl} {ctx : Context} {E initial : Eff}
    {ars : List (List RootRef)} {root : RootInst}
    (frame : Frame m W tenv penv env s future) (unknown : callee.summary = .unknown)
    (globals : ∀ index, Target.global index ∈ effectMutationTargets E → index < m.globals.size)
    (denoted : Gam noEnv (fun index root => Gam env W.P (ars[index]?.getD []) root)
      (effectMutationRoots m callee E) root) :
    MutationRoots env W.P W.base
      (effectMutationRoots m penv.impl (callEffects callee ctx ars initial)) root := by
  obtain ⟨reference, member, denotes⟩ := denoted
  cases reference with
  | «local» variableId =>
    obtain ⟨_, _, variableAt, _⟩ := denotes
    simp [noEnv] at variableAt
  | param index => exact callUnknownArgumentMutationRoot frame unknown denotes
  | global global =>
    have bound := effectMutationRoots_globalIndex globals member
    have unknownEffect : (callEffects callee ctx ars initial).unknown = true := by
      simp [callEffects, unknown]
    refine Or.inl ⟨.global global, ?_, denotes⟩
    simp only [effectMutationRoots, unknownEffect, if_true, List.mem_append]
    exact Or.inr (Or.inl (List.mem_map.mpr ⟨global, List.mem_range.mpr bound, rfl⟩))

private theorem callMutationRoot {W : World} {tenv : TEnv} {penv : PEnv} {env : Env}
    {s : St} {future : List VarId} {callee : Impl} {ctx : Context} {E initial : Eff}
    {ars : List (List RootRef)} {root : RootInst}
    (frame : Frame m W tenv penv env s future) (moduleOk : ModOk m)
    (implementationOk : ImplOk m callee) (contextOk : CtxOk m callee ctx)
    (contextEffect : ContextEff m callee ctx E)
    (denoted : Gam noEnv (fun index root => Gam env W.P (ars[index]?.getD []) root)
      (effectMutationRoots m callee E) root) :
    MutationRoots env W.P W.base
      (effectMutationRoots m penv.impl (callEffects callee ctx ars initial)) root := by
  cases summaryAt : callee.summary with
  | known summary => exact callKnownMutationRoot frame contextOk contextEffect summaryAt denoted
  | unknown =>
    exact callUnknownMutationRoot frame summaryAt
      (fun _ member => contextEffect.mutationGlobalIndex moduleOk implementationOk contextOk member) denoted

/-- Returning from a call keeps its entry allocations inside the caller's
earlier allocation budget and maps all external body roots through its arguments. -/
private theorem callMutationFootprint_caller {W : World} {tenv : TEnv} {penv : PEnv}
    {env : Env} {s s' : St} {future : List VarId} {ars : List (List RootRef)}
    {bodyRoots callerRoots : List RootRef}
    (frame : Frame m W tenv penv env s future)
    (footprint : MutationFootprint noEnv
      (fun index root => Gam env W.P (ars[index]?.getD []) root)
      s.nextScope bodyRoots s s')
    (included : ∀ root, Gam noEnv
      (fun index root => Gam env W.P (ars[index]?.getD []) root) bodyRoots root →
      MutationRoots env W.P W.base callerRoots root) :
    MutationFootprint env W.P W.base callerRoots s s' := by
  intro root outside
  apply footprint root
  rintro (external | ⟨act, instanceId, variableId, equal, allocated⟩)
  · exact outside (included root external)
  · exact outside (Or.inr ⟨act, instanceId, variableId, equal,
      Nat.le_trans frame.base_le allocated⟩)

private theorem callMutationFootprints_compose {W : World} {tenv : TEnv} {penv : PEnv}
    {env : Env} {s s1 s2 : St} {future : List VarId} {callee : Impl}
    {ars : List (List RootRef)} {argumentEffects bodyEffects finalEffects : Eff}
    (frame : Frame m W tenv penv env s1 future)
    (arguments : MutationFootprint env W.P W.base
      (effectMutationRoots m penv.impl argumentEffects) s s1)
    (body : MutationFootprint noEnv
      (fun index root => Gam env W.P (ars[index]?.getD []) root)
      s1.nextScope (effectMutationRoots m callee bodyEffects) s1 s2)
    (argumentEffectsLe : EffLe argumentEffects finalEffects)
    (argumentRebindsLe : RebindsLe argumentEffects finalEffects)
    (bodyIncluded : ∀ root, Gam noEnv
      (fun index root => Gam env W.P (ars[index]?.getD []) root)
      (effectMutationRoots m callee bodyEffects) root →
      MutationRoots env W.P W.base (effectMutationRoots m penv.impl finalEffects) root) :
    MutationFootprint env W.P W.base
      (effectMutationRoots m penv.impl finalEffects) s s2 :=
  (arguments.weaken (effectMutationRoots.mono m penv.impl argumentEffectsLe argumentRebindsLe)).trans
    (callMutationFootprint_caller frame body bodyIncluded)

private theorem demandSourceReplay {root node : DemandNode} {path : List Nat}
    (source : DemandNodeAt root path node) (env : PEnv) (before after : RState)
    (replay : ∃ output, rpDemandNode env root before = .ok (output, after)) :
    ∃ leafEnv leafBefore leafAfter output,
      leafEnv.mod = env.mod ∧ leafEnv.impl = env.impl ∧ leafEnv.ctx = env.ctx ∧
      rpDemandNode leafEnv node leafBefore = .ok (output, leafAfter) ∧ RLe leafAfter after := by
  induction source generalizing env before after with
  | here current =>
    obtain ⟨output, replay⟩ := replay
    exact ⟨env, before, after, output, rfl, rfl, rfl, replay, RLe.refl _⟩
  | @child parent current target index path childAt source ih =>
    obtain ⟨_, _, _, childEnv, childBefore, childAfter, childOutput,
      childMod, childImpl, childCtx, childReplay, childLe⟩ :=
      rpDemandNode_child env parent index current before after childAt replay
    obtain ⟨leafEnv, leafBefore, leafAfter, output, leafMod, leafImpl, leafCtx,
      leafReplay, leafLe⟩ := ih childEnv childBefore childAfter ⟨childOutput, childReplay⟩
    exact ⟨leafEnv, leafBefore, leafAfter, output, leafMod.trans childMod,
      leafImpl.trans childImpl, leafCtx.trans childCtx, leafReplay, leafLe.trans childLe⟩

private theorem DemandExpectedSourceAt.call_block_replay
    {owner : Nat} {path : List Nat} {expected : DemandExpectedPoint}
    {block : Block} {context : ContextId} {args : List Arg} {origin : OriginId}
    (sourceAt : DemandExpectedSourceAt m owner path
      (.expression (.call context args origin)) .mutation expected)
    (root : demandRoot? m owner = some (.block block))
    (env : PEnv) (before after : RState) (roots : List RootRef) (range : Nat × Nat)
    (replay : rpBlockValue env [] block before = .ok ((roots, range), after)) :
    ∃ leafEnv leafBefore leafAfter output,
      leafEnv.mod = env.mod ∧ leafEnv.impl = env.impl ∧ leafEnv.ctx = env.ctx ∧
      rpExpr leafEnv (.call context args origin) leafBefore = .ok (output, leafAfter) ∧
      RLe leafAfter after := by
  obtain ⟨sourceRoot, rootAt, source⟩ := sourceAt.sourceFacts.1
  have equal : sourceRoot = .block block := Option.some.inj (rootAt.symm.trans root)
  subst sourceRoot
  obtain ⟨leafEnv, leafBefore, leafAfter, output, leafMod, leafImpl, leafCtx,
    leafReplay, leafLe⟩ := demandSourceReplay source env before after
      ⟨(roots, range), by simpa only [rpDemandNode, DemandNode.replayOutput] using replay⟩
  exact ⟨leafEnv, leafBefore, leafAfter, output, leafMod, leafImpl, leafCtx,
    by simpa only [rpDemandNode, DemandNode.replayOutput] using leafReplay, leafLe⟩

private theorem forIn_ownerInvariant {α : Type} (items : List α)
    (step : α → List DemandOwner → V (ForInStep (List DemandOwner)))
    (property : DemandOwner → Prop)
    (preserve : ∀ item, item ∈ items → ∀ previous following,
      (∀ owner, owner ∈ previous → property owner) → step item previous = .ok following →
      ∃ next, following = .yield next ∧ ∀ owner, owner ∈ next → property owner)
    {previous following : List DemandOwner}
    (initial : ∀ owner, owner ∈ previous → property owner)
    (checked : forIn items previous step = .ok following) :
    ∀ owner, owner ∈ following → property owner := by
  induction items generalizing previous with
  | nil =>
    simp only [List.forIn_nil, ex_pure_ok] at checked
    subst following
    exact initial
  | cons item rest ih =>
    simp only [List.forIn_cons] at checked
    obtain ⟨control, head, tail⟩ := (ex_bind_ok _ _ _).mp checked
    obtain ⟨next, controlEq, invariant⟩ := preserve item (by simp) previous control initial head
    apply ih (fun item member => preserve item (List.mem_cons_of_mem _ member)) invariant
    simpa only [controlEq] using tail

private theorem AccessEnv.targetOwners_recorded (access : AccessEnv) (callee : Impl)
    (ctx : Context) (actual : List (List RootRef)) (targets : List Target)
    (owners : List DemandOwner) (checked : access.targetOwners callee ctx actual targets = .ok owners) :
    ∀ owner, owner ∈ owners → ∀ target, target ∈ rootsTargets owner.roots →
      target ∈ mapCallTargets callee ctx actual targets := by
  unfold AccessEnv.targetOwners at checked
  obtain ⟨result, loop, resultEq⟩ := (ex_bind_ok _ _ _).mp checked
  have equal : owners = result := (ex_pure_ok _ _).mp resultEq
  subst owners
  apply forIn_ownerInvariant targets _
    (fun owner => ∀ target, target ∈ rootsTargets owner.roots →
      target ∈ mapCallTargets callee ctx actual targets) ?_ (by simp) loop
  intro declared declaredMember previous following invariant stepChecked
  cases declared with
  | global global =>
    dsimp only at stepChecked
    cases declarationAt : access.mod.globals[global]? with
    | none => simp [declarationAt, reject, Functor.map, Except.map] at stepChecked
    | some declaration =>
      simp only [declarationAt] at stepChecked
      have equal := (ex_pure_ok _ _).mp stepChecked
      refine ⟨previous ++ [⟨some declaration.ty, [.global global]⟩], equal, ?_⟩
      intro owner member target targetMember
      rcases List.mem_append.mp member with old | added
      · exact invariant owner old target targetMember
      · simp only [List.mem_singleton] at added
        subst owner
        simp [rootsTargets, rootTarget] at targetMember
        subst target
        exact mapCall_global callee ctx actual targets global declaredMember
  | param index =>
    dsimp only at stepChecked
    cases actualAt : actual[index]? with
    | none => simp [actualAt, reject, Functor.map, Except.map] at stepChecked
    | some roots =>
      simp only [actualAt] at stepChecked
      obtain ⟨result, rootLoop, output⟩ := (ex_bind_ok _ _ _).mp stepChecked
      have equal := (ex_pure_ok _ _).mp output
      refine ⟨result, equal, ?_⟩
      apply forIn_ownerInvariant _ _ _ ?_ invariant rootLoop
      intro reference referenceMember previous following invariant checked
      have equal := (ex_pure_ok _ _).mp checked
      refine ⟨previous ++ [⟨access.rootType? reference, [reference]⟩], equal, ?_⟩
      intro owner member target targetMember
      rcases List.mem_append.mp member with old | added
      · exact invariant owner old target targetMember
      · simp only [List.mem_singleton] at added
        subst owner
        have mapped : target ∈ rootsTargets (actual[index]?.getD []) ∨
            target ∈ paramGlobals callee ctx index := by
          rcases List.mem_append.mp referenceMember with argument | globalRoot
          · exact Or.inl (by
              rw [actualAt]
              unfold rootsTargets at targetMember ⊢
              obtain ⟨ref, singleton, equal⟩ := List.mem_filterMap.mp targetMember
              have refEq : ref = reference := List.mem_singleton.mp singleton
              subst ref
              exact List.mem_filterMap.mpr ⟨reference, argument, equal⟩)
          · obtain ⟨globalTarget, globalMember, rootEq⟩ := List.mem_filterMap.mp globalRoot
            cases globalTarget with
            | param _ => simp at rootEq
            | global global =>
              have equal : reference = .global global := (Option.some.inj rootEq).symm
              subst reference
              simp [rootsTargets, rootTarget] at targetMember
              subst target
              exact Or.inr globalMember
        exact mapCall_param callee ctx actual targets index declaredMember target mapped

private theorem forIn_ownerAppend {α : Type} (items : List α)
    (step : α → List DemandOwner → V (ForInStep (List DemandOwner)))
    (added : α → List DemandOwner)
    (appendStep : ∀ item, item ∈ items → ∀ previous following,
      step item previous = .ok following → following = .yield (previous ++ added item))
    {previous following : List DemandOwner}
    (checked : forIn items previous step = .ok following) :
    following = previous ++ items.flatMap added := by
  induction items generalizing previous with
  | nil => simpa only [List.forIn_nil, ex_pure_ok, List.flatMap_nil, List.append_nil] using checked
  | cons item rest ih =>
    simp only [List.forIn_cons] at checked
    obtain ⟨control, head, tail⟩ := (ex_bind_ok _ _ _).mp checked
    have controlEq := appendStep item (by simp) previous control head
    have result := ih (fun item member => appendStep item (List.mem_cons_of_mem _ member))
      (by simpa only [controlEq] using tail)
    simpa only [List.flatMap_cons, List.append_assoc] using result

private def AccessEnv.targetOwnerEntries (access : AccessEnv) (callee : Impl)
    (ctx : Context) (actual : List (List RootRef)) : Target → List DemandOwner
  | .global global => [⟨access.rootType? (.global global), [.global global]⟩]
  | .param index =>
    ((actual[index]?.getD []) ++ (paramGlobals callee ctx index).filterMap (fun target => match target with
      | .global global => some (RootRef.global global)
      | _ => none)).map (fun reference => ⟨access.rootType? reference, [reference]⟩)

private theorem AccessEnv.targetOwners_entries (access : AccessEnv) (callee : Impl)
    (ctx : Context) (actual : List (List RootRef)) (targets : List Target)
    {owners : List DemandOwner} (checked : access.targetOwners callee ctx actual targets = .ok owners) :
    owners = targets.flatMap (AccessEnv.targetOwnerEntries access callee ctx actual) := by
  unfold AccessEnv.targetOwners at checked
  obtain ⟨result, loop, resultEq⟩ := (ex_bind_ok _ _ _).mp checked
  have equal : owners = result := (ex_pure_ok _ _).mp resultEq
  subst owners
  have result := forIn_ownerAppend targets _ (AccessEnv.targetOwnerEntries access callee ctx actual) ?_ loop
  · simpa only [List.nil_append] using result
  intro declared declaredMember previous following stepChecked
  cases declared with
  | global global =>
    dsimp only at stepChecked
    cases declarationAt : access.mod.globals[global]? with
    | none => simp [declarationAt, reject, Functor.map, Except.map] at stepChecked
    | some declaration =>
      simp only [declarationAt] at stepChecked
      have equal := (ex_pure_ok _ _).mp stepChecked
      simpa [AccessEnv.targetOwnerEntries, AccessEnv.rootType?, declarationAt] using equal
  | param index =>
    dsimp only at stepChecked
    cases actualAt : actual[index]? with
    | none => simp [actualAt, reject, Functor.map, Except.map] at stepChecked
    | some roots =>
      simp only [actualAt] at stepChecked
      obtain ⟨result, rootLoop, output⟩ := (ex_bind_ok _ _ _).mp stepChecked
      have resultEq := forIn_ownerAppend _ _
        (fun reference => [⟨access.rootType? reference, [reference]⟩])
        (fun reference _ previous following checked => (ex_pure_ok _ _).mp checked) rootLoop
      have singletonMap : ∀ roots : List RootRef,
          roots.flatMap (fun reference => [⟨access.rootType? reference, [reference]⟩]) =
            roots.map (fun reference => (⟨access.rootType? reference, [reference]⟩ : DemandOwner)) := by
        intro roots
        induction roots with
        | nil => rfl
        | cons _ _ ih => simp only [List.flatMap_cons, List.map_cons, List.singleton_append, ih]
      simp only [singletonMap] at resultEq
      have equal := (ex_pure_ok _ _).mp output
      rw [resultEq] at equal
      simp only [AccessEnv.targetOwnerEntries, actualAt, Option.getD_some]
      rw [equal]
      congr 4

private theorem targetOwnerEntries_argument {access : AccessEnv} {callee : Impl}
    {ctx : Context} {actual : List (List RootRef)} {index : Nat} {reference : RootRef}
    (member : reference ∈ actual[index]?.getD []) :
    (⟨access.rootType? reference, [reference]⟩ : DemandOwner) ∈
      AccessEnv.targetOwnerEntries access callee ctx actual (.param index) := by
  exact List.mem_map.mpr ⟨reference, List.mem_append_left _ member, rfl⟩

private theorem targetOwnerEntries_global {access : AccessEnv} {callee : Impl}
    {ctx : Context} {actual : List (List RootRef)} {index global : Nat}
    (member : Target.global global ∈ paramGlobals callee ctx index) :
    (⟨access.rootType? (.global global), [.global global]⟩ : DemandOwner) ∈
      AccessEnv.targetOwnerEntries access callee ctx actual (.param index) := by
  exact List.mem_map.mpr ⟨.global global, List.mem_append_right _
    (List.mem_filterMap.mpr ⟨.global global, member, rfl⟩), rfl⟩

private theorem callExpandedEffectRoot {penv : PEnv}
    {env : Env} {P : Nat → RootInst → Prop} {callee : Impl} {ctx : Context}
    {ars static : List (List RootRef)} {targets : List Target} {owners : List DemandOwner}
    {target : Target} {root : RootInst}
    (checked : CtxOk m callee ctx)
    (parameters : ∀ index, Target.param index ∈ targets → index < callee.params.size)
    (argumentsIncluded : RootListsIncluded ars static)
    (entries : owners = targets.flatMap (AccessEnv.targetOwnerEntries penv.access callee ctx static))
    (member : target ∈ expandTargets callee ctx targets)
    (denotes : TargetDenotes (fun index root => Gam env P (ars[index]?.getD []) root) target root)
    : ∃ reference, (⟨penv.access.rootType? reference, [reference]⟩ : DemandOwner) ∈ owners ∧
      RootIn env P root reference := by
  have fromReference : ∀ declared, declared ∈ targets → ∀ reference,
      (⟨penv.access.rootType? reference, [reference]⟩ : DemandOwner) ∈
        AccessEnv.targetOwnerEntries penv.access callee ctx static declared →
      RootIn env P root reference →
      ∃ reference, (⟨penv.access.rootType? reference, [reference]⟩ : DemandOwner) ∈ owners ∧
        RootIn env P root reference := by
    intro declared declaredAt reference entry realization
    exact ⟨reference, entries ▸ List.mem_flatMap.mpr ⟨declared, declaredAt, entry⟩, realization⟩
  have formal : ∀ index, Target.param index ∈ targets →
      Gam env P (ars[index]?.getD []) root →
      ∃ reference, (⟨penv.access.rootType? reference, [reference]⟩ : DemandOwner) ∈ owners ∧
        RootIn env P root reference := by
    intro index declaredAt authority
    obtain ⟨reference, referenceMember, realization⟩ := authority
    have staticMember : reference ∈ static[index]?.getD [] := by
      cases actualAt : ars[index]? with
      | none => simp [actualAt] at referenceMember
      | some actual =>
        obtain ⟨expected, expectedAt, subset⟩ := argumentsIncluded index actual actualAt
        simpa [expectedAt] using subset reference (by simpa [actualAt] using referenceMember)
    exact fromReference (.param index) declaredAt reference
      (targetOwnerEntries_argument staticMember) realization
  simp only [expandTargets, List.mem_flatMap] at member
  obtain ⟨declared, declaredAt, expandedAt⟩ := member
  cases declared with
  | global global =>
    simp only [List.mem_singleton] at expandedAt
    subst target
    exact fromReference (.global global) declaredAt (.global global) (by simp [AccessEnv.targetOwnerEntries]) denotes
  | param index =>
    cases variableAt : callee.vars[index]? with
    | none =>
      simp only [variableAt, List.mem_singleton] at expandedAt
      subst target
      exact formal index declaredAt denotes
    | some lv =>
      cases annotationAt : ctx.varRoots.find? (·.1 == index) with
      | none =>
        simp only [variableAt, annotationAt, List.mem_singleton] at expandedAt
        subst target
        exact formal index declaredAt denotes
      | some pair =>
        obtain ⟨variableId, roots⟩ := pair
        by_cases referenceType : lv.ty.isRefLike = true
        · simp only [variableAt, annotationAt, referenceType, if_true,
            rootsTargets, List.mem_filterMap] at expandedAt
          obtain ⟨reference, rootMember, targetEq⟩ := expandedAt
          cases reference with
          | «local» _ => simp [rootTarget] at targetEq
          | global global =>
            simp only [rootTarget, Option.some.injEq] at targetEq
            subst target
            have globalMember : Target.global global ∈ paramGlobals callee ctx index := by
              simp only [paramGlobals, variableAt, annotationAt, referenceType, if_true, List.mem_filterMap]
              exact ⟨.global global, rootMember, rfl⟩
            exact fromReference (.param index) declaredAt (.global global)
              (targetOwnerEntries_global globalMember) denotes
          | param actualIndex =>
            simp only [rootTarget, Option.some.injEq] at targetEq
            subst target
            rcases checked.paramAnn index roots (parameters index declaredAt)
              (by simp [annotationAt]) (.param actualIndex) rootMember with equal | ⟨_, equal⟩
            · cases equal
              exact formal index declaredAt denotes
            · cases equal
        · simp only [variableAt, annotationAt, referenceType, Bool.false_eq_true,
            if_false, List.mem_singleton] at expandedAt
          subst target
          exact formal index declaredAt denotes

private theorem callExpandedOwnerRoot {W : World} {tenv : TEnv} {penv : PEnv}
    {env : Env} {s : St} {future : List VarId} {callee : Impl} {ctx : Context}
    {ars static : List (List RootRef)} {targets : List Target} {owners : List DemandOwner}
    {target : Target} {root : RootInst} {observation : Observation}
    {continuation : List VarId} {retained : List RetainedAlias}
    (frame : Frame m W tenv penv env s future) (checked : CtxOk m callee ctx)
    (older : ∀ holder type, observation.roots holder type → BeforeBase W.base holder)
    (parameters : ∀ index, Target.param index ∈ targets → index < callee.params.size)
    (argumentsIncluded : RootListsIncluded ars static)
    (requests : penv.access.targetOwners callee ctx static targets = .ok owners)
    (member : target ∈ expandTargets callee ctx targets)
    (denotes : TargetDenotes (callOwnerP W callee env ars) target root)
    (capability : OwnerCap m
      (callObservation (m := m) observation W tenv env continuation retained s.store) root) :
    ∃ owner, owner ∈ owners ∧ owner.invalidates = true ∧ Gam env W.ownerP owner.roots root := by
  have broadDenotes : TargetDenotes
      (fun index root => Gam env W.ownerP (ars[index]?.getD []) root) target root := by
    cases target with
    | global _ => exact denotes
    | param _ => exact denotes.2
  obtain ⟨reference, member, realization⟩ := callExpandedEffectRoot checked parameters
    argumentsIncluded (AccessEnv.targetOwners_entries _ _ _ _ _ requests) member broadDenotes
  exact ⟨⟨penv.access.rootType? reference, [reference]⟩, member,
    frame.callOwner_invalidates older realization capability, reference, by simp, realization⟩

private theorem callMayShrink_coverage {W : World} {tenv : TEnv} {penv : PEnv}
    {env : Env} {s : St} {future : List VarId} {callee : Impl} {ctx : Context}
    {ars static : List (List RootRef)} {owners : List DemandOwner} {effect : Eff}
    {root : RootInst} {observation : Observation} {continuation : List VarId}
    {retained : List RetainedAlias}
    (frame : Frame m W tenv penv env s future) (checked : CtxOk m callee ctx)
    (effectReplay : ContextEff m callee ctx effect)
    (older : ∀ holder type, observation.roots holder type → BeforeBase W.base holder)
    (argumentsIncluded : RootListsIncluded ars static)
    (requests : (match callee.summary with
      | .unknown => pure (penv.access.unknownOwners static)
      | .known summary => penv.access.targetOwners callee ctx static summary.shrinks) = .ok owners)
    (shrinking : MayShrinkEff (callOwnerP W callee env ars) effect root)
    (capability : OwnerCap m
      (callObservation (m := m) observation W tenv env continuation retained s.store) root) :
    ∃ owner, owner ∈ owners ∧ owner.invalidates = true ∧ Gam env W.ownerP owner.roots root := by
  obtain ⟨target, effectTarget, denotes⟩ := shrinking
  cases summaryAt : callee.summary with
  | known summary =>
    obtain ⟨notUnknown, _, _, shrinks, _, parameters⟩ :=
      checkSummary_mutations (effectReplay.checkedSummary checked) summaryAt
    have explicit : target ∈ effect.shrinks := effectTarget.resolve_right (by simp [notUnknown])
    exact callExpandedOwnerRoot frame checked older
      (fun index member => parameters index (Or.inr (Or.inr (Or.inl member))))
      argumentsIncluded (by simpa [summaryAt] using requests) (shrinks target explicit) denotes capability
  | unknown =>
      have ownersEq : owners = penv.access.unknownOwners static := by
        simpa only [summaryAt, ex_pure_ok] using requests
      have argument : ∀ index, callOwnerP W callee env ars index root →
          ∃ owner, owner ∈ owners ∧ owner.invalidates = true ∧ Gam env W.ownerP owner.roots root := by
        intro index authority
        obtain ⟨reference, member, denotes⟩ := authority.2
        have flattened : reference ∈ static.flatten := by
          cases actualAt : ars[index]? with
          | none => simp [actualAt] at member
          | some actual =>
            obtain ⟨expected, expectedAt, subset⟩ := argumentsIncluded index actual actualAt
            exact List.mem_flatten.mpr ⟨expected, List.mem_of_getElem? expectedAt,
              subset reference (by simpa [actualAt] using member)⟩
        refine ⟨⟨penv.access.rootType? reference, [reference]⟩, ?_,
          frame.callOwner_invalidates older denotes capability, reference, by simp, denotes⟩
        rw [ownersEq]
        exact List.mem_append_right _ (List.mem_map.mpr ⟨reference, flattened, rfl⟩)
      cases target with
      | param index => exact argument index denotes
      | global global =>
        change root = .global global at denotes
        subst root
        obtain ⟨declaration, declarationAt, element, kind⟩ := capability
        have member : (declaration, global) ∈ penv.mod.globals.toList.zipIdx := by
          apply List.mem_zipIdx_iff_getElem?.mpr
          simpa only [Array.getElem?_toList, PEnv.access, frame.mod_p] using declarationAt
        refine ⟨⟨some declaration.ty, [.global global]⟩, ?_, ?_, .global global, by simp, rfl⟩
        · rw [ownersEq]
          apply List.mem_append_left
          apply List.mem_filterMap.mpr
          refine ⟨(declaration, global), member, ?_⟩
          rcases kind with grow | shrink
          · simp [grow, Ty.ownerElem?]
          · simp [shrink, Ty.ownerElem?]
        · rcases kind with grow | shrink
          · simp [DemandOwner.invalidates, grow]
          · simp [DemandOwner.invalidates, shrink]

private theorem callBodyEffectOwnerRoot {W : World} {tenv : TEnv} {penv : PEnv}
    {env : Env} {s : St} {future : List VarId} {callee : Impl} {ctx : Context}
    {ars static : List (List RootRef)} {owners : List DemandOwner} {effect initial : Eff}
    {root : RootInst} {element : Ty} {values : Array Val}
    (frame : Frame m W tenv penv env s future) (moduleOk : ModOk m)
    (implementationOk : ImplOk m callee) (checked : CtxOk m callee ctx)
    (contextEffect : ContextEff m callee ctx effect) (permission : Perm m W)
    (charged : EffLe (callEffects callee ctx ars initial) W.E)
    (argumentsIncluded : RootListsIncluded ars static)
    (requests : (match callee.summary with
      | .unknown => pure (penv.access.unknownOwners static)
      | .known summary => penv.access.targetOwners callee ctx static
          (summary.reads ++ summary.writes ++ summary.grows ++ summary.shrinks ++ summary.rebinds)) = .ok owners)
    (present : s.store.roots[root]? = some (.resizable element values))
    (denoted : Gam noEnv (fun index root => Gam env W.P (ars[index]?.getD []) root)
      (effectMutationRoots m callee effect) root) :
    ∃ owner, owner ∈ owners ∧ Gam env W.P owner.roots root := by
  cases summaryAt : callee.summary with
  | known summary =>
    obtain ⟨notUnknown, writes, grows, shrinks, rebinds, parameters⟩ :=
      checkSummary_mutations (contextEffect.checkedSummary checked) summaryAt
    have ownersEq := AccessEnv.targetOwners_entries penv.access callee ctx static _
      (by simpa only [summaryAt] using requests)
    let mutations := summary.writes ++ summary.grows ++ summary.shrinks ++ summary.rebinds
    let mutationOwners := mutations.flatMap (AccessEnv.targetOwnerEntries penv.access callee ctx static)
    have added : ∀ owner, owner ∈ mutationOwners → owner ∈ owners := by
      intro owner member
      rw [ownersEq]
      obtain ⟨declared, declaredAt, member⟩ := List.mem_flatMap.mp member
      exact List.mem_flatMap.mpr ⟨declared,
        by simpa only [mutations, List.append_assoc] using List.mem_append_right summary.reads declaredAt, member⟩
    have expand : ∀ target, target ∈ expandTargets callee ctx mutations →
        TargetDenotes (fun index root => Gam env W.P (ars[index]?.getD []) root) target root →
        ∃ owner, owner ∈ owners ∧ Gam env W.P owner.roots root := by
      intro target member realization
      obtain ⟨reference, member, realization⟩ := callExpandedEffectRoot checked
        (fun index member => parameters index (by
          simpa only [mutations, List.mem_append, or_assoc] using member))
        argumentsIncluded (owners := mutationOwners) rfl member realization
      exact ⟨⟨penv.access.rootType? reference, [reference]⟩, added _ member,
        reference, by simp, realization⟩
    obtain ⟨reference, member, realization⟩ := denoted
    simp only [effectMutationRoots, notUnknown, Bool.false_eq_true, ite_false,
      effectTargetRoots, List.mem_map] at member
    obtain ⟨target, targetAt, rfl⟩ := member
    have realizationTarget : TargetDenotes
        (fun index root => Gam env W.P (ars[index]?.getD []) root) target root := by
      cases target <;> exact realization
    simp only [effectMutationTargets, List.mem_append] at targetAt
    rcases targetAt with ((write | grow) | shrink) | rebind
    · apply expand target ?_ realizationTarget
      simp only [mutations, expandTargets, List.flatMap_append, List.mem_append]
      exact Or.inl (Or.inl (Or.inl (writes _ write)))
    · apply expand target ?_ realizationTarget
      simp only [mutations, expandTargets, List.flatMap_append, List.mem_append]
      exact Or.inl (Or.inl (Or.inr (grows _ grow)))
    · apply expand target ?_ realizationTarget
      simp only [mutations, expandTargets, List.flatMap_append, List.mem_append]
      exact Or.inl (Or.inr (shrinks _ shrink))
    · have declaredAt : target ∈ mutations := by
        simp only [mutations, List.mem_append]
        exact Or.inr (rebinds _ rebind)
      have emit : ∀ reference,
          (⟨penv.access.rootType? reference, [reference]⟩ : DemandOwner) ∈
            AccessEnv.targetOwnerEntries penv.access callee ctx static target →
          RootIn env W.P root reference → ∃ owner, owner ∈ owners ∧ Gam env W.P owner.roots root := by
        intro reference member realization
        exact ⟨⟨penv.access.rootType? reference, [reference]⟩,
          added _ (List.mem_flatMap.mpr ⟨target, declaredAt, member⟩), reference, by simp, realization⟩
      cases target with
      | global global => exact emit (.global global) (by simp [AccessEnv.targetOwnerEntries]) realization
      | param index =>
        obtain ⟨reference, member, realization⟩ := realization
        have staticMember : reference ∈ static[index]?.getD [] := by
          cases actualAt : ars[index]? with
          | none => simp [actualAt] at member
          | some actual =>
            obtain ⟨expected, expectedAt, subset⟩ := argumentsIncluded index actual actualAt
            simpa [expectedAt] using subset reference (by simpa [actualAt] using member)
        exact emit reference (targetOwnerEntries_argument staticMember) realization
  | unknown =>
    have ownersEq : owners = penv.access.unknownOwners static := by
      simpa only [summaryAt, ex_pure_ok] using requests
    obtain ⟨reference, member, realization⟩ := denoted
    cases reference with
    | «local» variableId =>
      obtain ⟨_, _, variableAt, _⟩ := realization
      simp [noEnv] at variableAt
    | param index =>
      obtain ⟨reference, member, realization⟩ := realization
      have flattened : reference ∈ static.flatten := by
        cases actualAt : ars[index]? with
        | none => simp [actualAt] at member
        | some actual =>
          obtain ⟨expected, expectedAt, subset⟩ := argumentsIncluded index actual actualAt
          exact List.mem_flatten.mpr ⟨expected, List.mem_of_getElem? expectedAt,
            subset reference (by simpa [actualAt] using member)⟩
      refine ⟨⟨penv.access.rootType? reference, [reference]⟩, ?_, reference, by simp, realization⟩
      rw [ownersEq]
      exact List.mem_append_right _ (List.mem_map.mpr ⟨reference, flattened, rfl⟩)
    | global global =>
      change root = .global global at realization
      subst root
      have bound := effectMutationRoots_globalIndex
        (fun _ targetAt => contextEffect.mutationGlobalIndex moduleOk implementationOk checked targetAt) member
      have initialized : global < W.G := by
        rcases permission with allInitialized | ⟨known, _⟩
        · exact Nat.lt_of_lt_of_le bound allInitialized
        · have unknown : W.E.unknown = true := charged.2.2.2.2 (by simp [callEffects, summaryAt])
          rw [known] at unknown
          cases unknown
      let declaration := m.globals[global]
      have declarationAt : m.globals[global]? = some declaration :=
        Array.getElem?_eq_some_iff.mpr ⟨bound, rfl⟩
      obtain ⟨value, read, typed⟩ := frame.inv.globals global declaration initialized declarationAt
      obtain ⟨stored, storedAt, valueAt⟩ := (read_ok_iff _ _ _).mp read
      rw [present] at storedAt
      cases storedAt
      simp only [get_nil, Option.some.injEq] at valueAt
      subst value
      have ownerType : declaration.ty.ownerElem?.isSome = true := by
        cases typeAt : declaration.ty <;> simp_all [FlatTy, Ty.ownerElem?]
      refine ⟨⟨some declaration.ty, [.global global]⟩, ?_, .global global, by simp, rfl⟩
      rw [ownersEq]
      apply List.mem_append_left
      apply List.mem_filterMap.mpr
      refine ⟨(declaration, global), ?_, ?_⟩
      · apply List.mem_zipIdx_iff_getElem?.mpr
        simpa only [Array.getElem?_toList, PEnv.access, frame.mod_p] using declarationAt
      · simp [ownerType]

private theorem mapCallTargets_included (callee : Impl) (ctx : Context)
    {static actual : List (List RootRef)} (included : RootListsIncluded static actual)
    (targets : List Target) :
    ∀ target, target ∈ mapCallTargets callee ctx static targets →
      target ∈ mapCallTargets callee ctx actual targets := by
  induction targets with
  | nil => simp [mapCallTargets]
  | cons declared rest ih =>
    intro target member
    cases declared with
    | global global =>
      simp only [mapCallTargets, List.mem_cons] at member ⊢
      exact member.elim Or.inl (fun tail => Or.inr (ih target tail))
    | param index =>
      simp only [mapCallTargets, List.mem_append] at member ⊢
      rcases member with (argument | global) | tail
      · refine Or.inl (Or.inl ?_)
        cases staticAt : static[index]? with
        | none => simp [staticAt, rootsTargets] at argument
        | some roots =>
          obtain ⟨actualRoots, actualAt, subset⟩ := included index roots staticAt
          rw [staticAt] at argument
          rw [actualAt]
          obtain ⟨reference, referenceMember, targetEq⟩ := List.mem_filterMap.mp argument
          exact List.mem_filterMap.mpr ⟨reference, subset reference referenceMember, targetEq⟩
      · exact Or.inl (Or.inr global)
      · exact Or.inr (ih target tail)

/-- A call's expected request roots are part of its own replay contribution.
Unknown summaries supply the unknown flag instead of enumerated shrink targets. -/
private theorem callShrinkOwners_recorded {penv : PEnv} {context : ContextId} {args : List Arg}
    {origin : OriginId} {before after : RState} {output : List RootRef}
    {owners : List DemandOwner}
    (moduleOk : ModOk m) (modMatches : penv.mod = m)
    (queried : penv.access.callShrinkOwners context args = .ok owners)
    (replay : rpExpr penv (.call context args origin) before = .ok (output, after)) :
    ∀ owner, owner ∈ owners → ∀ target, target ∈ rootsTargets owner.roots →
      target ∈ after.eff.shrinks ∨ after.eff.unknown = true := by
  simp only [rpExpr] at replay
  inv at replay
  obtain ⟨actual, argumentState, argumentsReplay, _, callReplay⟩ := replay
  obtain ⟨ctx, callee, contextAt, implementationAt, _, effectAt, _⟩ :=
    rpCall_ok _ _ _ _ _ _ callReplay
  simp only [AccessEnv.callShrinkOwners, PEnv.access, contextAt, implementationAt] at queried
  obtain ⟨static, staticAt, requests⟩ := (ex_bind_ok _ _ _).mp queried
  cases summaryAt : callee.summary with
  | unknown =>
    intro _ _ _ _
    exact Or.inr (by simp [effectAt, callEffects, summaryAt])
  | known summary =>
    rw [summaryAt] at requests
    have argumentsIncluded := rpArgs_accessRoots_reverse penv moduleOk modMatches args
      before actual argumentState static argumentsReplay staticAt
    intro owner ownerMember target targetMember
    have staticMember := AccessEnv.targetOwners_recorded penv.access callee ctx static summary.shrinks
      owners requests owner ownerMember target targetMember
    have actualMember := mapCallTargets_included callee ctx argumentsIncluded summary.shrinks
      target staticMember
    exact Or.inl (by
      rw [effectAt]
      exact callShrinkTargets_ok callee ctx actual argumentState.eff summary summaryAt target actualMember)

private theorem DemandExpectedSourceAt.callShrink_owner_context_targets
    {impl : Impl} {ctx : Context} {effect : Eff} {contextOwner : Nat}
    {path : List Nat} {context : ContextId} {args : List Arg} {origin : OriginId}
    {expected : DemandExpectedPoint} {shrinkOwner : DemandOwner}
    (sourceAt : DemandExpectedSourceAt m contextOwner path
      (.expression (.call context args origin)) .mutation expected)
    (root : demandRoot? m contextOwner = some (.block impl.body))
    (moduleOk : ModOk m)
    (accessMatches : demandAccess? m contextOwner = some (⟨m, impl, ctx⟩ : AccessEnv))
    (ownerMember : shrinkOwner ∈ expected.shrinkOwners)
    (contextEffect : ContextEff m impl ctx effect) :
    ∀ target, target ∈ rootsTargets shrinkOwner.roots →
      target ∈ effect.shrinks ∨ effect.unknown = true := by
  obtain ⟨_, _, requests⟩ := sourceAt.callShrinkOwners rfl rfl accessMatches
  obtain ⟨roots, range, after, replay, effectEq⟩ := contextEffect
  obtain ⟨leafEnv, leafBefore, leafAfter, output, leafMod, leafImpl, leafCtx,
    leafReplay, leafLe⟩ := DemandExpectedSourceAt.call_block_replay sourceAt root ⟨m, impl, ctx, []⟩
      ⟨impl.params.size, {}⟩ after roots range replay
  have leafAccess : leafEnv.access = (⟨m, impl, ctx⟩ : AccessEnv) := by
    simp only [PEnv.access, leafMod, leafImpl, leafCtx]
  have leafRequests : leafEnv.access.callShrinkOwners context args = .ok expected.shrinkOwners := by
    rw [leafAccess]
    exact requests
  intro target member
  rcases callShrinkOwners_recorded moduleOk leafMod leafRequests leafReplay
    shrinkOwner ownerMember target member with recorded | unknown
  · exact Or.inl (effectEq ▸ leafLe.2.2.2.2.1 target recorded)
  · exact Or.inr (effectEq ▸ leafLe.2.2.2.2.2 unknown)

private theorem DemandNode.mutation_direct_or_call (node : DemandNode)
    (phase : DemandNodeHasPhase node .mutation) :
    (∃ place, node.directShrinkPlace? = some place) ∨
      ∃ context args origin, node = .expression (.call context args origin) := by
  cases node with
  | expression expression =>
    cases expression <;> simp_all [DemandNodeHasPhase, DemandNode.phaseMatches,
      DemandNode.directShrinkPlace?]
  | statement statement =>
    cases statement <;> simp_all [DemandNodeHasPhase, DemandNode.phaseMatches,
      DemandNode.directShrinkPlace?]
  | place _ | view _ | bound _ | block _ =>
    simp [DemandNodeHasPhase, DemandNode.phaseMatches] at phase

/-- Every owner request in the checked body is recorded by the exact replay.
Nested call requests contribute either their mapped shrink targets or unknown. -/
private theorem PlanContext.shrinkOwner_recorded {plans : Array (Array DemandPoint)}
    (pc : PlanContext m plans) {impl : Impl} {ctx : Context} {effect : Eff}
    {expected : DemandExpectedPoint} {owner : DemandOwner}
    (root : demandRoot? m pc.owner = some (.block impl.body))
    (moduleOk : ModOk m)
    (accessMatches : demandAccess? m pc.owner = some (⟨m, impl, ctx⟩ : AccessEnv))
    (member : expected ∈ pc.expected) (phase : expected.phase = .mutation)
    (ownerMember : owner ∈ expected.shrinkOwners)
    (contextEffect : ContextEff m impl ctx effect) :
    ∀ target, target ∈ rootsTargets owner.roots →
      target ∈ effect.shrinks ∨ effect.unknown = true := by
  have sourceAt : DemandExpectedSourceAt m pc.owner expected.path expected.node .mutation expected :=
    ⟨pc.expected, pc.expectedWalk, member, rfl, rfl, phase⟩
  rcases DemandNode.mutation_direct_or_call expected.node sourceAt.sourceFacts.2 with
    ⟨place, direct⟩ | ⟨context, args, origin, callEq⟩
  · obtain ⟨queriedOwner, queried, ownerEq⟩ :=
      sourceAt.directShrinkOwner_result rfl direct accessMatches
    have equal : owner = queriedOwner := by simpa [ownerEq] using ownerMember
    subst owner
    have recorded := DemandExpectedSourceAt.directShrink_owner_context_targets sourceAt root direct moduleOk
      accessMatches queried contextEffect
    exact fun target targetMember => Or.inl (recorded.2 target targetMember)
  · have callSource : DemandExpectedSourceAt m pc.owner expected.path
        (.expression (.call context args origin)) .mutation expected := by
      simpa [callEq] using sourceAt
    exact DemandExpectedSourceAt.callShrink_owner_context_targets callSource root moduleOk accessMatches ownerMember contextEffect

/-- The checked body's external owner relation is covered by its exact effect. -/
private theorem PlanMayShrink.contextEffect {plans : Array (Array DemandPoint)}
    {pc : PlanContext m plans} {impl : Impl} {ctx : Context} {effect : Eff}
    {P : Nat → RootInst → Prop} {rootInst : RootInst}
    (root : demandRoot? m pc.owner = some (.block impl.body)) (moduleOk : ModOk m)
    (accessMatches : demandAccess? m pc.owner = some (⟨m, impl, ctx⟩ : AccessEnv))
    (contextEffect : ContextEff m impl ctx effect)
    (shrinking : PlanMayShrink pc P rootInst) : MayShrinkEff P effect rootInst := by
  obtain ⟨expected, member, phase, owner, ownerMember, _, reference, referenceMember, denotes⟩ := shrinking
  have recorded := pc.shrinkOwner_recorded root moduleOk accessMatches member phase ownerMember contextEffect
  cases reference with
  | «local» variableId =>
    obtain ⟨_, _, variableAt, _⟩ := denotes
    simp [noEnv] at variableAt
  | global global =>
    exact ⟨.global global, recorded _ (mem_rootsTargets_global referenceMember), denotes⟩
  | param index =>
    exact ⟨.param index, recorded _ (mem_rootsTargets_param referenceMember), denotes⟩

private theorem EvaluationContext.callBody_effect {plans : Array (Array DemandPoint)}
    {impl : Impl} {ctx : Context} {c : ContextId} {effect : Eff}
    (root : EvaluationContext m plans [] (.block impl.body) .block)
    {P : Nat → RootInst → Prop} {observation : Observation} {rootInst : RootInst}
    (owner : root.OwnerMatches c) (contextAt : m.contexts[c]? = some ctx)
    (implementationAt : m.impls[ctx.impl]? = some impl) (moduleOk : ModOk m)
    (contextEffect : ContextEff m impl ctx effect)
    (shrinking : root.mayShrink P observation rootInst) :
    MayShrinkEff P effect rootInst ∧ OwnerCap m observation rootInst := by
  cases root with
  | pilot _ _ => exact False.elim shrinking
  | @shrink pc _ context =>
    change pc.owner = c at owner
    have bodyRoot : demandRoot? m pc.owner = some (.block impl.body) := by
      rw [owner]
      exact demandRoot?_context contextAt implementationAt
    have bodyAccess : demandAccess? m pc.owner = some (⟨m, impl, ctx⟩ : AccessEnv) := by
      rw [owner]
      exact demandAccess?_context contextAt implementationAt
    exact ⟨PlanMayShrink.contextEffect bodyRoot moduleOk bodyAccess contextEffect shrinking.1, shrinking.2⟩

/-- The caller mutation point is selected from its exact source occurrence. -/
private noncomputable def NodeContext.callMutationContext {plans : Array (Array DemandPoint)}
    {pc : PlanContext m plans} {path : List Nat} {c : ContextId} {args : List Arg} {origin : OriginId}
    (context : NodeContext pc path (.expression (.call c args origin)) .expression) :
    NodeContext pc path (.expression (.call c args origin)) .mutation :=
  (context.phase rfl .mutation (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).context

private theorem NodeContext.callMutation_retains_argument {plans : Array (Array DemandPoint)}
    {pc : PlanContext m plans} {path : List Nat} {c : ContextId} {args : List Arg} {origin : OriginId}
    (context : NodeContext pc path (.expression (.call c args origin)) .expression)
    (index : Nat) (arg : Arg) (argumentAt : args[index]? = some arg) :
    ∃ aliases, pc.approvals.access.aliasArg (path ++ [index]) arg = .ok aliases ∧
      ∀ alias, alias ∈ aliases → alias ∈ context.callMutationContext.expected.frame.retained := by
  let transition := context.phase rfl .mutation
    (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])
  obtain ⟨aliases, checked, retained⟩ := DemandNode.call_mutation_retains_argument
    transition.phaseFrameEq (List.getElem?_eq_some_iff.mp argumentAt).1 argumentAt
  refine ⟨aliases, checked, ?_⟩
  intro alias member
  change alias ∈ transition.context.expected.frame.retained
  rw [transition.expectedFrameEq]
  exact retained alias member

private theorem NodeContext.callMutation_retains_parent {plans : Array (Array DemandPoint)}
    {pc : PlanContext m plans} {path : List Nat} {c : ContextId} {args : List Arg} {origin : OriginId}
    (context : NodeContext pc path (.expression (.call c args origin)) .expression) :
    ∀ alias, alias ∈ context.expected.frame.retained →
      alias ∈ context.callMutationContext.expected.frame.retained := by
  let transition := context.phase rfl .mutation
    (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])
  have phaseFrame := transition.phaseFrameEq
  simp only [DemandNode.phaseFrame, beq_self_eq_true, Bool.or_true, ite_true] at phaseFrame
  obtain ⟨aliases, _, frameEq⟩ := (ex_bind_ok _ _ _).mp phaseFrame
  have resultEq := (ex_pure_ok _ _).mp frameEq
  intro alias member
  change alias ∈ transition.context.expected.frame.retained
  rw [transition.expectedFrameEq, resultEq]
  exact List.mem_append_right _ member

/-- Every call owner approval uses the canonical access environment and the
same active, future and retained membership as this mutation occurrence. -/
private theorem NodeContext.callMutation_shrinkSafe {plans : Array (Array DemandPoint)}
    {pc : PlanContext m plans} {path : List Nat} {c : ContextId} {args : List Arg} {origin : OriginId}
    (context : NodeContext pc path (.expression (.call c args origin)) .expression)
    (owner : DemandOwner) (membership : owner ∈ context.callMutationContext.expected.shrinkOwners) :
    DemandPointShrinkSafe pc.approvals.access context.callMutationContext.expected.toPoint owner := by
  let mutation := context.callMutationContext
  obtain ⟨_, _, _, _, nodeEq, phaseEq⟩ := mutation.sourceAt
  have callInfo : mutation.expected.node.callInfo? = some (c, args) := by
    rw [nodeEq]
    rfl
  obtain ⟨approval, accessEq, _, ownerEq, _, frameMembership⟩ :=
    pc.approvals.callShrinkAt mutation.expected mutation.member c args callInfo phaseEq owner membership
  have safe := approval.safe
  rw [accessEq, ownerEq] at safe
  constructor
  · constructor
    · intro x future active alias realized
      exact safe.1.1 x ((frameMembership.2.1 x).mpr future)
        ((frameMembership.1 x).mpr active) alias realized
    · intro alias retained
      exact safe.1.2 alias ((frameMembership.2.2 alias).mpr retained)
  · intro x future active
    exact safe.aliasVariable_succeeds ((frameMembership.2.1 x).mpr future)
      ((frameMembership.1 x).mpr active)

private theorem NodeContext.checkedAccess_eq {plans : Array (Array DemandPoint)}
    {pc : PlanContext m plans} {path : List Nat} {node : DemandNode} {phase : DemandPhase}
    (context : NodeContext pc path node phase) (matched : context.AccessMatches tenv penv) :
    pc.approvals.access = penv.access := by
  rcases matched with ⟨_, _, modEq, implEq, ctxEq⟩
  have rebuild : pc.approvals.access =
      ⟨pc.approvals.access.mod, pc.approvals.access.impl, pc.approvals.access.ctx⟩ := by
    cases pc.approvals.access
    rfl
  exact rebuild.trans (by rw [modEq, implEq, ctxEq]; rfl)

private theorem NodeContext.callGlobal_initialized {plans : Array (Array DemandPoint)}
    {pc : PlanContext m plans} {path : List Nat} {c : ContextId} {args : List Arg} {origin : OriginId}
    (context : NodeContext pc path (.expression (.call c args origin)) .expression)
    {W : World} {tenv : TEnv} {penv : PEnv} {env : Env} {s : St} {future : List VarId}
    {before after : RState} {output : List RootRef} {observation : Observation} {global : Nat}
    {owner : DemandOwner}
    (moduleOk : ModOk m) (frame : Frame m W tenv penv env s future)
    (access : context.AccessMatches tenv penv) (permission : Perm m W)
    (replay : rpExpr penv (.call c args origin) before = .ok (output, after))
    (effects : EffLe after.eff W.E)
    (ownerMember : owner ∈ context.callMutationContext.expected.shrinkOwners)
    (ownerIn : Gam env W.ownerP owner.roots (.global global))
    (capability : OwnerCap m observation (.global global)) : global < W.G := by
  have accessEq := context.checkedAccess_eq access
  obtain ⟨_, _, query⟩ := context.callMutationContext.sourceAt.callShrinkOwners
    rfl rfl pc.approvals.accessMatches
  rw [accessEq] at query
  have recorded := callShrinkOwners_recorded moduleOk frame.mod_p query replay owner ownerMember
  obtain ⟨reference, member, denotes⟩ := ownerIn
  have may : MayShrinkEff W.P W.E (.global global) := by
    cases reference with
    | «local» variableId =>
      obtain ⟨_, _, _, _, impossible⟩ := denotes
      cases impossible
    | global targetGlobal =>
      exact ⟨.global targetGlobal,
        (recorded _ (mem_rootsTargets_global member)).elim
          (fun shrink => Or.inl (effects.2.2.2.1 _ shrink))
          (fun unknown => Or.inr (effects.2.2.2.2 unknown)), denotes⟩
    | param index =>
      exact ⟨.param index,
        (recorded _ (mem_rootsTargets_param member)).elim
          (fun shrink => Or.inl (effects.2.2.2.1 _ shrink))
          (fun unknown => Or.inr (effects.2.2.2.2 unknown)), frame.ownerSubset index _ denotes⟩
  exact Goose.Core.Sound.callGlobal_initialized permission capability may

private theorem NodeContext.callBody_coverage {plans : Array (Array DemandPoint)}
    {pc : PlanContext m plans} {path : List Nat} {c : ContextId} {args : List Arg} {origin : OriginId}
    (context : NodeContext pc path (.expression (.call c args origin)) .expression)
    {W : World} {tenv : TEnv} {penv : PEnv} {env : Env} {s : St} {future : List VarId}
    {observation : Observation} {retained : List RetainedAlias} {callee : Impl} {ctx : Context}
    {effect : Eff} {ars : List (List RootRef)} {before after : RState}
    (frame : Frame m W tenv penv env s future)
    (access : context.AccessMatches tenv penv) (contextAt : m.contexts[c]? = some ctx)
    (implementationAt : m.impls[ctx.impl]? = some callee) (checked : CtxOk m callee ctx)
    (contextEffect : ContextEff m callee ctx effect)
    (older : ∀ holder type, observation.roots holder type → BeforeBase W.base holder)
    (argumentsReplay : rpArgs penv args before = .ok (ars, after)) :
    ∀ root, MayShrinkEff (callOwnerP W callee env ars) effect root →
      OwnerCap m (callObservation (m := m) observation W tenv env context.outputFuture retained s.store) root →
      ∃ owner, owner ∈ context.callMutationContext.expected.shrinkOwners ∧
        owner.invalidates = true ∧ Gam env W.ownerP owner.roots root := by
  have accessEq := context.checkedAccess_eq access
  obtain ⟨static, staticAt, query⟩ := context.callMutationContext.sourceAt.callShrinkOwners
    rfl rfl pc.approvals.accessMatches
  rw [accessEq] at staticAt query
  have included := rpArgs_accessRoots penv args before ars after static argumentsReplay staticAt
  have query' : (match callee.summary with
      | .unknown => pure (penv.access.unknownOwners static)
      | .known summary => penv.access.targetOwners callee ctx static summary.shrinks) =
      .ok context.callMutationContext.expected.shrinkOwners := by
    have contextAtP : penv.access.mod.contexts[c]? = some ctx := by
      simpa only [PEnv.access, frame.mod_p] using contextAt
    have implementationAtP : penv.access.mod.impls[ctx.impl]? = some callee := by
      simpa only [PEnv.access, frame.mod_p] using implementationAt
    cases summaryAt : callee.summary <;>
      simpa only [AccessEnv.callShrinkOwners, contextAtP, implementationAtP, staticAt,
        summaryAt, bind, Except.bind, pure, Except.pure] using query
  exact fun root shrinking capability =>
    callMayShrink_coverage frame checked contextEffect older included query' shrinking capability

private theorem NodeContext.callBody_forbidden {plans : Array (Array DemandPoint)}
    {pc : PlanContext m plans} {path : List Nat} {c : ContextId} {args : List Arg} {origin : OriginId}
    (context : NodeContext pc path (.expression (.call c args origin)) .expression)
    {W : World} {tenv : TEnv} {penv : PEnv} {env : Env} {s s' : St} {future : List VarId}
    {callee : Impl} {ctx : Context} {effect initial : Eff} {ars : List (List RootRef)}
    {before after : RState}
    (moduleOk : ModOk m) (frame : Frame m W tenv penv env s future)
    (access : context.AccessMatches tenv penv) (contextAt : m.contexts[c]? = some ctx)
    (implementationAt : m.impls[ctx.impl]? = some callee) (implementationOk : ImplOk m callee)
    (contextOk : CtxOk m callee ctx) (contextEffect : ContextEff m callee ctx effect)
    (permission : Perm m W) (charged : EffLe (callEffects callee ctx ars initial) W.E)
    (argumentsReplay : rpArgs penv args before = .ok (ars, after))
    (body : MutationFootprint noEnv (fun index root => Gam env W.P (ars[index]?.getD []) root)
      s.nextScope (effectMutationRoots m callee effect) s s') :
    PreservesForbiddenOwnerRoots (m := m) (G := W.G) (env := env) (P := W.P)
      context.expected.forbidden s s' := by
  intro forbidden forbiddenAt root sourceOwner
  let transition := context.phase rfl .mutation
    (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])
  have forbiddenMutation : forbidden ∈ context.callMutationContext.expected.forbidden := by
    change forbidden ∈ transition.context.expected.forbidden
    rw [transition.forbiddenEq]
    exact forbiddenAt
  obtain ⟨effects, effectQuery, requests⟩ := context.callMutationContext.sourceAt.callWholeRootsRequests
    pc.approvals.accessMatches forbiddenMutation
  have accessEq := context.checkedAccess_eq access
  rw [accessEq] at effectQuery
  have contextAtP : penv.access.mod.contexts[c]? = some ctx := by
    simpa only [PEnv.access, frame.mod_p] using contextAt
  have implementationAtP : penv.access.mod.impls[ctx.impl]? = some callee := by
    simpa only [PEnv.access, frame.mod_p] using implementationAt
  simp only [AccessEnv.callEffectOwners, contextAtP, implementationAtP,
    bind, Except.bind, pure, Except.pure] at effectQuery
  obtain ⟨static, staticAt, effectsAt⟩ := (ex_bind_ok _ _ _).mp effectQuery
  have query : (match callee.summary with
      | .unknown => pure (penv.access.unknownOwners static)
      | .known summary => penv.access.targetOwners callee ctx static
          (summary.reads ++ summary.writes ++ summary.grows ++ summary.shrinks ++ summary.rebinds)) = .ok effects := by
    cases summaryAt : callee.summary <;> simpa only [summaryAt, pure, Except.pure] using effectsAt
  have included := rpArgs_accessRoots penv args before ars after static argumentsReplay staticAt
  have disjoint : ∀ owner, owner ∈ effects → DemandRootsDisjoint forbidden.roots owner.roots := by
    intro owner ownerAt
    obtain ⟨approval, _, _, ownerEq, rootsEq, _⟩ := pc.approvals.wholeRootsAt
      context.callMutationContext.expected context.callMutationContext.member _ (requests owner ownerAt)
    simpa only [ownerEq, rootsEq] using approval.disjoint
  obtain ⟨element, values, _, forbiddenRoot, present⟩ := sourceOwner
  apply body
  rintro (denoted | ⟨activation, instanceId, variableId, equal, allocated⟩)
  · obtain ⟨owner, ownerAt, ownerRoot⟩ := callBodyEffectOwnerRoot frame moduleOk implementationOk
      contextOk contextEffect permission charged included query present denoted
    exact (Gam.root_ne_of_no_overlap frame (disjoint owner ownerAt) forbiddenRoot ownerRoot) rfl
  · have older := frame.gam_older forbiddenRoot activation instanceId variableId equal
    exact Nat.not_lt_of_ge allocated older

/-- Argument annotations use either the checked caller context or the empty
initializer context selected by canonical demand access. -/
private theorem NodeContext.callerContext_checked {plans : Array (Array DemandPoint)}
    {pc : PlanContext m plans} {path : List Nat} {node : DemandNode} {phase : DemandPhase}
    (context : NodeContext pc path node phase) (moduleOk : ModOk m)
    (access : context.AccessMatches tenv penv) : CtxOk m penv.impl penv.ctx := by
  have accessEq := context.checkedAccess_eq access
  rcases demandAccess?_cases pc.approvals.accessMatches with
    ⟨ctx, impl, _, contextAt, implementationAt, canonical⟩ |
    ⟨global, _, _, canonical⟩
  · obtain ⟨checkedImpl, checkedAt, checked⟩ := moduleOk.ctx pc.owner ctx contextAt
    rw [implementationAt] at checkedAt
    cases checkedAt
    rw [canonical] at accessEq
    have implEq : impl = penv.impl := congrArg AccessEnv.impl accessEq
    have ctxEq : ctx = penv.ctx := congrArg AccessEnv.ctx accessEq
    rw [← implEq, ← ctxEq]
    exact checked
  · rw [canonical] at accessEq
    have implEq : initImpl = penv.impl := congrArg AccessEnv.impl accessEq
    have ctxEq : initContext = penv.ctx := congrArg AccessEnv.ctx accessEq
    rw [← implEq, ← ctxEq]
    exact initContext_checked m

private theorem NodeContext.callMutation_frame {plans : Array (Array DemandPoint)}
    {pc : PlanContext m plans} {path : List Nat} {c : ContextId} {args : List Arg} {origin : OriginId}
    (context : NodeContext pc path (.expression (.call c args origin)) .expression) :
    context.callMutationContext.expected.frame.active = context.expected.frame.active ∧
      context.callMutationContext.expected.frame.future = context.expected.frame.future := by
  let transition := context.phase rfl .mutation
    (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])
  constructor
  · change transition.context.expected.frame.active = _
    rw [transition.expectedFrameEq]
    exact DemandNode.phaseFrame_active transition.phaseFrameEq
  · change transition.context.expected.frame.future = _
    rw [transition.expectedFrameEq]
    exact DemandNode.phaseFrame_future transition.phaseFrameEq

/-- A checked shrink request resolves every active continuation alias in the
same canonical access environment as the call source. -/
private theorem NodeContext.callFuture_aliasVariable_success {plans : Array (Array DemandPoint)}
    {pc : PlanContext m plans} {path : List Nat} {c : ContextId} {args : List Arg} {origin : OriginId}
    (context : NodeContext pc path (.expression (.call c args origin)) .expression)
    (active : context.ActiveMatches tenv) (owner : DemandOwner)
    (ownerAt : owner ∈ context.callMutationContext.expected.shrinkOwners)
    {x : VarId} (needed : x ∈ context.outputFuture) (visible : x ∈ tenv.visible) :
    ∃ result, pc.approvals.access.aliasVariable x = .ok result := by
  apply (context.callMutation_shrinkSafe owner ownerAt).aliasVariable_succeeds
  · change x ∈ context.callMutationContext.expected.frame.future
    rw [context.callMutation_frame.2]
    exact needed
  · change x ∈ context.callMutationContext.expected.frame.active
    rw [context.callMutation_frame.1]
    exact (active x).mpr visible

/-- A continuation slice or directly passed slice holder has its content
annotation protected by the canonical call mutation approval. -/
private theorem NodeContext.callSliceContent_ne {plans : Array (Array DemandPoint)}
    {pc : PlanContext m plans} {path : List Nat} {c : ContextId} {args : List Arg} {origin : OriginId}
    (context : NodeContext pc path (.expression (.call c args origin)) .expression)
    {W : World} {tenv : TEnv} {penv : PEnv} {env : Env} {s : St} {future : List VarId}
    (frame : Frame m W tenv penv env s future)
    (active : context.ActiveMatches tenv) (access : context.AccessMatches tenv penv)
    {x : VarId} {lv : LocalVar} {mu : Mutability} {E : Ty} {annotation : List RootRef}
    {target ownerRoot : RootInst} (variableAt : env.vars[x]? = some lv)
    (typeEq : lv.ty = .slice mu E) (visible : x ∈ tenv.visible)
    (needed : x ∈ context.outputFuture ∨ ∃ passingMu, Arg.byRef passingMu (.var x) ∈ args)
    (annotationAt : penv.ann x = some annotation) (targetIn : Gam env W.P annotation target)
    (owner : DemandOwner) (ownerMember : owner ∈ context.callMutationContext.expected.shrinkOwners)
    (invalidates : owner.invalidates = true) (ownerIn : Gam env W.ownerP owner.roots ownerRoot) :
    target ≠ ownerRoot := by
  have accessEq := context.checkedAccess_eq access
  have variableP : penv.impl.vars[x]? = some lv := by rw [frame.vars_p]; exact variableAt
  have annotationCtx : (penv.ctx.varRoots.find? (·.1 == x)).map (·.2) = some annotation := annotationAt
  have safe := context.callMutation_shrinkSafe owner ownerMember
  have disjoint : DemandRootsDisjoint owner.roots annotation := by
    rcases needed with continuation | ⟨passingMu, passed⟩
    · let alias : RetainedAlias := ⟨.slice mu E, annotation, .variable x⟩
      have aliasLookup : pc.approvals.access.aliasVariable x = .ok (some alias) := by
        rw [accessEq]
        simp [AccessEnv.aliasVariable, PEnv.access, variableP, typeEq,
          Ty.isRefSlice, Ty.interiorTarget?, AccessEnv.variableRoots, annotationCtx, alias]
        rfl
      have mutationFuture : x ∈ context.callMutationContext.expected.toPoint.future := by
        change x ∈ context.callMutationContext.expected.frame.future
        rw [context.callMutation_frame.2]
        exact continuation
      have mutationActive : x ∈ context.callMutationContext.expected.toPoint.active := by
        change x ∈ context.callMutationContext.expected.frame.active
        rw [context.callMutation_frame.1]
        exact (active x).mpr visible
      exact DemandOwner.conflicts_false_disjoint invalidates (by simp [alias, Ty.interiorTarget?])
        (safe.1.1 x mutationFuture mutationActive alias aliasLookup)
    · obtain ⟨index, bound, argumentEq⟩ := List.mem_iff_getElem.mp passed
      have argumentAt : args[index]? = some (.byRef passingMu (.var x)) :=
        List.getElem?_eq_some_iff.mpr ⟨bound, argumentEq⟩
      let alias : RetainedAlias := ⟨.slice mu E, annotation, .operand (path ++ [index])⟩
      have aliasLookup : pc.approvals.access.aliasArg (path ++ [index]) (.byRef passingMu (.var x)) =
          .ok [alias] := by
        rw [accessEq]
        simp [AccessEnv.aliasArg, AccessEnv.placeType?, PEnv.access, variableP, typeEq,
          AccessEnv.exprRoots, Ty.isRefLike, AccessEnv.variableRoots, annotationCtx, alias]
        rfl
      obtain ⟨aliases, aliasesChecked, aliasesRetained⟩ :=
        context.callMutation_retains_argument index (.byRef passingMu (.var x)) argumentAt
      have aliasesEq : aliases = [alias] := Except.ok.inj (aliasesChecked.symm.trans aliasLookup)
      rw [aliasesEq] at aliasesRetained
      exact DemandOwner.conflicts_false_disjoint invalidates (by simp [alias, Ty.interiorTarget?])
        (safe.1.2 alias (aliasesRetained alias List.mem_cons_self))
  exact (Gam.root_ne_of_no_overlap frame disjoint (ownerIn.mono frame.ownerSubset) targetIn).symm

/-- Inherited slice targets use the caller's whole-plan protection after
scope age excludes current locals. New local holders use the exact call point. -/
private theorem NodeContext.callD_shrinkProtected {plans : Array (Array DemandPoint)}
    {pc : PlanContext m plans} {path : List Nat} {c : ContextId} {args : List Arg} {origin : OriginId}
    (context : NodeContext pc path (.expression (.call c args origin)) .expression)
    {W : World} {tenv : TEnv} {penv : PEnv} {env : Env} {s : St} {future : List VarId}
    {observation : Observation} {retained : List RetainedAlias} {shrinking : RootInst → Prop}
    (frame : Frame m W tenv penv env s future)
    (active : context.ActiveMatches tenv) (access : context.AccessMatches tenv penv)
    (protectedSlices : ShrinkProtected W.D W.A
      (fun root => PlanMayShrink pc W.ownerP root ∧ OwnerCap m observation root))
    (capabilities : ∀ root, shrinking root → OwnerCap m
      (callObservation (m := m) observation W tenv env context.outputFuture retained s.store) root)
    (coverage : ∀ root, shrinking root → ∃ owner,
      owner ∈ context.callMutationContext.expected.shrinkOwners ∧ owner.invalidates = true ∧
      Gam env W.ownerP owner.roots root) :
    ShrinkProtected (callD W tenv env context.outputFuture args) (callA W penv env) shrinking := by
  intro holder element target demanded allowed root shrink
  obtain ⟨owner, ownerMember, invalidates, ownerIn⟩ := coverage root shrink
  rcases demanded with inherited | ⟨x, lv, si, mu, variableAt, scope, rfl, typeEq, visible, needed⟩
  · have inheritedAllowed : W.A holder target := by
      rcases allowed with ⟨_, inheritedAllowed⟩ | ⟨x, lv, si, ann, _, scope, equal, _⟩
      · exact inheritedAllowed
      · subst holder
        exact False.elim (frame.not_outer scope ⟨element, inherited⟩)
    intro equal
    have before : BeforeBase W.base root := by
      rw [← equal]
      exact frame.allowed_beforeBase inherited inheritedAllowed
    have capability := OwnerCap.callObservation_beforeBase frame before (capabilities root shrink)
    have external := frame.gam_noEnv_of_beforeBase before ownerIn
    have phaseEq : context.callMutationContext.expected.phase = .mutation := by
      obtain ⟨_, _, _, _, _, phaseEq⟩ := context.callMutationContext.sourceAt
      exact phaseEq
    have planned := PlanMayShrink.ofExpected context.callMutationContext.member phaseEq
      ownerMember ⟨invalidates, external⟩
    exact protectedSlices holder element target inherited inheritedAllowed root ⟨planned, capability⟩ equal
  · rcases allowed with ⟨outer, _⟩ |
      ⟨x', lv', si', ann, variableAt', _, equal, annotationAt, targetIn, _⟩
    · exact False.elim (frame.not_outer scope outer)
    · cases equal
      rw [variableAt] at variableAt'
      cases variableAt'
      exact context.callSliceContent_ne frame active access variableAt typeEq visible needed
        annotationAt targetIn owner ownerMember invalidates ownerIn

/-- Inherited observations only target roots older than this activation, so
the exact call mutation owners specialize back to the caller's whole plan. -/
private theorem NodeContext.callInherited_observed {plans : Array (Array DemandPoint)}
    {pc : PlanContext m plans} {path : List Nat} {c : ContextId} {args : List Arg} {origin : OriginId}
    (context : NodeContext pc path (.expression (.call c args origin)) .expression)
    {W : World} {tenv : TEnv} {penv : PEnv} {env : Env} {s : St} {future : List VarId}
    {observation : Observation} {retained : List RetainedAlias} {shrinking : RootInst → Prop}
    (frame : Frame m W tenv penv env s future)
    (safe : ObservedSafe m W
      (fun root => PlanMayShrink pc W.ownerP root ∧ OwnerCap m observation root) observation s.store)
    (capabilities : ∀ root, shrinking root → OwnerCap m
      (callObservation (m := m) observation W tenv env context.outputFuture retained s.store) root)
    (coverage : ∀ root, shrinking root → ∃ owner,
      owner ∈ context.callMutationContext.expected.shrinkOwners ∧ owner.invalidates = true ∧
      Gam env W.ownerP owner.roots root) :
    ObservedSafe m { W with base := s.nextScope } shrinking observation s.store := by
  have mapped : ∀ root, BeforeBase W.base root → shrinking root →
      PlanMayShrink pc W.ownerP root ∧ OwnerCap m observation root := by
    intro root older shrink
    obtain ⟨owner, ownerAt, invalidates, ownerIn⟩ := coverage root shrink
    have phaseEq : context.callMutationContext.expected.phase = .mutation := by
      obtain ⟨_, _, _, _, _, phaseEq⟩ := context.callMutationContext.sourceAt
      exact phaseEq
    exact ⟨PlanMayShrink.ofExpected context.callMutationContext.member phaseEq ownerAt
      ⟨invalidates, frame.gam_noEnv_of_beforeBase older ownerIn⟩,
      OwnerCap.callObservation_beforeBase frame older (capabilities root shrink)⟩
  refine ⟨safe.typed, ?_, ?_, ?_, ?_, safe.holderTypes⟩
  · exact (safe.base_mono frame.base_le).rootsOlder
  · exact (safe.base_mono frame.base_le).valuesOlder
  · intro holder type value rootObserved present interior target targeted shrink
    have age := frame.inv.age holder value present target targeted
    have older := safe.rootsOlder holder type rootObserved
    have targetOlder : BeforeBase W.base target := by
      cases target with
      | global _ => trivial
      | «local» activation instanceId variableId =>
        cases holder with
        | global _ => cases age
        | «local» holderActivation holderInstance holderVariable =>
          exact Nat.lt_of_le_of_lt age older
    exact safe.rootsProtected holder type value rootObserved present interior target targeted
      (mapped target targetOlder shrink)
  · intro value type observed interior target targeted shrink
    exact safe.valuesProtected value type observed interior target targeted
      (mapped target (safe.valuesOlder value type observed target targeted) shrink)

private theorem callDemandedHeader_notShrinking {W : World} {tenv : TEnv} {penv : PEnv}
    {env : Env} {s : St} {future : List VarId} {observation : Observation}
    {shrinking : RootInst → Prop} {holder : RootInst} {element : Ty}
    (frame : Frame m W tenv penv env s future)
    (observed : Observed m W.G observation s.store)
    (capabilities : ∀ root, shrinking root → OwnerCap m observation root)
    (demanded : W.D holder element) : ¬ shrinking holder := by
  obtain ⟨activation, instanceId, variableId, rfl, _⟩ := frame.dOut holder element demanded
  obtain ⟨value, present, typed, _⟩ := frame.sa _ element demanded
  intro shrink
  obtain ⟨ownerType, ownerObserved, ownerElement, ownerTypeEq⟩ := capabilities _ shrink
  obtain ⟨ownerValue, ownerPresent, ownerTyped⟩ := observed.roots _ ownerType ownerObserved
  rw [present] at ownerPresent
  cases ownerPresent
  have reference : IsRef value := typed.isRef rfl
  rcases ownerTypeEq with rfl | rfl
  · exact ownerTyped.not_ref rfl reference
  · exact ownerTyped.not_ref rfl reference

/-- Demanded slice references protect their contents through parameter facts;
their runtime header target is itself a demanded slice holder. Other interior
bindings use the exact future-variable approval. -/
private theorem NodeContext.callVariable_notShrinking {plans : Array (Array DemandPoint)}
    {pc : PlanContext m plans} {path : List Nat} {c : ContextId} {args : List Arg} {origin : OriginId}
    (context : NodeContext pc path (.expression (.call c args origin)) .expression)
    {W : World} {tenv : TEnv} {penv : PEnv} {env : Env} {s : St} {future : List VarId}
    {observation : Observation} {shrinking : RootInst → Prop}
    {x : VarId} {lv : LocalVar} {si : ScopeInst} {value : Val}
    (frame : Frame m W tenv penv env s future)
    (active : context.ActiveMatches tenv) (access : context.AccessMatches tenv penv)
    (observed : Observed m W.G observation s.store)
    (capabilities : ∀ root, shrinking root → OwnerCap m observation root)
    (coverage : ∀ root, shrinking root → ∃ owner,
      owner ∈ context.callMutationContext.expected.shrinkOwners ∧ owner.invalidates = true ∧
      Gam env W.ownerP owner.roots root)
    (variableAt : env.vars[x]? = some lv) (scope : env.scopes.lookup lv.scope = some si)
    (present : s.store.roots[RootInst.local env.act si x]? = some value)
    (visible : x ∈ tenv.visible) (needed : x ∈ context.outputFuture)
    (interior : lv.ty.interiorTarget?.isSome = true) :
    ∀ target, Targets value target → ¬ shrinking target := by
  have accessEq := context.checkedAccess_eq access
  have variableP : penv.impl.vars[x]? = some lv := by rw [frame.vars_p]; exact variableAt
  intro target targeted shrink
  obtain ⟨annotation, annotationAt, targetIn⟩ := frame.rooted x lv si value
    variableAt scope present target targeted
  cases sliceRef : lv.ty.isRefSlice with
  | true =>
    obtain ⟨owner, ownerAt, _, _⟩ := coverage target shrink
    obtain ⟨result, checked⟩ :=
      context.callFuture_aliasVariable_success active owner ownerAt needed visible
    rw [accessEq] at checked
    have content : ∃ roots, penv.cont x = some roots := by
      cases contentAt : penv.cont x with
      | some roots => exact ⟨roots, rfl⟩
      | none =>
        simp [AccessEnv.aliasVariable, PEnv.access, variableP, sliceRef,
          AccessEnv.contentRoots] at checked
        simp only [PEnv.cont] at contentAt
        rw [contentAt] at checked
        cases checked
    obtain ⟨content, contentAt⟩ := content
    have parameter := frame.pref x content contentAt
    rw [parameter.2.1] at annotationAt
    cases annotationAt
    have parameterTarget : W.P x target := by
      obtain ⟨root, member, denoted⟩ := targetIn
      simp only [List.mem_singleton] at member
      subst root
      exact denoted
    cases typeEq : lv.ty with
    | ref mu referred =>
      cases referred with
      | slice sliceMu element =>
        exact callDemandedHeader_notShrinking frame observed capabilities
          (parameter.2.2 lv mu sliceMu element variableAt typeEq target parameterTarget).1 shrink
      | _ => simp [typeEq, Ty.isRefSlice] at sliceRef
    | _ => simp [typeEq, Ty.isRefSlice] at sliceRef
  | false =>
    obtain ⟨owner, ownerAt, invalidates, ownerIn⟩ := coverage target shrink
    let alias : RetainedAlias := ⟨lv.ty, annotation, .variable x⟩
    have annotationCtx : (penv.ctx.varRoots.find? (·.1 == x)).map (·.2) = some annotation :=
      annotationAt
    have aliasLookup : pc.approvals.access.aliasVariable x = .ok (some alias) := by
      rw [accessEq]
      simp [AccessEnv.aliasVariable, PEnv.access, variableP, sliceRef, interior,
        AccessEnv.variableRoots, annotationCtx]
      rfl
    have mutationFuture : x ∈ context.callMutationContext.expected.toPoint.future := by
      change x ∈ context.callMutationContext.expected.frame.future
      rw [context.callMutation_frame.2]
      exact needed
    have mutationActive : x ∈ context.callMutationContext.expected.toPoint.active := by
      change x ∈ context.callMutationContext.expected.frame.active
      rw [context.callMutation_frame.1]
      exact (active x).mpr visible
    have safe := context.callMutation_shrinkSafe owner ownerAt
    have disjoint := DemandOwner.conflicts_false_disjoint invalidates interior
      (safe.1.1 x mutationFuture mutationActive alias aliasLookup)
    exact (Gam.root_ne_of_no_overlap frame disjoint (ownerIn.mono frame.ownerSubset) targetIn) rfl

/-- Limited headers cannot invalidate physical sampled runs. A possible
shrink of a global also requires that global to be initialized. -/
private theorem callLimited_notShrinking {G : Nat} {state : St} {demand : RootInst → Prop}
    {observation : Observation} {shrinking : RootInst → Prop}
    {location : Loc} {mu : Mutability} {E : Ty} {capacity : Nat}
    (invariant : StoreInv m G state demand) (observed : Observed m G observation state.store)
    (capabilities : ∀ root, shrinking root → OwnerCap m observation root)
    (initialized : ∀ global, shrinking (.global global) → global < G)
    (typed : HasTy m G state.store (.ref location) (.ref mu (.limited E capacity))) :
    ¬ shrinking location.root := by
  have pathEq := typed.ownerHeader (by simp [Ty.ownerElem?])
  obtain ⟨target, equal, ordinary | header⟩ := typed
  all_goals cases Val.ref.inj equal
  · obtain ⟨_, (limited | unbound), _⟩ := ordinary
    · have rootLimited : LocTy state.store ⟨location.root, []⟩ (.limited E capacity) := by
        cases location with
        | mk root path =>
          change path = [] at pathEq
          cases pathEq
          exact limited
      intro shrink
      have capability := capabilities location.root shrink
      cases rootEq : location.root with
      | «local» activation instanceId variableId =>
        rw [rootEq] at rootLimited capability
        exact (OwnerCap.not_localLimited observed rootLimited) capability
      | global global =>
        rw [rootEq] at rootLimited capability
        obtain ⟨gl, declaration, _⟩ := capability
        exact (OwnerCap.not_globalLimited invariant declaration
          (initialized global (by simpa [rootEq] using shrink)) rootLimited)
          (by simpa [rootEq] using capabilities location.root shrink)
    · obtain ⟨global, gl, uninitialized, rootEq, _, _⟩ := unbound
      intro shrink
      exact (Nat.not_lt_of_ge uninitialized) (initialized global (by simpa [rootEq] using shrink))
  · simp [Ty.isSlice] at header

/-- Retained arguments exclude checked shrinking owners. Physical limited
runs are preserved by their backing header's declared capability. -/
private theorem NodeContext.callRetained_notShrinking {plans : Array (Array DemandPoint)}
    {pc : PlanContext m plans} {path : List Nat} {c : ContextId} {args : List Arg} {origin : OriginId}
    (context : NodeContext pc path (.expression (.call c args origin)) .expression)
    {W : World} {tenv : TEnv} {penv : PEnv} {env : Env} {s : St} {future : List VarId}
    {observation : Observation} {retained : List RetainedAlias} {shrinking : RootInst → Prop}
    (frame : Frame m W tenv penv env s future)
    (observed : Observed m W.G observation s.store)
    (capabilities : ∀ root, shrinking root → OwnerCap m observation root)
    (initialized : ∀ global, shrinking (.global global) → global < W.G)
    (retainedSubset : ∀ alias, alias ∈ retained →
      alias ∈ context.callMutationContext.expected.frame.retained)
    (coverage : ∀ root, shrinking root → ∃ owner,
      owner ∈ context.callMutationContext.expected.shrinkOwners ∧ owner.invalidates = true ∧
      Gam env W.ownerP owner.roots root) :
    ∀ v T, callRetainedValues (m := m) W env retained s.store v T →
      T.interiorTarget?.isSome = true → ∀ target, Targets v target → ¬ shrinking target := by
  intro value type retainedValue interior target targeted shrink
  rcases retainedValue with ⟨alias, retainedAt, rfl, realized⟩ |
    ⟨alias, mu, element, capacity, location, start, len, _, aliasType, realized, _, rfl, rfl⟩
  · obtain ⟨owner, ownerAt, invalidates, ownerIn⟩ := coverage target shrink
    have safe := context.callMutation_shrinkSafe owner ownerAt
    have disjoint := DemandOwner.conflicts_false_disjoint invalidates interior
      (safe.1.2 alias (retainedSubset alias retainedAt))
    exact (Gam.root_ne_of_no_overlap frame disjoint (ownerIn.mono frame.ownerSubset) (realized.2 target targeted)) rfl
  · have typed := realized.1
    rw [aliasType] at typed
    change location.root = target at targeted
    subst target
    exact callLimited_notShrinking frame.inv observed capabilities initialized typed
      shrink

/-- Broad argument-root interpretations classify initialized local storage
through the same boundary observation used to preserve caller bindings. -/
private theorem Frame.callObservation_classified {W : World} {tenv : TEnv} {penv : PEnv}
    {env : Env} {s : St} {future continuation : List VarId} {args : List Arg}
    {ars : List (List RootRef)} {observation : Observation} {retained : List RetainedAlias}
    (frame : Frame m W tenv penv env s future)
    (declarations : ArgumentRootDeclarations m penv.impl tenv env ars)
    (inherited : ClassifiedParameters m W.P W.D observation s.store) :
    ClassifiedParameters m (fun i root => Gam env W.P (ars[i]?.getD []) root)
      (callD W tenv env continuation args)
      (callObservation (m := m) observation W tenv env continuation retained s.store) s.store := by
  apply frame.classifiedArgumentRoots declarations inherited
  · exact fun _ _ observed => Or.inl observed
  · exact fun _ _ storage present => Or.inr (Or.inl (Or.inr ⟨storage, present⟩))
  · exact fun _ _ demanded => Or.inl demanded

/-- The boundary combines inherited observations, continuation bindings,
initialized storage and sampled arguments under the checked mutation owners. -/
private theorem NodeContext.callObservation_observed {plans : Array (Array DemandPoint)}
    {pc : PlanContext m plans} {path : List Nat} {c : ContextId} {args : List Arg} {origin : OriginId}
    (context : NodeContext pc path (.expression (.call c args origin)) .expression)
    {W : World} {tenv : TEnv} {penv : PEnv} {env : Env} {s : St} {future : List VarId}
    {observation : Observation} {retained : List RetainedAlias} {shrinking : RootInst → Prop}
    (frame : Frame m W tenv penv env s future)
    (active : context.ActiveMatches tenv) (access : context.AccessMatches tenv penv)
    (futureSubset : ∀ x, x ∈ context.outputFuture → x ∈ future)
    (safe : ObservedSafe m W
      (fun root => PlanMayShrink pc W.ownerP root ∧ OwnerCap m observation root) observation s.store)
    (protectedSlices : ShrinkProtected W.D W.A
      (fun root => PlanMayShrink pc W.ownerP root ∧ OwnerCap m observation root))
    (capabilities : ∀ root, shrinking root → OwnerCap m
      (callObservation (m := m) observation W tenv env context.outputFuture retained s.store) root)
    (initialized : ∀ global, shrinking (.global global) → global < W.G)
    (retainedSubset : ∀ alias, alias ∈ retained →
      alias ∈ context.callMutationContext.expected.frame.retained)
    (coverage : ∀ root, shrinking root → ∃ owner,
      owner ∈ context.callMutationContext.expected.shrinkOwners ∧ owner.invalidates = true ∧
      Gam env W.ownerP owner.roots root) :
    ObservedSafe m { W with base := s.nextScope } shrinking
      (callObservation (m := m) observation W tenv env context.outputFuture retained s.store) s.store := by
  have sourceFalse := (safe.weakenShrinking (shrinking' := fun _ => False)
    (fun _ impossible => False.elim impossible)).base_mono frame.base_le
  have typed := (callObservation_safe (retained := retained) frame futureSubset sourceFalse
    (fun _ _ _ _ _ _ _ _ impossible => False.elim impossible)
    (fun _ _ _ _ _ _ impossible => False.elim impossible)).typed
  have inherited := context.callInherited_observed frame safe capabilities coverage
  have sliceProtection := context.callD_shrinkProtected frame active access protectedSlices capabilities coverage
  apply callObservation_safe frame futureSubset inherited
  · intro holder type value rootObserved present interior target targeted
    rcases rootObserved with (⟨x, lv, si, visible, needed, variableAt, scope, rfl, rfl⟩ |
      ⟨⟨x, lv, si, variableAt, scope, rfl, nonref, rfl⟩, _⟩) | ⟨element, demanded, rfl⟩
    · exact context.callVariable_notShrinking frame active access typed capabilities coverage
        variableAt scope present visible needed interior target targeted
    · cases typeEq : lv.ty <;> simp [typeEq, Ty.isRefLike, Ty.interiorTarget?] at nonref interior
    · obtain ⟨stored, storedAt, _, allowed⟩ := frame.sa holder element demanded
      rw [present] at storedAt
      cases storedAt
      intro shrink
      exact sliceProtection holder element target (Or.inl demanded)
        (Or.inl ⟨⟨element, demanded⟩, allowed target targeted⟩) target shrink rfl
  · exact context.callRetained_notShrinking frame typed capabilities initialized retainedSubset coverage

set_option maxHeartbeats 1600000 in
/-- At a call, each parameter of the callee that refers to a slice variable
points at a slice variable the callee may rewrite, whose slices are rooted
exactly within the parameter's content roots as the callee reads them. -/
private theorem call_pref {W : World} {tenv : TEnv} {penv : PEnv} {env : Env} {s1 : St}
    {future continuation : List VarId}
    (hF1 : Frame m W tenv penv env s1 future) {callee : Impl} {cctx : Context} {args : List Arg}
    {ars : List (List RootRef)} {vals : List Val} (himplOk : ImplOk m callee)
    (hctxOk : CtxOk m callee cctx)
    (hcheck : ∀ i, i < args.length → checkContent penv cctx args ars i = .ok ())
    (hsize : callee.params.size = args.length) (hlen : vals.length = args.length)
    (hall : ∀ (i : Nat) (v : Val), vals[i]? = some v → ∃ (p : Param) (pv : LocalVar)
        (ar : List RootRef) (a : Arg) (ty : Ty) (tn0 tn1 : Nat) (rst0 rst1 : RState),
      callee.params.toList[i]? = some p ∧ callee.vars[p.var]? = some pv ∧
      ars[i]? = some ar ∧ HasTy m W.G s1.store v pv.ty ∧ (∀ r, Targets v r → Gam env W.P ar r) ∧
      OwnerRooted env W.ownerP ar v pv.ty ∧ args[i]? = some a ∧ ArgTy tenv a tn0 ty tn1 ∧ ty.passableTo pv.ty = true ∧
      ArgRp penv a rst0 ar rst1) :
    ∀ x cont, (cctx.contentRoots.find? (·.1 == x)).map (·.2) = some cont →
      PRef (fun j r => Gam env W.P (ars[j]?.getD []) r)
        (callD W tenv env continuation args) (callA W penv env)
        ⟨m, callee, cctx, []⟩ callee.vars x cont := by
  intro x cont hfind
  obtain ⟨hxlt, hannx, hnl⟩ := hctxOk.content x cont hfind
  refine ⟨hnl, hannx, ?_⟩
  intro lv mu mu' E hlv hty r hPc
  have hxa : x < args.length := hsize ▸ hxlt
  obtain ⟨v, hv⟩ : ∃ v, vals[x]? = some v := ⟨vals[x]'(hlen ▸ hxa), List.getElem?_eq_getElem _⟩
  obtain ⟨p, pv, ar, a, ty, tn0, tn1, rst0, rst1, g1, g2, g3, _, _, _, g6, g7, g8, g9⟩ := hall x v hv
  have hp_x : callee.params[x]? = some p := by simpa using g1
  obtain ⟨hvar, lv', hlv', _, hlst⟩ := himplOk.params x p hp_x
  rw [hvar, hlv] at g2
  cases g2
  rw [hlv] at hlv'
  cases hlv'
  have hEfl : E.flat = true := by
    simpa [hty, Ty.paramOk, Ty.storable, Ty.refTarget, Ty.isRefSlice] using hlst
  have hPc' : Gam env W.P ar r := by simpa [g3] using hPc
  obtain ⟨inst, hmap, hcase⟩ := checkContent_ok _ _ _ _ x cont (hcheck x hxa) hfind
  have hgi := gam_inst (env := env) (P := W.P) hmap
  rcases hcase with ⟨mua, sv, anns, ha, hanns, hsub, hb⟩ | ⟨mua, q, cq, ha, hcq, hsub1, hsub2⟩
  · -- A slice variable of the caller itself.
    rw [g6] at ha
    cases ha
    obtain ⟨t, mub, htp, _, rfl⟩ := g7
    simp only [tyPlace] at htp; inv at htp
    obtain ⟨hvis, lvs, hlvs, rfl, _, _⟩ := htp
    rw [hty] at g8
    simp only [Ty.passableTo, Bool.and_eq_true, beq_iff_eq] at g8
    have hts : lvs.ty = .slice mu' E := g8.1
    have g9' : rpPlace penv (.var sv) rst0 = .ok (ar, rst1) := g9
    simp only [rpPlace] at g9'; inv at g9'
    obtain ⟨rfl, _⟩ := g9'
    obtain ⟨q', hq', hrq'⟩ := hPc'
    simp only [List.mem_singleton] at hq'
    subst hq'
    obtain ⟨lv2, si, k1, k2, rfl⟩ := hrq'
    rw [hF1.vars_t] at hlvs
    rw [hlvs] at k1
    cases k1
    refine ⟨Or.inr ⟨sv, lvs, si, mu', hlvs, k2, rfl, hts, hvis,
      Or.inr ⟨mua, List.mem_of_getElem? g6⟩⟩, ?_, ?_⟩
    · rintro t (⟨hd, _⟩ | ⟨x', lv', si', ann', _, _, e, ha', hg', _⟩)
      · exact absurd hd (hF1.not_outer k2)
      · cases e
        rw [hanns] at ha'
        cases ha'
        exact (hgi t).1 (hg'.subset hsub)
    · intro t ht
      have hgt := (hgi t).2 ht
      obtain ⟨⟨ann, ha', hga⟩, hold⟩ := bind_roots_sem hF1 hb hlvs k2 (v := .ref ⟨t, []⟩)
        (fun r' hr' => by cases hr'; exact hgt) t rfl
      exact Or.inr ⟨sv, lvs, si, ann, hlvs, k2, rfl, ha', hga, hold⟩
  · -- The pointee of a reference the caller was given.
    rw [g6] at ha
    cases ha
    obtain ⟨t, mub, htp, _, rfl⟩ := g7
    rw [hty] at g8
    simp only [Ty.passableTo, Bool.and_eq_true, beq_iff_eq] at g8
    obtain ⟨rfl, _⟩ := g8
    cases hs : sliceRefTy tenv (.read (.var q)) with
    | none =>
      simp only [tyPlace, hs] at htp; inv at htp
      obtain ⟨te, t1', ⟨te', t0, hte, hnr, rfl, rfl⟩, htp⟩ := htp
      cases te <;> inv at htp
      obtain ⟨rfl, _, _⟩ := htp
      simp [Ty.isRefSlice, hEfl] at hnr
    | some tyq =>
      obtain ⟨q', lvq, mu0, mus, Eq, e, hqvis, hlvq, htyq, hflq, rfl⟩ := sliceRefTy_some hs
      cases e
      simp only [tyPlace, hs] at htp
      rw [htyq] at htp; inv at htp
      obtain ⟨hts, _, _⟩ := htp
      cases hts
      rw [hF1.vars_t] at hlvq
      have g9' : rpPlace penv (.deref (.read (.var q))) rst0 = .ok (ar, rst1) := g9
      simp only [rpPlace] at g9'
      simp only [rpExpr] at g9'; inv at g9'
      obtain ⟨rp, r1, _, r2, _, hrr⟩ := g9'
      obtain ⟨_, hroots⟩ := readRoots_ok _ _ _ _ hrr
      obtain ⟨hnlq, hannq, hprq⟩ := hF1.pref q cq hcq
      have har : ar = [.param q] := by
        rcases hroots with ⟨x', lv', e, _, _, ha'⟩ | ⟨x', e, _⟩ | ⟨_, hnr, _⟩
        · cases e
          rw [hannq] at ha'
          exact (Option.some.inj ha').symm
        · cases e
        · have := hnr q lvq rfl (by rw [hF1.vars_p]; exact hlvq)
          rw [htyq] at this; simp [Ty.isRefLike] at this
      subst har
      obtain ⟨q', hq', hrq'⟩ := hPc'
      simp only [List.mem_singleton] at hq'
      subst hq'
      obtain ⟨hD, hFRq, hFWq⟩ := hprq lvq mu0 mu' E hlvq htyq r hrq'
      refine ⟨Or.inl hD, ?_, ?_⟩
      · rintro t (⟨_, hA⟩ | ⟨x', lv', si', ann', _, hl', e, _⟩)
        · exact (hgi t).1 ((gam_of_noEnv (hFRq t hA)).subset hsub2)
        · subst e
          exact absurd ⟨E, hD⟩ (hF1.not_outer hl')
      · intro t ht
        exact Or.inl ⟨⟨E, hD⟩, hFWq t (gam_noEnv (((hgi t).2 ht).subset hsub1) hnlq)⟩

/-- Once the exact callee observations and protection have been established,
call entry and return preserve the caller through the same checked plan array. -/
private theorem callBody_spec {plans path c args origin} (ihCall : CallSpec m prof plans n)
    (ec : EvaluationContext m plans path (.expression (.call c args origin)) .expression)
    (observation : Observation) (W : World) (tenv : TEnv) (penv : PEnv) (env : Env) (s : St)
    (ctx : Context) (callee : Impl) (E : Eff) (vals : List Val) (ars : List (List RootRef))
    (retained : List RetainedAlias) (ty : Ty) (rho : List RootRef) (initialEffects : Eff)
    (contextAt : m.contexts[c]? = some ctx) (implementationAt : m.impls[ctx.impl]? = some callee)
    (implementationChecked : ImplOk m callee) (contextChecked : CtxOk m callee ctx)
    (effectReplay : ContextEff m callee ctx E)
    (active : ec.ActiveMatches tenv) (access : ec.AccessMatches tenv penv)
    (protectedSlices : ShrinkProtected W.D W.A (ec.mayShrink W.ownerP observation))
    (sourceSafe : ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s.store)
    (sourceClassified : m.profile = .shrink → ClassifiedParameters m W.P W.D observation s.store)
    (permission : Perm m W)
    (frame : Frame m W tenv penv env s (callArgsFuture ec args.length []))
    (size : callee.params.size = args.length) (length : vals.length = args.length)
    (argumentsChecked : ∀ i, i < callee.params.size → checkArgRoots callee ctx ars i = .ok ())
    (contentsChecked : ∀ i, i < args.length → checkContent penv ctx args ars i = .ok ())
    (sampled : ∀ (i : Nat) (v : Val), vals[i]? = some v →
      ∃ (p : Param) (pv : LocalVar) (ar : List RootRef) (a : Arg) (t : Ty)
        (tn0 tn1 : Nat) (rst0 rst1 : RState),
      callee.params.toList[i]? = some p ∧ callee.vars[p.var]? = some pv ∧
      ars[i]? = some ar ∧ HasTy m W.G s.store v pv.ty ∧
      (∀ r, Targets v r → Gam env W.P ar r) ∧
      OwnerRooted env W.ownerP ar v pv.ty ∧ args[i]? = some a ∧
      ArgTy tenv a tn0 t tn1 ∧ t.passableTo pv.ty = true ∧ ArgRp penv a rst0 ar rst1)
    (resultType : (callee.results.toList = [] ∧ ty = .unit) ∨ callee.results.toList = [ty])
    (resultReplay : callResultRoots callee ctx ars = .ok rho)
    (effects : EffLe (callEffects callee ctx ars initialEffects) W.E)
    (retainedSubset : ∀ alias, alias ∈ ec.retained → alias ∈ retained) :
    let Pc := fun i root => Gam env W.P (ars[i]?.getD []) root
    let boundary := callObservation (m := m) observation W tenv env ec.outputFuture retained s.store
    let root := ec.calleeContext callee contextAt implementationAt
    let calleeWorld := World.mk W.G Pc (callOwnerP W callee env ars) E s.nextScope
      (callD W tenv env ec.outputFuture args) (callA W penv env)
    ObservedSafe m calleeWorld (root.mayShrink (callOwnerP W callee env ars) boundary) boundary s.store →
    (m.profile = .shrink → ClassifiedParameters m Pc
      (callD W tenv env ec.outputFuture args) boundary s.store) →
    ShrinkProtected (callD W tenv env ec.outputFuture args) (callA W penv env)
      (root.mayShrink (callOwnerP W callee env ars) boundary) →
    Sat (enterCall n ⟨prof, m⟩ env.depth c vals) s (fun value s' =>
      Frame m W tenv penv env s' ec.outputFuture ∧ Footprint (insts env) (Dset W) s s' ∧
      PreservesRootTypes m W.G observation.roots s.store s'.store ∧
      PreservesValues m W.G observation.values s.store s'.store ∧
      ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s'.store ∧
      RetainsAliases m W env s.store s'.store ec.retained ∧ PilotStoreLe m s s' ∧
      HasTy m W.G s'.store value ty ∧ (∀ r, Targets value r → Gam env W.P rho r) ∧
      (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s'.store) ∧
      OwnerRooted env W.ownerP rho value ty ∧
      MutationFootprint noEnv (fun i root => Gam env W.P (ars[i]?.getD []) root)
        s.nextScope (effectMutationRoots m callee E) s s') := by
  dsimp only
  intro boundarySafe boundaryClassified boundaryProtected
  have futureSubset : ∀ x, x ∈ ec.outputFuture → x ∈ callArgsFuture ec args.length [] := by
    cases ec with
    | pilot _ _ =>
      intro x member
      simpa [callArgsFuture, EvaluationContext.outputFuture, DemandNode.visibleAfter] using member
    | shrink _ _ =>
      intro x member
      simp only [callArgsFuture, List.flatMap_nil, List.append_nil, List.mem_append]
      exact Or.inr member
  have outer : OuterOk m W.G (callD W tenv env ec.outputFuture args) (callA W penv env) s :=
    callOuterOk frame (fun x lv mu element variableAt typeEq visible needed =>
      callArgsFuture_sliceHolder ec active access frame.vars_t variableAt typeEq visible needed)
  have invariant := (frame.callDemand boundarySafe.typed
    (fun root element hd => by obtain ⟨v, hv, ht, _⟩ := outer root element hd; exact ⟨v, hv, ht⟩)).observationDemand
  have call := ihCall W.G (fun i root => Gam env W.P (ars[i]?.getD []) root)
    (callOwnerP W callee env ars) (callD W tenv env ec.outputFuture args) (callA W penv env) env.depth c vals s ctx callee E
    (callObservation (m := m) observation W tenv env ec.outputFuture retained s.store)
    (ec.calleeContext callee contextAt implementationAt)
    (ec.calleeContext_owner callee contextAt implementationAt) effectReplay contextAt implementationAt
    (frame.callOwnerP_subset callee ars) (callOwnerP.shape W callee env ars)
    invariant boundarySafe boundaryClassified boundaryProtected
    (by rw [length]; exact size.symm)
    (by
      intro i value valueAt
      obtain ⟨lv, variableAt, typed, roots⟩ := callValues_ok implementationChecked
        contextChecked argumentsChecked (fun j v sampledAt => by
          obtain ⟨p, pv, ar, _, _, _, _, _, _, hp, hv, hr, ht, roots, _⟩ := sampled j v sampledAt
          exact ⟨p, pv, ar, hp, hv, hr, ht, roots⟩) i value valueAt
      refine ⟨lv, variableAt, typed, ?_, roots⟩
      exact callValues_ownerRooted implementationChecked (fun j v sampledAt => by
        obtain ⟨p, pv, ar, _, _, _, _, _, _, hp, hv, hr, _, _, owner, _⟩ := sampled j v sampledAt
        exact ⟨p, pv, ar, hp, hv, hr, owner⟩) i value lv valueAt variableAt)

    (fun i activation instanceId variableId denoted => frame.gam_older denoted _ _ _ rfl)
    (callA_older frame) (callD_out frame) (callD_fun frame) outer
    (call_pref frame implementationChecked contextChecked contentsChecked size length sampled)
    (callPermission permission contextChecked effects)
  apply call.mono
  intro value final post
  obtain ⟨invariant, transition, _, pilot, outer, returned, roots, _, ownerResult, mutation⟩ := post
  obtain ⟨callerFrame, callerFootprint, callerRoots, callerValues, callerSafe, callerRetained,
    callerClassified⟩ := frame.callBoundary_return sourceSafe sourceClassified protectedSlices
      transition invariant outer futureSubset retainedSubset
  have ownerRooted := callResult_ownerRooted resultType resultReplay
    (fun ownerType root targeted => by
      have single : callee.results.toList = [ty] := by
        rcases resultType with ⟨_, unit⟩ | single
        · rw [unit] at ownerType
          obtain ⟨mu, element, impossible | impossible⟩ := ownerType <;> cases impossible
        · exact single
      obtain ⟨declared, declaredAt, rooted⟩ := ownerResult ty single
      exact ⟨declared, declaredAt, rooted ownerType root targeted⟩)
  obtain ⟨typed, roots⟩ := callResult_ok resultType resultReplay returned roots
  exact ⟨callerFrame, callerFootprint, callerRoots, callerValues, callerSafe, callerRetained,
    pilot, typed, roots, callerClassified, ownerRooted, mutation⟩

private theorem callObservation_callD_holderTypes
    {W : World} {tenv : TEnv} {penv : PEnv} {env : Env} {s : St}
    {future continuation : List VarId} {args : List Arg} {retained : List RetainedAlias}
    {observation : Observation} {sourceShrinking observedShrinking : RootInst → Prop}
    (frame : Frame m W tenv penv env s future)
    (source : ObservedSafe m W sourceShrinking observation s.store)
    (observed : ObservedSafe m { W with base := s.nextScope } observedShrinking
      (callObservation (m := m) observation W tenv env continuation retained s.store)
      s.store) :
    ∀ r T E,
      (callObservation (m := m) observation W tenv env continuation retained s.store).roots r T →
      callD W tenv env continuation args r E → ∃ mu, T = .slice mu E := by
  intro r T E rootObserved demanded
  rcases demanded with inherited | ⟨x, lv, si, mu, variableAt, scopeAt, rfl, variableType,
      _, _⟩
  · exact observed.holderTypes r T E rootObserved inherited
  · rcases rootObserved with inheritedObserved |
      ((⟨x', lv', si', _, _, variableAt', scopeAt', rootEq, typeEq⟩ |
        ⟨⟨x', lv', si', variableAt', scopeAt', rootEq, _, typeEq⟩, _⟩) |
        ⟨element, inheritedDemand, typeEq⟩)
    · have older := source.rootsOlder _ _ inheritedObserved
      exact False.elim ((Nat.not_le_of_gt older) (frame.inst_lt scopeAt).1)
    · cases rootEq
      rw [variableAt] at variableAt'
      cases variableAt'
      rw [variableType] at typeEq
      exact ⟨mu, typeEq⟩
    · cases rootEq
      rw [variableAt] at variableAt'
      cases variableAt'
      rw [variableType] at typeEq
      exact ⟨mu, typeEq⟩
    · exact False.elim (frame.not_outer scopeAt ⟨element, inheritedDemand⟩)

/-- Pilot calls observe the caller's active bindings. Their callee context
has no shrink authority, so owner protection and classification are vacuous. -/
private theorem callBody_pilot_observed {W : World} {tenv : TEnv} {penv : PEnv} {env : Env}
    {s : St} {observation : Observation} {active : List VarId} {args : List Arg}
    {ars : List (List RootRef)} {callee : Impl} {E : Eff}
    (frame : Frame m W tenv penv env s active)
    (source : ObservedSafe m W (fun _ => False) observation s.store) :
    ObservedSafe m
      ⟨W.G, (fun i root => Gam env W.P (ars[i]?.getD []) root),
        callOwnerP W callee env ars, E, s.nextScope,
        callD W tenv env active args, callA W penv env⟩
      (fun _ => False)
      (callObservation (m := m) observation W tenv env active [] s.store) s.store := by
  have observed := callObservation_safe (retained := []) frame (fun _ member => member)
    (source.base_mono frame.base_le)
    (fun _ _ _ _ _ _ _ _ hFalse => False.elim hFalse)
    (fun _ _ _ _ _ _ hFalse => False.elim hFalse)
  exact ⟨observed.typed, observed.rootsOlder, observed.valuesOlder,
    observed.rootsProtected, observed.valuesProtected,
    callObservation_callD_holderTypes frame source observed⟩

set_option maxHeartbeats 1600000 in
 private theorem step_expr_call_pilot {plans : Array (Array DemandPoint)} {path : List Nat}
    (hm : ModOk m) (ih : Specs m prof plans n) (profile : m.profile = .pilot)
    (variables : List VarId) (observation : Observation) (W : World)
    (tenv : TEnv) (penv : PEnv) (env : Env) (s : St) (c : ContextId)
    (args : List Arg) (origin : OriginId) (tn tn' : Nat) (ty : Ty)
    (rst rst' : RState) (rho : List RootRef)
    (active : ∀ x, x ∈ variables ↔ x ∈ tenv.visible)
    (source : ObservedSafe m W (fun _ => False) observation s.store)
    (permission : Perm m W) (frame : Frame m W tenv penv env s variables)
    (typing : tyExpr tenv (.call c args origin) tn = .ok (ty, tn'))
    (replay : rpExpr penv (.call c args origin) rst = .ok (rho, rst'))
    (effects : EffLe rst'.eff W.E) :
    Sat (evalExpr (n + 1) ⟨prof, m⟩ env (.call c args origin)) s (fun value s' =>
      Frame m W tenv penv env s' variables ∧ Footprint (insts env) (Dset W) s s' ∧
      PreservesRootTypes m W.G observation.roots s.store s'.store ∧
      PreservesValues m W.G observation.values s.store s'.store ∧
      ObservedSafe m W (fun _ => False) observation s'.store ∧
      RetainsAliases m W env s.store s'.store [] ∧ PilotStoreLe m s s' ∧
      HasTy m W.G s'.store value ty ∧ (∀ r, Targets value r → Gam env W.P rho r) ∧
      (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s'.store) ∧
      OwnerRooted env W.ownerP rho value ty ∧
      PreservesForbiddenOwnerRoots (m := m) (G := W.G) (env := env) (P := W.P) [] s s' ∧
      MutationFootprint env W.P W.base (effectMutationRoots m penv.impl rst'.eff) s s') := by
  simp only [rpExpr] at replay; inv at replay
  obtain ⟨ars, state1, argumentsReplay, contentsCheck, callReplay⟩ := replay
  have argumentsEffects := (PMono.rpCall _ _ _ _ _ _ callReplay).2.trans effects
  obtain ⟨ctx, callee, contextAt, implementationAt, argumentCheck, effectAt, resultReplay⟩ :=
    rpCall_ok _ _ _ _ _ _ callReplay
  have contents := checkContents_ok _ _ _ _ ctx contentsCheck contextAt
  rw [frame.mod_p] at contextAt implementationAt
  have contextAtT : tenv.mod.contexts[c]? = some ctx := by rw [frame.mod_t]; exact contextAt
  have implementationAtT : tenv.mod.impls[ctx.impl]? = some callee := by
    rw [frame.mod_t]; exact implementationAt
  simp only [tyExpr, contextAtT, implementationAtT] at typing; inv at typing
  obtain ⟨_, size, next, argumentTypes, _, _, resultType, _⟩ := typing
  obtain ⟨other, otherAt, contextChecked⟩ := hm.ctx c ctx contextAt
  rw [implementationAt] at otherAt
  cases otherAt
  have implementationChecked := hm.impl _ _ implementationAt
  let ec : EvaluationContext m plans path (.expression (.call c args origin)) .expression :=
    .pilot profile variables
  have suffixFrame : Frame m W tenv penv env s (callArgsFuture ec 0 args) :=
    frame.changeFuture (fun x visible _ => (active x).2 visible)
  have classified : m.profile = .shrink → ClassifiedParameters m W.P W.D observation s.store := by
    intro shrink
    rw [profile] at shrink
    cases shrink
  have protectedSlices : ShrinkProtected W.D W.A (ec.mayShrink W.ownerP observation) := by
    intro _ _ _ _ _ _ shrink
    exact False.elim shrink
  simp only [evalExpr]
  refine Sat.bind (args_spec ec observation ih.arg permission active trivial protectedSlices
    callee implementationChecked args callee.params.toList 0 s _ _ _ _ _ (by simp) (by omega)
    (fun _ member => member) suffixFrame source classified (by simpa using size)
    argumentTypes argumentsReplay argumentsEffects) ?_
  rintro vals s1 ⟨frame1, footprint1, roots1, values1, source1, _, pilot1, _, length, sampled, class1, _, argumentsMutation⟩
  obtain ⟨bodyRoots, range, bodyState, bodyReplay, _, _⟩ := contextChecked.body
  have bodyEffects : ContextEff m callee ctx bodyState.eff :=
    ⟨bodyRoots, range, bodyState, bodyReplay, rfl⟩
  have charged : EffLe (callEffects callee ctx ars state1.eff) W.E := by
    rw [effectAt] at effects
    exact effects
  have body := callBody_spec ih.call ec observation W tenv penv env s1 ctx callee bodyState.eff
    vals ars [] ty rho state1.eff contextAt implementationAt implementationChecked contextChecked bodyEffects
    active trivial protectedSlices source1 class1 permission frame1 size length argumentCheck contents sampled
    resultType resultReplay charged (by simp [ec, EvaluationContext.retained])
  have boundary := callBody_pilot_observed (args := args) (ars := ars) (callee := callee)
    (E := bodyState.eff)
    (by simpa [ec, callArgsFuture] using frame1) source1
  refine (body (by
    change ObservedSafe m _ (fun _ => False) _ _
    simpa only [ec, EvaluationContext.outputFuture, DemandNode.visibleAfter] using boundary)
    (by intro shrink; rw [profile] at shrink; cases shrink)
    (by intro _ _ _ _ _ _ shrink; exact False.elim shrink)).mono ?_
  intro value final post
  obtain ⟨frame2, footprint2, roots2, values2, safe2, retained2, pilot2, typed, targets, class2, ownerRooted, bodyMutation⟩ := post
  refine ⟨frame2, footprint1.trans footprint2, roots1.trans roots2, values1.trans values2,
    safe2, (by intro alias member; cases member), fun h => (pilot1 h).trans (pilot2 h), typed, targets, class2, ownerRooted, (by intro owner member; cases member), ?_⟩
  apply callMutationFootprints_compose (finalEffects := rst'.eff) frame1 argumentsMutation bodyMutation
    (PMono.rpCall _ _ _ _ _ _ callReplay).2
    (PMonoRebinds.rpCall _ _ _ _ _ _ callReplay)
  intro root denoted
  rw [effectAt]
  exact callMutationRoot frame1 hm implementationChecked contextChecked bodyEffects denoted

set_option maxHeartbeats 1600000 in
private theorem step_expr_call_shrink {plans : Array (Array DemandPoint)} {path : List Nat}
    {pc : PlanContext m plans} {c : ContextId} {args : List Arg} {origin : OriginId}
    (hm : ModOk m) (ih : Specs m prof plans n) (profile : m.profile = .shrink)
    (context : NodeContext pc path (.expression (.call c args origin)) .expression)
    (observation : Observation) (W : World) (tenv : TEnv) (penv : PEnv) (env : Env)
    (s : St) (tn tn' : Nat) (ty : Ty) (rst rst' : RState) (rho : List RootRef)
    (active : context.ActiveMatches tenv) (access : context.AccessMatches tenv penv)
    (protectedSlices : ShrinkProtected W.D W.A
      (fun root => PlanMayShrink pc W.ownerP root ∧ OwnerCap m observation root))
    (source : ObservedSafe m W
      (fun root => PlanMayShrink pc W.ownerP root ∧ OwnerCap m observation root) observation s.store)
    (classified : ClassifiedParameters m W.P W.D observation s.store)
    (permission : Perm m W) (frame : Frame m W tenv penv env s context.inputFuture)
    (typing : tyExpr tenv (.call c args origin) tn = .ok (ty, tn'))
    (replay : rpExpr penv (.call c args origin) rst = .ok (rho, rst'))
    (effects : EffLe rst'.eff W.E) :
    let ec : EvaluationContext m plans path (.expression (.call c args origin)) .expression :=
      .shrink profile context
    Sat (evalExpr (n + 1) ⟨prof, m⟩ env (.call c args origin)) s (fun value s' =>
      Frame m W tenv penv env s' ec.outputFuture ∧ Footprint (insts env) (Dset W) s s' ∧
      PreservesRootTypes m W.G observation.roots s.store s'.store ∧
      PreservesValues m W.G observation.values s.store s'.store ∧
      ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s'.store ∧
      RetainsAliases m W env s.store s'.store ec.retained ∧ PilotStoreLe m s s' ∧
      HasTy m W.G s'.store value ty ∧ (∀ r, Targets value r → Gam env W.P rho r) ∧
      (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s'.store) ∧
      OwnerRooted env W.ownerP rho value ty ∧
      PreservesForbiddenOwnerRoots (m := m) (G := W.G) (env := env) (P := W.P)
        ec.forbiddenOwners s s' ∧
      MutationFootprint env W.P W.base (effectMutationRoots m penv.impl rst'.eff) s s') := by
  let ec : EvaluationContext m plans path (.expression (.call c args origin)) .expression :=
    .shrink profile context
  have sourceReplay := replay
  simp only [rpExpr] at replay; inv at replay
  obtain ⟨ars, state1, argumentsReplay, contentsCheck, callReplay⟩ := replay
  have argumentsEffects := (PMono.rpCall _ _ _ _ _ _ callReplay).2.trans effects
  obtain ⟨ctx, callee, contextAt, implementationAt, argumentCheck, effectAt, resultReplay⟩ :=
    rpCall_ok _ _ _ _ _ _ callReplay
  have contents := checkContents_ok _ _ _ _ ctx contentsCheck contextAt
  rw [frame.mod_p] at contextAt implementationAt
  have contextAtT : tenv.mod.contexts[c]? = some ctx := by rw [frame.mod_t]; exact contextAt
  have implementationAtT : tenv.mod.impls[ctx.impl]? = some callee := by
    rw [frame.mod_t]; exact implementationAt
  simp only [tyExpr, contextAtT, implementationAtT] at typing; inv at typing
  obtain ⟨_, size, next, argumentTypes, _, _, resultType, _⟩ := typing
  obtain ⟨other, otherAt, contextChecked⟩ := hm.ctx c ctx contextAt
  rw [implementationAt] at otherAt
  cases otherAt
  have implementationChecked := hm.impl _ _ implementationAt
  have declarations := ArgumentRootDeclarations.ofCallArgs frame hm
    (context.callerContext_checked hm access) size argumentTypes argumentsReplay
  have suffixFrame : Frame m W tenv penv env s (callArgsFuture ec 0 args) := by
    simpa [ec, callArgsFuture, NodeContext.inputFuture, NodeContext.outputFuture,
      DemandNode.variables, Expr.variables] using frame
  simp only [evalExpr]
  refine Sat.bind (args_spec ec observation ih.arg permission active access protectedSlices
    callee implementationChecked args callee.params.toList 0 s _ _ _ _ _ (by simp) (by omega)
    (fun _ member => member) suffixFrame source (fun _ => classified) (by simpa using size)
    argumentTypes argumentsReplay argumentsEffects) ?_
  rintro vals s1 ⟨frame1, footprint1, roots1, values1, source1, retained1, pilot1, _, length,
    sampled, class1, forbidden1, argumentsMutation⟩
  obtain ⟨bodyRoots, range, bodyState, bodyReplay, _, _⟩ := contextChecked.body
  have bodyEffects : ContextEff m callee ctx bodyState.eff :=
    ⟨bodyRoots, range, bodyState, bodyReplay, rfl⟩
  let boundary := callObservation (m := m) observation W tenv env context.outputFuture ec.retained s1.store
  let root := ec.calleeContext callee contextAt implementationAt
  let shrinking := root.mayShrink (callOwnerP W callee env ars) boundary
  have recorded : ∀ rootInst, shrinking rootInst →
      MayShrinkEff (callOwnerP W callee env ars) bodyState.eff rootInst ∧ OwnerCap m boundary rootInst :=
    fun _ shrink => EvaluationContext.callBody_effect root
      (ec.calleeContext_owner callee contextAt implementationAt) contextAt implementationAt hm bodyEffects shrink
  have coverage := NodeContext.callBody_coverage (retained := ec.retained) context frame1 access contextAt implementationAt
    contextChecked bodyEffects source1.rootsOlder argumentsReplay
  have cover : ∀ rootInst, shrinking rootInst → ∃ owner,
      owner ∈ context.callMutationContext.expected.shrinkOwners ∧ owner.invalidates = true ∧
      Gam env W.ownerP owner.roots rootInst :=
    fun rootInst shrink => coverage rootInst (recorded rootInst shrink).1 (recorded rootInst shrink).2
  have caps : ∀ rootInst, shrinking rootInst → OwnerCap m boundary rootInst :=
    fun rootInst shrink => (recorded rootInst shrink).2
  have futureSubset : ∀ x, x ∈ context.outputFuture → x ∈ callArgsFuture ec args.length [] := by
    simp only [ec, callArgsFuture, List.flatMap_nil, List.append_nil, List.mem_append]
    exact fun _ member => Or.inr member
  have initialized : ∀ global, shrinking (.global global) → global < W.G := by
    intro global shrink
    obtain ⟨owner, ownerMember, _, ownerIn⟩ := cover _ shrink
    exact NodeContext.callGlobal_initialized context hm frame1 access permission sourceReplay effects
      ownerMember ownerIn (caps _ shrink)
  have boundaryObserved := context.callObservation_observed frame1 active access futureSubset source1
    protectedSlices caps initialized (context.callMutation_retains_parent) cover
  have protectedBoundary := context.callD_shrinkProtected frame1 active access protectedSlices caps cover
  have boundaryClass := frame1.callObservation_classified (continuation := context.outputFuture)
    (args := args) (retained := ec.retained) declarations (class1 profile)
  have charged : EffLe (callEffects callee ctx ars state1.eff) W.E := by
    rw [effectAt] at effects
    exact effects
  have body := callBody_spec ih.call ec observation W tenv penv env s1 ctx callee bodyState.eff
    vals ars ec.retained ty rho state1.eff contextAt implementationAt implementationChecked contextChecked bodyEffects
    active access protectedSlices source1 class1 permission frame1 size length argumentCheck contents sampled
    resultType resultReplay charged (fun _ member => member)
  refine (body (by exact ⟨boundaryObserved.typed, boundaryObserved.rootsOlder,
    boundaryObserved.valuesOlder, boundaryObserved.rootsProtected, boundaryObserved.valuesProtected,
    callObservation_callD_holderTypes frame1 source1 boundaryObserved⟩)
    (fun _ => boundaryClass) protectedBoundary).mono ?_
  intro value final post
  obtain ⟨frame2, footprint2, roots2, values2, safe2, retained2, pilot2, typed, targets,
    class2, ownerRooted, bodyMutation⟩ := post
  refine ⟨frame2, footprint1.trans footprint2, roots1.trans roots2, values1.trans values2,
    safe2, retained1.trans retained2, fun h => (pilot1 h).trans (pilot2 h), typed, targets,
    class2, ownerRooted, ?_, ?_⟩
  · exact forbidden1.trans (NodeContext.callBody_forbidden context hm frame1 access contextAt
      implementationAt implementationChecked contextChecked bodyEffects permission charged argumentsReplay bodyMutation)
  · apply callMutationFootprints_compose (finalEffects := rst'.eff) frame1 argumentsMutation bodyMutation
      (PMono.rpCall _ _ _ _ _ _ callReplay).2 (PMonoRebinds.rpCall _ _ _ _ _ _ callReplay)
    intro rootInst denoted
    rw [effectAt]
    exact callMutationRoot frame1 hm implementationChecked contextChecked bodyEffects denoted

set_option maxHeartbeats 1600000 in
theorem step_expr_call {plans : Array (Array DemandPoint)} (hm : ModOk m)
    (ih : Specs m prof plans n) (path : List Nat) (c : ContextId) (args : List Arg) (origin : OriginId)
    (ec : EvaluationContext m plans path (.expression (.call c args origin)) .expression)
    (observation : Observation) (W : World) (tenv : TEnv) (penv : PEnv) (env : Env) (s : St)
    (tn tn' : Nat) (ty : Ty) (rst rst' : RState) (rho : List RootRef)
    (active : ec.ActiveMatches tenv) (access : ec.AccessMatches tenv penv)
    (protectedSlices : ShrinkProtected W.D W.A (ec.mayShrink W.ownerP observation))
    (source : ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s.store)
    (classified : m.profile = .shrink → ClassifiedParameters m W.P W.D observation s.store)
    (permission : Perm m W) (frame : Frame m W tenv penv env s ec.inputFuture)
    (typing : tyExpr tenv (.call c args origin) tn = .ok (ty, tn'))
    (replay : rpExpr penv (.call c args origin) rst = .ok (rho, rst'))
    (effects : EffLe rst'.eff W.E) :
    Sat (evalExpr (n + 1) ⟨prof, m⟩ env (.call c args origin)) s (fun value s' =>
      Frame m W tenv penv env s' ec.outputFuture ∧ Footprint (insts env) (Dset W) s s' ∧
      PreservesRootTypes m W.G observation.roots s.store s'.store ∧
      PreservesValues m W.G observation.values s.store s'.store ∧
      ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s'.store ∧
      RetainsAliases m W env s.store s'.store ec.retained ∧ PilotStoreLe m s s' ∧
      HasTy m W.G s'.store value ty ∧ (∀ r, Targets value r → Gam env W.P rho r) ∧
      (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s'.store) ∧
      OwnerRooted env W.ownerP rho value ty ∧
      PreservesForbiddenOwnerRoots (m := m) (G := W.G) (env := env) (P := W.P)
        ec.forbiddenOwners s s' ∧
      MutationFootprint env W.P W.base (effectMutationRoots m penv.impl rst'.eff) s s') := by
  cases ec with
  | pilot profile variables =>
    have activeFrame : Frame m W tenv penv env s variables :=
      frame.changeFuture (fun _ _ member => List.mem_append_right _ member)
    exact step_expr_call_pilot (path := path) hm ih profile variables observation W tenv penv env s c args origin
      tn tn' ty rst rst' rho active source permission activeFrame typing replay effects
  | shrink profile context =>
    exact step_expr_call_shrink hm ih profile context observation W tenv penv env s tn tn' ty
      rst rst' rho active access protectedSlices source (classified profile) permission frame typing replay effects

end Goose.Core.Sound
