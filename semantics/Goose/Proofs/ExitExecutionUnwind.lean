import Goose.Proofs.ExitExecution

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct
open Goose.Proofs.Exit

private theorem withScope_escape_before_release (environment : RuntimeActivation)
    (scope scopeInst : Nat) (action : EvalM α) (initial final : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier)
    (escaped : withScope environment scope scopeInst action initial = .escape address carriers final) :
    ∃ before, action initial = .escape address carriers before ∧
      final = releaseScopeState environment scope scopeInst before := by
  cases evaluated : action initial with
  | ok value before | stop reason before | jump target kind before =>
    simp only [withScope, evaluated, releaseScope, EvalM.get, EvalM.set, bind] at escaped
    cases escaped
  | escape target payload before =>
    simp only [withScope, evaluated, releaseScope, EvalM.get, EvalM.set, bind] at escaped
    cases escaped
    exact ⟨before, rfl, rfl⟩

theorem execBlock_escape_unwinds_scope (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (channels : List Channel)
    (scope : Nat) (statements : List Stmt) (tail : Option Expr)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : execBlock (fuel + 1) config environment pre channels (.mk scope statements tail) initial =
      .escape address carriers final) :
    let scopeInst := initial.nextScope
    let scopeEnvironment := { environment with scopes := (scope, scopeInst) :: environment.scopes }
    let prepared : ExecutionState := { initial with nextScope := initial.nextScope + 1 }
    let body : EvalM Flow := do
      bindAll environment.act scopeInst pre
      let flow ← execStmts fuel config scopeEnvironment statements
      match flow, tail with
      | .normal _, some expression =>
          if channels.isEmpty then pure (.normal (← evalValue fuel config scopeEnvironment expression))
          else pure (.normal (← carrierValue (← singleCarrier (← evalProduce fuel config scopeEnvironment channels expression))))
      | flow, _ => pure flow
    ∃ before, body prepared = .escape address carriers before ∧
      final = releaseScopeState environment scope scopeInst before ∧
      final.construction = before.construction ∧
      ∀ entry : Goose.Core.RootInst × Value,
        entry ∈ final.objects ↔ entry ∈ before.objects ∧
          (runtimeScopeRoots environment scope scopeInst).contains entry.1 = false := by
  let scopeInst := initial.nextScope
  let scopeEnvironment := { environment with scopes := (scope, scopeInst) :: environment.scopes }
  let prepared : ExecutionState := { initial with nextScope := initial.nextScope + 1 }
  let body : EvalM Flow := do
    bindAll environment.act scopeInst pre
    let flow ← execStmts fuel config scopeEnvironment statements
    match flow, tail with
    | .normal _, some expression =>
        if channels.isEmpty then pure (.normal (← evalValue fuel config scopeEnvironment expression))
        else pure (.normal (← carrierValue (← singleCarrier (← evalProduce fuel config scopeEnvironment channels expression))))
    | flow, _ => pure flow
  have actual : withScope environment scope scopeInst body prepared = .escape address carriers final := by
    simp only [scopeInst, scopeEnvironment, prepared, body, bind, pure]
    simp only [execBlock, freshScope, EvalM.get, EvalM.set, bind, pure] at escaped
    refine Eq.trans ?_ escaped
    apply congrArg (fun action : EvalM Flow =>
      withScope environment scope initial.nextScope action { initial with nextScope := initial.nextScope + 1 })
    funext state
    cases bound : bindAll environment.act initial.nextScope pre state <;> simp only
    case ok value after =>
      cases evaluated : execStmts fuel config
        { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
        statements after <;> simp only
      case ok flow middle =>
        cases flow <;> cases tail <;> rfl

  obtain ⟨before, bodyEscape, released⟩ :=
    withScope_escape_before_release environment scope scopeInst body prepared final address carriers actual
  refine ⟨before, bodyEscape, released, ?_, ?_⟩
  · rw [released]
    rfl
  · intro entry
    rw [released]
    exact runtime_release_scope_members environment scope scopeInst before entry

theorem execResultScope_escape_unwinds_scope (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (channels : List Channel)
    (scope : Nat) (statements : List Stmt) (tail : Option Expr)
    (statementsAction : RuntimeActivation → List Stmt → EvalM Flow)
    (tailAction : RuntimeActivation → Expr → EvalM (List Carrier))
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : execResultScope environment pre channels (.mk scope statements tail)
      statementsAction tailAction initial = .escape address carriers final) :
    let scopeInst := initial.nextScope
    let scopeEnvironment := { environment with scopes := (scope, scopeInst) :: environment.scopes }
    let prepared : ExecutionState := { initial with
      nextScope := initial.nextScope + 1
      activations := initial.activations.map (fun (current : RuntimeActivation) => if current.act == environment.act then
        { current with scopes := scopeEnvironment.scopes } else current) }
    let body : EvalM (Flow × List Carrier) := do
      bindAll environment.act scopeInst pre
      let flow ← statementsAction scopeEnvironment statements
      match flow, tail with
      | .normal _, some expression => pure (.normal .unit, ← tailAction scopeEnvironment expression)
      | .normal _, none =>
          if channels.isEmpty then pure (flow, [])
          else match channels with
            | [.register .unit] => pure (flow, [.register .unit])
            | _ => fault .arity
      | flow, _ => pure (flow, [])
    ∃ before, body prepared = .escape address carriers before ∧
      final = releaseScopeState environment scope scopeInst before ∧
      final.construction = before.construction ∧
      ∀ entry : Goose.Core.RootInst × Value,
        entry ∈ final.objects ↔ entry ∈ before.objects ∧
          (runtimeScopeRoots environment scope scopeInst).contains entry.1 = false := by
  let scopeInst := initial.nextScope
  let scopeEnvironment := { environment with scopes := (scope, scopeInst) :: environment.scopes }
  let prepared : ExecutionState := { initial with
    nextScope := initial.nextScope + 1
    activations := initial.activations.map (fun (current : RuntimeActivation) => if current.act == environment.act then
      { current with scopes := scopeEnvironment.scopes } else current) }
  let body : EvalM (Flow × List Carrier) := do
    bindAll environment.act scopeInst pre
    let flow ← statementsAction scopeEnvironment statements
    match flow, tail with
    | .normal _, some expression => pure (.normal .unit, ← tailAction scopeEnvironment expression)
    | .normal _, none =>
        if channels.isEmpty then pure (flow, [])
        else match channels with
          | [.register .unit] => pure (flow, [.register .unit])
          | _ => fault .arity
    | flow, _ => pure (flow, [])
  have actual : withScope environment scope scopeInst body prepared = .escape address carriers final := by
    simp only [scopeInst, scopeEnvironment, prepared, body, bind, pure]
    simp only [execResultScope, freshScope, EvalM.get, EvalM.set, bind, pure] at escaped
    refine Eq.trans ?_ escaped
    apply congrArg (fun action : EvalM (Flow × List Carrier) =>
      withScope environment scope initial.nextScope action
        { initial with
          nextScope := initial.nextScope + 1
          activations := initial.activations.map (fun (current : RuntimeActivation) => if current.act == environment.act then
            { current with scopes := (scope, initial.nextScope) :: environment.scopes } else current) })
    funext state
    cases bindAll environment.act initial.nextScope pre state <;> simp only
    case ok value after =>
      cases statementsAction
        { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
        statements after <;> simp only
      case ok flow middle =>
        cases flow <;> cases tail <;> rfl
  obtain ⟨before, bodyEscape, released⟩ :=
    withScope_escape_before_release environment scope scopeInst body prepared final address carriers actual
  refine ⟨before, bodyEscape, released, ?_, ?_⟩
  · rw [released]
    rfl
  · intro entry
    rw [released]
    exact runtime_release_scope_members environment scope scopeInst before entry

private abbrev NeverEscapes (action : EvalM α) : Prop :=
  ∀ (state : ExecutionState) (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState),
    action state ≠ .escape address carriers final

private theorem neverEscapes_pure (value : α) : NeverEscapes (pure value) := by
  intro state address carriers final impossible
  cases impossible

private theorem neverEscapes_get : NeverEscapes EvalM.get := by
  intro state address carriers final impossible
  cases impossible

private theorem neverEscapes_set (next : ExecutionState) : NeverEscapes (EvalM.set next) := by
  intro state address carriers final impossible
  cases impossible

private theorem neverEscapes_fault (kind : Goose.Core.FaultKind) : NeverEscapes (fault (α := α) kind) := by
  intro state address carriers final impossible
  cases impossible

private theorem neverEscapes_lift (origin : Goose.Core.OriginId) (action : ConstructionM α) :
    NeverEscapes (liftConstruction origin action) := by
  intro state address carriers final impossible
  cases result : action state.construction <;>
    simp only [liftConstruction, result] at impossible <;> cases impossible

private theorem neverEscapes_bind (action : EvalM α) (next : α → EvalM β)
    (first : NeverEscapes action) (remaining : ∀ value, NeverEscapes (next value)) :
    NeverEscapes (action >>= next) := by
  intro state address carriers final impossible
  cases evaluated : action state with
  | ok value after =>
    exact remaining value after address carriers final (by simpa only [bind, evaluated] using impossible)
  | stop reason after | jump target kind after =>
    simp only [bind, evaluated] at impossible
    cases impossible
  | escape target payload after => exact first state target payload after evaluated

private theorem neverEscapes_forIn (items : List α) (initial : β)
    (action : α → β → EvalM (ForInStep β))
    (body : ∀ item current, NeverEscapes (action item current)) :
    NeverEscapes (forIn items initial action) := by
  induction items generalizing initial with
  | nil => exact neverEscapes_pure _
  | cons item rest ih =>
    rw [List.forIn_cons]
    apply neverEscapes_bind
    · exact body item initial
    · intro step
      cases step with
      | done value => exact neverEscapes_pure _
      | yield value => exact ih value

private theorem neverEscapes_getDestination (id : Goose.Core.DestinationId) :
    NeverEscapes (getDestination id) := by
  unfold getDestination
  apply neverEscapes_bind
  · exact neverEscapes_get
  · intro state
    split
    · exact neverEscapes_pure _
    · exact neverEscapes_fault _

private theorem neverEscapes_receivingDestination (id : Goose.Core.DestinationId) :
    NeverEscapes (receivingDestination id) := neverEscapes_lift _ _

private theorem neverEscapes_receivingLayout (layout : LayoutEnv) (ty : Ty) :
    NeverEscapes (receivingLayout layout ty) := by
  cases ty <;> simp only [receivingLayout]
  all_goals first | exact neverEscapes_pure _ | exact neverEscapes_fault _ | skip
  split
  · exact neverEscapes_pure _
  · exact neverEscapes_fault _

local elab "landing_escape_intro" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.isForall do throwError "expected landing callback"
  Lean.Elab.Tactic.evalTactic (← `(tactic| intro value))

local syntax "landing_never_escapes" : tactic
macro_rules
  | `(tactic| landing_never_escapes) => `(tactic|
    repeat' first
      | with_reducible exact neverEscapes_pure _
      | with_reducible exact neverEscapes_get
      | with_reducible exact neverEscapes_set _
      | with_reducible exact neverEscapes_fault _
      | with_reducible exact neverEscapes_lift _ _
      | with_reducible exact neverEscapes_getDestination _
      | with_reducible exact neverEscapes_receivingDestination _
      | with_reducible exact neverEscapes_receivingLayout _ _
      | with_reducible apply neverEscapes_bind
      | with_reducible apply neverEscapes_forIn
      | split
      | landing_escape_intro)

private theorem neverEscapes_setObjectOrdinal (root : Goose.Core.RootInst) (ordinal : Goose.Core.StorageId) :
    NeverEscapes (setObjectOrdinal root ordinal) := by
  unfold setObjectOrdinal
  landing_never_escapes

private theorem neverEscapes_reserveRootObject (root : Goose.Core.RootInst) :
    NeverEscapes (reserveRootObject root) := by
  unfold reserveRootObject
  repeat' first
    | with_reducible exact neverEscapes_setObjectOrdinal _ _
    | with_reducible exact neverEscapes_pure _
    | with_reducible exact neverEscapes_get
    | with_reducible exact neverEscapes_lift _ _
    | with_reducible apply neverEscapes_bind
    | split
    | landing_escape_intro

private theorem neverEscapes_bindRoot (root : Goose.Core.RootInst) (value : Value) :
    NeverEscapes (bindRoot root value) := by
  unfold bindRoot bindStaticRoot
  repeat' first
    | with_reducible exact neverEscapes_setObjectOrdinal _ _
    | with_reducible exact neverEscapes_reserveRootObject _
    | with_reducible exact neverEscapes_pure _
    | with_reducible exact neverEscapes_get
    | with_reducible exact neverEscapes_set _
    | with_reducible apply neverEscapes_bind
    | split
    | landing_escape_intro

private theorem neverEscapes_bindAll (act scopeInst : Nat) (values : List (Goose.Core.VarId × Value)) :
    NeverEscapes (bindAll act scopeInst values) := by
  unfold bindAll
  apply neverEscapes_bind
  · apply neverEscapes_forIn
    intro entry ignored
    rcases entry with ⟨localVar, value⟩
    apply neverEscapes_bind
    · exact neverEscapes_bindRoot _ _
    · intro ignored; exact neverEscapes_pure _
  · intro ignored; exact neverEscapes_pure _

private theorem neverEscapes_singleCarrier (values : List Carrier) :
    NeverEscapes (singleCarrier values) := by
  unfold singleCarrier
  landing_never_escapes

private theorem neverEscapes_carrierValue (carrier : Carrier) :
    NeverEscapes (carrierValue carrier) := by
  cases carrier <;> simp only [carrierValue, storedDestination]
  all_goals landing_never_escapes

private theorem bind_escape_of_right_never (action : EvalM α) (next : α → EvalM β)
    (remaining : ∀ value, NeverEscapes (next value))
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : (action >>= next) initial = .escape address carriers final) :
    action initial = .escape address carriers final := by
  cases evaluated : action initial with
  | ok value middle =>
      simp only [bind, evaluated] at escaped
      exact False.elim (remaining value middle address carriers final escaped)
  | stop reason after | jump target kind after =>
      simp only [bind, evaluated] at escaped
      cases escaped
  | escape target payload after =>
      simp only [bind, evaluated] at escaped
      cases escaped
      rfl

theorem execBlock_escape_call (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (channels : List Channel)
    (scope : Nat) (statements : List Stmt) (tail : Option Expr)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : execBlock (fuel + 1) config environment pre channels (.mk scope statements tail) initial =
      .escape address carriers final) :
    let scopeInst := initial.nextScope
    let scopeEnvironment := { environment with scopes := (scope, scopeInst) :: environment.scopes }
    let prepared : ExecutionState := { initial with nextScope := initial.nextScope + 1 }
    ∃ bound before,
      bindAll environment.act scopeInst pre prepared = .ok () bound ∧
      (execStmts fuel config scopeEnvironment statements bound = .escape address carriers before ∨
        ∃ value middle expression,
          execStmts fuel config scopeEnvironment statements bound = .ok (.normal value) middle ∧
          tail = some expression ∧
          (channels.isEmpty = true ∧
              evalValue fuel config scopeEnvironment expression middle = .escape address carriers before ∨
           channels.isEmpty = false ∧
              evalProduce fuel config scopeEnvironment channels expression middle = .escape address carriers before)) ∧
      final = releaseScopeState environment scope scopeInst before := by
  obtain ⟨before, bodyEscape, released, construction, objects⟩ :=
    execBlock_escape_unwinds_scope fuel config environment pre channels scope statements tail
      initial final address carriers escaped
  let scopeEnvironment := { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
  let prepared : ExecutionState := { initial with nextScope := initial.nextScope + 1 }
  cases binding : bindAll environment.act initial.nextScope pre prepared with
  | stop reason after | jump target kind after =>
      simp only [prepared, bind, binding] at bodyEscape
      cases bodyEscape
  | escape target values after =>
      exact False.elim (neverEscapes_bindAll environment.act initial.nextScope pre
        prepared target values after binding)
  | ok ignored bound =>
      cases ignored
      refine ⟨bound, before, binding, ?_, released⟩
      dsimp only [prepared] at binding
      simp only [bind, binding] at bodyEscape
      change (do
        let flow ← execStmts fuel config scopeEnvironment statements
        match flow, tail with
        | .normal _, some expression =>
            if channels.isEmpty then pure (Flow.normal (← evalValue fuel config scopeEnvironment expression))
            else pure (Flow.normal (← carrierValue (← singleCarrier (← evalProduce fuel config scopeEnvironment channels expression))))
        | flow, _ => pure flow) bound = .escape address carriers before at bodyEscape
      cases evaluated : execStmts fuel config scopeEnvironment statements bound with
      | stop reason after | jump target kind after =>
          simp only [bind, evaluated] at bodyEscape
          cases bodyEscape
      | escape target values after =>
          simp only [bind, evaluated] at bodyEscape
          cases bodyEscape
          exact Or.inl rfl
      | ok flow middle =>
          simp only [bind, evaluated] at bodyEscape
          cases flow with
          | breaking value | continuing => cases bodyEscape
          | normal value =>
              cases tail with
              | none => cases bodyEscape
              | some expression =>
                  refine Or.inr ⟨value, middle, expression, rfl, rfl, ?_⟩
                  cases empty : channels.isEmpty with
                  | true =>
                      simp only [empty] at bodyEscape
                      exact Or.inl ⟨rfl, bind_escape_of_right_never _ _
                        (fun value => neverEscapes_pure (Flow.normal value))
                        middle before address carriers bodyEscape⟩
                  | false =>
                      simp only [empty] at bodyEscape
                      refine Or.inr ⟨rfl, bind_escape_of_right_never _ _ ?_
                        middle before address carriers bodyEscape⟩
                      intro values
                      apply neverEscapes_bind
                      · exact neverEscapes_singleCarrier values
                      · intro carrier
                        apply neverEscapes_bind
                        · exact neverEscapes_carrierValue carrier
                        · intro value; exact neverEscapes_pure _

theorem execResultScope_escape_call (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (channels : List Channel)
    (scope : Nat) (statements : List Stmt) (tail : Option Expr)
    (statementsAction : RuntimeActivation → List Stmt → EvalM Flow)
    (tailAction : RuntimeActivation → Expr → EvalM (List Carrier))
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : execResultScope environment pre channels (.mk scope statements tail)
      statementsAction tailAction initial = .escape address carriers final) :
    let scopeInst := initial.nextScope
    let scopeEnvironment := { environment with scopes := (scope, scopeInst) :: environment.scopes }
    let prepared : ExecutionState := { initial with
      nextScope := initial.nextScope + 1
      activations := initial.activations.map (fun (current : RuntimeActivation) => if current.act == environment.act then
        { current with scopes := scopeEnvironment.scopes } else current) }
    ∃ bound before,
      bindAll environment.act scopeInst pre prepared = .ok () bound ∧
      (statementsAction scopeEnvironment statements bound = .escape address carriers before ∨
        ∃ value middle expression,
          statementsAction scopeEnvironment statements bound = .ok (.normal value) middle ∧
          tail = some expression ∧
          tailAction scopeEnvironment expression middle = .escape address carriers before) ∧
      final = releaseScopeState environment scope scopeInst before := by
  obtain ⟨before, bodyEscape, released, construction, objects⟩ :=
    execResultScope_escape_unwinds_scope environment pre channels scope statements tail statementsAction tailAction
      initial final address carriers escaped
  let scopeEnvironment := { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
  let prepared : ExecutionState := { initial with
    nextScope := initial.nextScope + 1
    activations := initial.activations.map (fun (current : RuntimeActivation) => if current.act == environment.act then
      { current with scopes := scopeEnvironment.scopes } else current) }
  cases binding : bindAll environment.act initial.nextScope pre prepared with
  | stop reason after | jump target kind after =>
      simp only [prepared, scopeEnvironment, bind, binding] at bodyEscape
      cases bodyEscape
  | escape target values after =>
      exact False.elim (neverEscapes_bindAll environment.act initial.nextScope pre
        prepared target values after binding)
  | ok ignored bound =>
      cases ignored
      refine ⟨bound, before, binding, ?_, released⟩
      dsimp only [prepared, scopeEnvironment] at binding
      simp only [bind, binding] at bodyEscape
      change (do
        let flow ← statementsAction scopeEnvironment statements
        match flow, tail with
        | .normal _, some expression => pure (Flow.normal .unit, ← tailAction scopeEnvironment expression)
        | .normal _, none =>
            if channels.isEmpty then pure (flow, [])
            else match channels with
              | [.register .unit] => pure (flow, [.register .unit])
              | _ => fault .arity
        | flow, _ => pure (flow, [])) bound = .escape address carriers before at bodyEscape
      cases evaluated : statementsAction scopeEnvironment statements bound with
      | stop reason after | jump target kind after =>
          simp only [bind, evaluated] at bodyEscape
          cases bodyEscape
      | escape target values after =>
          simp only [bind, evaluated] at bodyEscape
          cases bodyEscape
          exact Or.inl rfl
      | ok flow middle =>
          simp only [bind, evaluated] at bodyEscape
          cases flow with
          | breaking value | continuing => cases bodyEscape
          | normal value =>
              cases tail with
              | none =>
                  have never : NeverEscapes (if channels.isEmpty then pure (Flow.normal value, [])
                      else match channels with
                        | [.register .unit] => pure (Flow.normal value, [Carrier.register .unit])
                        | _ => fault .arity) := by landing_never_escapes
                  exact False.elim (never middle address carriers before bodyEscape)
              | some expression =>
                  exact Or.inr ⟨value, middle, expression, rfl, rfl,
                    bind_escape_of_right_never _ _ (fun values => neverEscapes_pure (Flow.normal .unit, values))
                      middle before address carriers bodyEscape⟩

private theorem neverEscapes_landCarriersInto (origin : Goose.Core.OriginId)
    (channels : List Channel) (carriers : List Carrier) :
    NeverEscapes (landCarriersInto origin channels carriers) := by
  unfold landCarriersInto
  landing_never_escapes

private theorem neverEscapes_finishChannel (layout : LayoutEnv) (origin : Goose.Core.OriginId)
    (carrier : Carrier) (ty : Ty) : NeverEscapes (finishChannel layout origin carrier ty) := by
  cases carrier <;> simp only [finishChannel]
  all_goals landing_never_escapes

private theorem neverEscapes_finishChannels (layout : LayoutEnv) (channels : List Channel)
    (types : List Ty) (carriers : List Carrier) (origin : Goose.Core.OriginId) :
    NeverEscapes (finishChannels layout channels types carriers origin) := by
  unfold finishChannels
  apply neverEscapes_bind
  · exact neverEscapes_landCarriersInto _ _ _
  · intro ignored
    repeat' first
      | with_reducible exact neverEscapes_pure _
      | with_reducible exact neverEscapes_fault _
      | with_reducible exact neverEscapes_finishChannel _ _ _ _
      | with_reducible apply neverEscapes_bind
      | with_reducible apply neverEscapes_forIn
      | split
      | landing_escape_intro

theorem finishChannels_no_escape (layout : LayoutEnv) (channels : List Channel)
    (types : List Ty) (carriers : List Carrier) (origin : Goose.Core.OriginId)
    (initial final : ExecutionState) (address : ExitAddress) (payload : List Carrier) :
    finishChannels layout channels types carriers origin initial ≠ .escape address payload final :=
  neverEscapes_finishChannels layout channels types carriers origin initial address payload final


private theorem finishActivation_escape_origin (layout : LayoutEnv) (activation : RuntimeActivation)
    (types : List Ty) (origin : Goose.Core.OriginId) (action : EvalM (List Carrier))
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : finishActivation layout activation types origin action initial = .escape address carriers final) :
    ∃ before, action initial = .escape address carriers before ∧
      address.activation ≠ activation.act ∧
      final = { before with activations := before.activations.filter (fun current => current.act != activation.act) } := by
  cases evaluated : action initial with
  | stop reason before | jump target kind before =>
    simp only [finishActivation, evaluated] at escaped
    cases escaped
  | ok payload before =>
    cases landed : finishChannels layout activation.channels types payload origin
        { before with activations := before.activations.filter (fun current => current.act != activation.act) } with
    | escape target returned after =>
      exact False.elim (neverEscapes_finishChannels _ _ _ _ _ _ _ _ _ landed)
    | ok value after =>
      cases value
      simp only [finishActivation, evaluated, landed] at escaped
      cases escaped
    | stop reason after | jump target kind after =>
      simp only [finishActivation, evaluated, landed] at escaped
      cases escaped
  | escape target payload before =>
    by_cases caught : target.activation = activation.act
    · cases landed : finishChannels layout activation.channels types payload origin
          { before with activations := before.activations.filter (fun current => current.act != activation.act) } with
      | escape target returned after =>
        exact False.elim (neverEscapes_finishChannels _ _ _ _ _ _ _ _ _ landed)
      | ok value after =>
        cases value
        simp only [finishActivation, evaluated, caught, beq_self_eq_true, ↓reduceIte, landed] at escaped
        cases escaped
      | stop reason after | jump target kind after =>
        simp only [finishActivation, evaluated, caught, beq_self_eq_true, ↓reduceIte, landed] at escaped
        cases escaped
    · simp only [finishActivation, evaluated, caught, beq_iff_eq, ↓reduceIte] at escaped
      cases escaped
      exact ⟨before, rfl, caught, rfl⟩

theorem enterActivation_escape_origin (fuel : Nat) (config : EvalConfig)
    (activation : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
    (body : Block) (origin : Goose.Core.OriginId)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : enterActivation (fuel + 1) config activation pre body origin initial =
      .escape address carriers final) :
    ∃ implementation before,
      config.module.impls[activation.implementation]? = some implementation ∧
      execActivationBody fuel config activation pre body initial = .escape address carriers before ∧
      address.activation ≠ activation.act ∧
      final = { before with activations := before.activations.filter (fun current => current.act != activation.act) } := by
  cases present : config.module.impls[activation.implementation]? with
  | none =>
    simp only [enterActivation, present, fault, EvalM.stop] at escaped
    cases escaped
  | some implementation =>
    have actual : finishActivation config.layout activation (implementation.results.toList.map (·.ty)) origin
        (execActivationBody fuel config activation pre body) initial = .escape address carriers final := by
      simpa only [enterActivation, present] using escaped
    obtain ⟨before, bodyEscape, different, released⟩ :=
      finishActivation_escape_origin config.layout activation (implementation.results.toList.map (·.ty)) origin
        (execActivationBody fuel config activation pre body) initial final address carriers actual
    exact ⟨implementation, before, rfl, bodyEscape, different, released⟩

theorem execActivationBody_escape_origin (fuel : Nat) (config : EvalConfig)
    (activation : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (body : Block)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : execActivationBody (fuel + 1) config activation pre body initial =
      .escape address carriers final) :
    execResultScope activation pre activation.channels body
      (fun environment statements => execStmts fuel config environment statements)
      (fun environment expression => withCompletionChannels activation.channels (expressionOrigin expression)
        (fun channels => evalProduce fuel config environment channels expression)) initial =
      .escape address carriers final := by
  simp only [execActivationBody] at escaped
  cases result : execResultScope activation pre activation.channels body
      (fun environment statements => execStmts fuel config environment statements)
      (fun environment expression => withCompletionChannels activation.channels (expressionOrigin expression)
        (fun channels => evalProduce fuel config environment channels expression)) initial with
  | stop reason after | jump target kind after =>
    simp only [bind, result] at escaped
    cases escaped
  | escape target payload after =>
    simp only [bind, result] at escaped
    cases escaped
    rfl
  | ok pair after =>
    rcases pair with ⟨flow, returned⟩
    cases flow <;> simp only [bind, result, pure, fault, EvalM.stop] at escaped <;> cases escaped

private theorem neverEscapes_targetActivation (config : EvalConfig) (target : Nat) :
    NeverEscapes (targetActivation config target) := by
  unfold targetActivation
  landing_never_escapes

private theorem finishBorrowedExitChannels_not_ok (origin : Goose.Core.OriginId)
    (borrowed : List BorrowedWaitingExitReservation) (tokens : List Nat)
    (cancel : Bool) (carriers : List Carrier) (result : ExecutionState → ExecutionStep (List Carrier))
    (never : ∀ state values final, result state ≠ .ok values final)
    (initial final : ExecutionState) (values : List Carrier) :
    finishBorrowedExitChannels origin borrowed tokens cancel carriers result initial ≠ .ok values final := by
  intro normal
  unfold finishBorrowedExitChannels at normal
  cases cleanup : exitChannelCleanupBorrowed origin borrowed tokens cancel carriers initial with
  | ok ignored after =>
      simp only [cleanup] at normal
      exact never after values final normal
  | stop reason after | escape address payload after | jump target kind after =>
      simp only [cleanup] at normal
      cases normal

private theorem exit_nonreturning (origin : Goose.Core.OriginId)
    (borrowed : List BorrowedWaitingExitReservation) (tokens : List Nat)
    (initial final : ExecutionState) (values : List Carrier) :
    (∀ reason,
      finishBorrowedExitChannels origin borrowed tokens false [] (.stop reason) initial ≠ .ok values final) ∧
    (∀ address carriers,
      finishBorrowedExitChannels origin borrowed tokens true carriers (.escape address carriers) initial ≠ .ok values final) ∧
    (∀ target kind carriers,
      finishBorrowedExitChannels origin borrowed tokens true carriers (.jump target kind) initial ≠ .ok values final) := by
  refine ⟨?_, ?_, ?_⟩
  all_goals intros; apply finishBorrowedExitChannels_not_ok
  all_goals intro state values final impossible; cases impossible

theorem withExitChannels_ok_origin (source activation : RuntimeActivation) (operands : List Expr)
    (origin : Goose.Core.OriginId) (action : List Channel → EvalM (List Carrier))
    (initial final : ExecutionState) (carriers : List Carrier)
    (normal : withExitChannels source activation operands origin action initial = .ok carriers final) :
    ∃ channels prepared raw afterOperands afterMaterialized,
      exitChannels source activation operands origin initial = .ok channels prepared ∧
      action channels prepared = .ok raw afterOperands ∧
      materializeOwnedCarriers origin (exitChannelReservationTokens initial.construction.exitReservations.size prepared)
        raw afterOperands = .ok carriers afterMaterialized ∧
      exitChannelCleanupBorrowed origin (borrowedExitChannelReceipts activation initial)
        (exitChannelReservationTokens initial.construction.exitReservations.size prepared) false carriers
        afterMaterialized = .ok () final := by
  rw [withExitChannels_decomposition] at normal
  cases setup : exitChannels source activation operands origin initial with
  | stop reason after | escape address payload after | jump target kind after =>
      simp only [setup] at normal
      cases normal
  | ok channels prepared =>
      simp only [setup] at normal
      cases evaluated : action channels prepared with
      | stop reason after =>
          simp only [evaluated] at normal
          exact False.elim ((exit_nonreturning _ _ _ after final carriers).1 reason normal)
      | escape address payload after =>
          simp only [evaluated] at normal
          exact False.elim ((exit_nonreturning _ _ _ after final carriers).2.1 address payload normal)
      | jump target kind after =>
          simp only [evaluated] at normal
          exact False.elim ((exit_nonreturning _ _ _ after final carriers).2.2 target kind _ normal)
      | ok raw afterOperands =>
          simp only [evaluated] at normal
          cases materialized : materializeOwnedCarriers origin
              (exitChannelReservationTokens initial.construction.exitReservations.size prepared) raw afterOperands with
          | stop reason after =>
              simp only [materialized] at normal
              exact False.elim ((exit_nonreturning _ _ _ after final carriers).1 reason normal)
          | escape address payload after =>
              simp only [materialized] at normal
              exact False.elim ((exit_nonreturning _ _ _ after final carriers).2.1 address payload normal)
          | jump target kind after =>
              simp only [materialized] at normal
              exact False.elim ((exit_nonreturning _ _ _ after final carriers).2.2 target kind _ normal)
          | ok completed afterMaterialized =>
              simp only [materialized, finishBorrowedExitChannels] at normal
              cases cleanup : exitChannelCleanupBorrowed origin (borrowedExitChannelReceipts activation initial)
                  (exitChannelReservationTokens initial.construction.exitReservations.size prepared)
                  false completed afterMaterialized with
              | ok ignored after =>
                  cases ignored
                  simp only [cleanup] at normal
                  cases normal
                  exact ⟨channels, prepared, raw, afterOperands, afterMaterialized, rfl, evaluated, materialized, cleanup⟩
              | stop reason after | escape address payload after | jump target kind after =>
                  simp only [cleanup] at normal
                  cases normal

theorem returnFrom_escape_origin (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (targetId : Nat) (operands : List Expr) (origin : Goose.Core.OriginId)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : execStmt (fuel + 1) config environment (.returnFrom targetId operands origin) initial =
      .escape address carriers final) :
    ∃ activation target discarded outer,
      config.module.targets[targetId]? = some target ∧
      initial.activations = discarded ++ activation :: outer ∧
      target.contains activation.implementation = true ∧
      (∀ earlier ∈ discarded, target.contains earlier.implementation = false) ∧
      (withExitChannels environment activation operands origin
          (fun channels => evalOperands fuel config environment channels operands) initial =
        .escape address carriers final ∨
       (withExitChannels environment activation operands origin
          (fun channels => evalOperands fuel config environment channels operands) initial =
        .ok carriers final ∧ address = ⟨activation.act, .nonlocal targetId⟩)) := by
  simp only [execStmt] at escaped
  cases selected : targetActivation config targetId initial with
  | stop reason after | jump target kind after =>
    simp only [bind, selected] at escaped
    cases escaped
  | escape target payload after =>
    exact False.elim (neverEscapes_targetActivation config targetId initial target payload after selected)
  | ok activation after =>
    obtain ⟨unchanged, target, discarded, outer, declared, stack, included, excluded⟩ :=
      targetActivation_selects_nearest config targetId initial after activation selected
    subst after
    refine ⟨activation, target, discarded, outer, declared, stack, included, excluded, ?_⟩
    cases returned : withExitChannels environment activation operands origin
        (fun channels => evalOperands fuel config environment channels operands) initial with
    | stop reason after | jump target kind after =>
      simp only [bind, selected, returned] at escaped
      cases escaped
    | escape target payload after =>
      simp only [bind, selected, returned] at escaped
      cases escaped
      exact Or.inl rfl
    | ok payload after =>
      simp only [bind, selected, returned, Goose.Construct.escaped] at escaped
      cases escaped
      exact Or.inr ⟨rfl, rfl⟩

theorem returnFrom_escape_operands_origin (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (targetId : Nat) (operands : List Expr) (origin : Goose.Core.OriginId)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : execStmt (fuel + 1) config environment (.returnFrom targetId operands origin) initial =
      .escape address carriers final) :
    ∃ activation target discarded outer,
      config.module.targets[targetId]? = some target ∧
      initial.activations = discarded ++ activation :: outer ∧
      target.contains activation.implementation = true ∧
      (∀ earlier ∈ discarded, target.contains earlier.implementation = false) ∧
      (withExitChannels environment activation operands origin
          (fun channels => evalOperands fuel config environment channels operands) initial =
        .escape address carriers final ∨
       ∃ channels prepared raw afterOperands afterMaterialized,
         exitChannels environment activation operands origin initial = .ok channels prepared ∧
         evalOperands fuel config environment channels operands prepared = .ok raw afterOperands ∧
         materializeOwnedCarriers origin (exitChannelReservationTokens initial.construction.exitReservations.size prepared)
           raw afterOperands = .ok carriers afterMaterialized ∧
         exitChannelCleanupBorrowed origin (borrowedExitChannelReceipts activation initial)
           (exitChannelReservationTokens initial.construction.exitReservations.size prepared) false carriers
           afterMaterialized = .ok () final ∧
         address = ⟨activation.act, .nonlocal targetId⟩) := by
  obtain ⟨activation, target, discarded, outer, declared, stack, included, excluded, occurrence⟩ :=
    returnFrom_escape_origin fuel config environment targetId operands origin initial final address carriers escaped
  refine ⟨activation, target, discarded, outer, declared, stack, included, excluded, ?_⟩
  rcases occurrence with interrupted | ⟨normal, emitted⟩
  · exact Or.inl interrupted
  · obtain ⟨channels, prepared, raw, afterOperands, afterMaterialized, setup, evaluated, materialized, released⟩ :=
      withExitChannels_ok_origin environment activation operands origin
        (fun channels => evalOperands fuel config environment channels operands) initial final carriers normal
    exact Or.inr ⟨channels, prepared, raw, afterOperands, afterMaterialized, setup, evaluated, materialized, released, emitted⟩

#print axioms returnFrom_escape_origin
#print axioms enterActivation_escape_origin
#print axioms execActivationBody_escape_origin
#print axioms execResultScope_escape_unwinds_scope
#print axioms execBlock_escape_unwinds_scope
#print axioms execBlock_escape_call
#print axioms execResultScope_escape_call
#print axioms withExitChannels_ok_origin
#print axioms returnFrom_escape_operands_origin

end Goose.Proofs.ExitExecution
