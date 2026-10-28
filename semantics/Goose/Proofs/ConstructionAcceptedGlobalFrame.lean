import Goose.Proofs.ConstructionAcceptedScalarEffects
import Goose.Proofs.ConstructionAcceptedGlobalPrefix
import Lean.Elab.Tactic

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

private def initializerRootHelperName (name : String) : Lean.Name :=
  Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Goose") "Construct") "Roots") 0) "Goose") "Construct") name

elab "unfold_initializer_root_checker" : tactic => do
  let checker := Lean.mkIdent (initializerRootHelperName "checkInitFacts")
  Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $checker at *))

def initializerSource (config : EvalConfig) (names : Array (List RootRef)) : PEnv :=
  ⟨config.module, initImpl, initContext, [], none, #[], #[], [], names, []⟩

theorem initializerRootFacts_operand (config : EvalConfig) (id : Nat) (descriptor : Global)
    (names : Array (List RootRef)) (calls : List (Goose.Core.ContextId × List (List RootRef)))
    (present : config.module.globals[id]? = some descriptor)
    (facts : InitializerRootFactsAt config.module id calls names) :
    ∃ roots after, rpExpr (initializerSource config names) descriptor.init ⟨0, {}, []⟩ = .ok (roots, after) := by
  obtain ⟨effects, checked, callsEq⟩ := facts
  unfold_initializer_root_checker
  simp only [present] at checked
  cases rooted : rpExpr (initializerSource config names) descriptor.init ⟨0, {}, []⟩ with
  | error failure =>
    simp only [initializerSource] at rooted
    simp [StateT.run, rooted, bind, StateT.bind, Except.bind] at checked
  | ok result => exact ⟨result.1, result.2, rfl⟩

def scalarGlobalInitializerFrame (config : EvalConfig) (id act : Nat) (names : Array (List RootRef)) : ConstructionSourceFrame :=
  { phase := .initializer id
    typing := {
      module := config.module
      implementation := none
      variables := #[]
      visible := []
      scope := 0
      loops := 0
      globalLimit := id }
    source := initializerSource config names
    interpretation := EntryInterpretation ⟨0, act, #[], [], []⟩ config.module.globals.size
    initialized := id
    typingFuel := 4096
    typingCounter := 0
    rootCursor := ⟨0, {}, []⟩ }

theorem accepted_scalarGlobalInitializer_frame (config : EvalConfig) (accepted : AcceptedModule config)
    (id : Nat) (descriptor : Global) (before : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (world : AcceptedWorld config id before ambient types live [] []) (clear : FutureGlobalsClear config id before)
    (present : config.module.globals[id]? = some descriptor) :
    ∃ names, let activated := { before with nextAct := before.nextAct + 1 }
      AcceptedWorld config id activated ambient types live [] [] ∧
      AcceptedFrame config accepted (scalarGlobalInitializerFrame config id before.nextAct names) activated types ∧
      ∃ roots after, rpExpr (initializerSource config names) descriptor.init ⟨0, {}, []⟩ = .ok (roots, after) := by
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  obtain ⟨calls, ⟨names, facts⟩, closure⟩ := (Classical.choose_spec accepted.roots).2.2 id inside
  have rootFacts := initializerRootFacts_operand config id descriptor names calls present facts
  let frame := scalarGlobalInitializerFrame config id before.nextAct names
  let activated := { before with nextAct := before.nextAct + 1 }
  have origin : SourceOrigin accepted frame := by
    change ∃ descriptor, config.module.globals[id]? = some descriptor ∧ _
    exact ⟨descriptor, present, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, calls, facts, closure⟩
  have compatible : SourceFrameCompatible accepted frame := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simpa [frame, scalarGlobalInitializerFrame] using Nat.le_of_lt inside,
      by simpa [frame, scalarGlobalInitializerFrame] using Nat.le_of_lt inside, by simp [frame, scalarGlobalInitializerFrame],
      by simp [frame, scalarGlobalInitializerFrame], ?_, ?_, ?_, origin⟩
    · simp [frame, scalarGlobalInitializerFrame]
    · simp [frame, scalarGlobalInitializerFrame, initializerSource]
    · simp [frame, scalarGlobalInitializerFrame, initializerSource]
  have activeWorld := (freshAct_acceptedWorld config id before ambient types live world).2
  have activeClear := clear.freshAct
  have frameSource : AcceptedFrame config accepted frame activated types := by
    refine ⟨compatible, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [frame, scalarGlobalInitializerFrame, activated] using
        (freshAct_emptyParameters_frontier ⟨0, 0, #[], [], []⟩ config.module.globals.size before).2
    · simp [frame, scalarGlobalInitializerFrame, EntryInterpretation]
    · simp [frame, scalarGlobalInitializerFrame, initializerSource]
    · simpa [frame, scalarGlobalInitializerFrame, initializerSource] using entry_aliasComplete ⟨0, before.nextAct, #[], [], []⟩ config.module.globals.size
    · simp [frame, scalarGlobalInitializerFrame, LocalRepresentations]
    · simp [frame, scalarGlobalInitializerFrame]
    · intro other condition root resolved
      simp [frame, scalarGlobalInitializerFrame, EntryInterpretation, rootOf, fault, EvalM.stop] at resolved
    · intro other condition root resolved
      simp [frame, scalarGlobalInitializerFrame, EntryInterpretation, rootOf, fault, EvalM.stop] at resolved
    · intro global future within
      exact activeClear global future within
    · simp [frame, scalarGlobalInitializerFrame, LocalRootCorrespondence]
    · simp [frame, scalarGlobalInitializerFrame, ContentRootCorrespondence]
  exact ⟨names, activeWorld, frameSource, rootFacts⟩

private theorem initializer_scalar_passesTo_equal (source target : Ty)
    (scalar : (∃ ty, target = .int ty) ∨ target = .bool) (passing : source.passesTo target = true) :
    source = target := by
  rcases scalar with ⟨ty, rfl⟩ | rfl <;> cases source <;>
    simp [Ty.passesTo, Ty.adaptsTo, Ty.element?] at passing ⊢ <;> assumption

theorem accepted_scalarGlobalInitializer_checked (config : EvalConfig) (accepted : AcceptedModule config)
    (id : Nat) (descriptor : Global) (before : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (world : AcceptedWorld config id before ambient types live [] []) (clear : FutureGlobalsClear config id before)
    (present : config.module.globals[id]? = some descriptor) (form : AcceptedBinaryExpression descriptor.init)
    (scalar : (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool) :
    ∃ names roots typingAfter rootsAfter,
      let frame := scalarGlobalInitializerFrame config id before.nextAct names
      let activated := { before with nextAct := before.nextAct + 1 }
      AcceptedWorld config id activated ambient types live [] [] ∧
      AcceptedFrame config accepted frame activated types ∧
      CheckedValue frame descriptor.init descriptor.ty roots typingAfter rootsAfter := by
  obtain ⟨names, activeWorld, frameSource, roots, rootsAfter, rooted⟩ :=
    accepted_scalarGlobalInitializer_frame config accepted id descriptor before ambient types live world clear present
  obtain ⟨ty, typingAfter, typed, adapts⟩ := validated_global_initializer_typing config.module id descriptor accepted.accepted present
  have passes : ty.passesTo descriptor.ty = true := by
    rcases scalar with ⟨intTy, same⟩ | same <;> rw [same] at adapts ⊢ <;> cases ty <;> simpa [Ty.passesTo] using adapts
  have sameType := initializer_scalar_passesTo_equal ty descriptor.ty scalar passes
  subst ty
  let frame := scalarGlobalInitializerFrame config id before.nextAct names
  have initial : GlobalEffectTargetsBounded frame.rootCursor.eff id := by
    simp [frame, scalarGlobalInitializerFrame, GlobalEffectTargetsBounded, Eff.accessTargets]
  have effects := recursiveScalar_effects_bounded form 4096 frame.typing frame.source id 0 typingAfter frame.rootCursor
    rootsAfter [descriptor.ty] roots (by simp [frame, scalarGlobalInitializerFrame]) initial typed rooted
  have available : GlobalEffectsAvailable frame.interpretation id rootsAfter.eff := by
    intro target member global instantiated
    cases target with
    | global other =>
      change global = other at instantiated
      subst global
      exact effects other member
    | param parameter =>
      exact instantiated.1.elim
  exact ⟨names, roots, typingAfter, rootsAfter, activeWorld, frameSource, typed, rooted, available⟩

#print axioms accepted_scalarGlobalInitializer_checked
#print axioms accepted_scalarGlobalInitializer_frame
#print axioms initializerRootFacts_operand
end Goose.Proofs.ConstructionAcceptedExecution
