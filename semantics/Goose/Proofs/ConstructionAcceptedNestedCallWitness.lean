import Goose.Proofs.ConstructionAcceptedRecursiveCallModule
import Goose.Proofs.ConstructionAcceptedRecursiveMixedGlobalModule
import Goose.Construct.Validate
import Goose.Construct.Eval
import Goose.Proofs.ConstructionAcceptedLocalRead

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

private def nestedCallSummary : SummaryAnn := .known ⟨[], [], [], [], [], [], [], [], false, false⟩
private def nestedCallEntry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, nestedCallSummary⟩
private def nestedCallInner : Impl := ⟨"inner", #[], #[⟨.int .i64, .register, none⟩],
  #[⟨"value", .int .i64, .immutable, 0, 0⟩],
  .mk 0 [.letS 0 (.lit .i64 7) 0] (some (.read (.var 0))), nestedCallSummary⟩
private def nestedCallOuter : Impl := ⟨"outer", #[], #[⟨.int .i64, .register, none⟩], #[],
  .mk 0 [] (some (.call 2 [] 0)), nestedCallSummary⟩
private def nestedCallModule : Module := ⟨#["nested-call.goose"], #[.int .i64],
  #[⟨"answer", .int .i64, .immutable, .call 1 [] 0, 0⟩],
  #[nestedCallEntry, nestedCallOuter, nestedCallInner],
  #[⟨0, "entry", [], [], []⟩, ⟨1, "outer", [], [[]], []⟩, ⟨2, "inner", [], [[]], []⟩],
  0, #[⟨0, 1, "call"⟩], #[], #[]⟩
private def nestedCallObservation : Option Int :=
  match runModule 100 ⟨.release, nestedCallModule⟩ .initial with
  | .ok () state => match state.objects.lookup (.global 0) with
    | some (.int .i64 value) => some value
    | _ => none
  | _ => none

theorem validated_global_noDirectLocalRead (module : Module) (global localId : Nat) (descriptor : Global)
    (accepted : validate module = .ok ()) (present : module.globals[global]? = some descriptor) :
    descriptor.init ≠ .read (.var localId) := by
  intro shape
  obtain ⟨ty, after, typed, _⟩ := validated_global_initializer_typing module global descriptor accepted present
  rw [shape] at typed
  obtain ⟨_, visible, _, _, _, _⟩ := typeExpr_localRead_descriptor 4096
    { module := module, implementation := none, variables := #[], visible := [], scope := 0, loops := 0,
      globalLimit := global } localId 0 after ty typed
  simp at visible

theorem nestedCall_validated : validate nestedCallModule = .ok () := by cbv

theorem nestedCall_result : nestedCallObservation = some 7 := by decide +kernel

theorem nestedCall_graph : RegisterCallGraph ⟨.release, nestedCallModule⟩ (.int .i64) := by
  intro target context implementation contextAt implementationAt parameters results
  cases target with
  | zero =>
    simp [nestedCallModule] at contextAt
    subst context
    simp [nestedCallModule, nestedCallEntry] at implementationAt
    subst implementation
    simp [nestedCallEntry] at results
  | succ target =>
    cases target with
    | zero =>
      simp [nestedCallModule] at contextAt
      subst context
      simp [nestedCallModule] at implementationAt
      subst implementation
      refine ⟨_, rfl, Or.inr ⟨0, 2, 0, _, nestedCallInner, rfl, rfl, rfl, rfl, rfl⟩⟩
    | succ target =>
      cases target with
      | zero =>
        simp [nestedCallModule] at contextAt
        subst context
        simp [nestedCallModule] at implementationAt
        subst implementation
        refine ⟨_, rfl, Or.inl ⟨0, _, _, rfl, ?_, ?_, ?_⟩⟩
        · repeat constructor
        · repeat constructor
        · intro id expression origin member descriptor found
          simp [nestedCallInner] at member found
          obtain ⟨rfl, rfl, rfl⟩ := member
          simp at found
          subst descriptor
          exact Or.inl ⟨.i64, rfl⟩
      | succ target => simp [nestedCallModule] at contextAt

theorem nestedCall_initializer_allFuel (fuel : Nat) :
    ∃ completed types live ambient,
      let outcome := initGlobals fuel ⟨.release, nestedCallModule⟩ [0] .initial
      let after := Goose.Proofs.Exit.stepState outcome
      RootTypesExtend (declaredRootTypes nestedCallModule) types ∧ completed ≤ 1 ∧
      AcceptedWorld ⟨.release, nestedCallModule⟩ completed after ambient types live [] [] ∧
      (match outcome with
       | .ok _ _ => ambient = [] ∧ completed = 1 ∧ FutureGlobalsClear ⟨.release, nestedCallModule⟩ completed after
       | .stop _ _ => completed = 0 ∧ FutureGlobalsClear ⟨.release, nestedCallModule⟩ 0 after
       | .escape .. | .jump .. => False) := by
  let config : EvalConfig := ⟨.release, nestedCallModule⟩
  let descriptor : Global := ⟨"answer", .int .i64, .immutable, .call 1 [] 0, 0⟩
  let context : Context := ⟨1, "outer", [], [[]], []⟩
  have safe := initGlobals_recursive_register_single fuel 0 config (acceptedModule config nestedCall_validated)
    .initial [] (declaredRootTypes nestedCallModule) (fun _ => False) descriptor 1 0 context nestedCallOuter
    (initial_acceptedWorld config nestedCall_validated) (futureGlobalsClear_initial config)
    (by rfl) (by rfl) (Or.inl ⟨.i64, rfl⟩) (by rfl) (by rfl) (by rfl) (by rfl) nestedCall_graph
  obtain ⟨completed, types, live, ambient, extend, lower, upper, world, result⟩ := safe
  exact ⟨completed, types, live, ambient, extend, upper, world, result⟩

theorem nestedCall_module_allFuel (fuel : Nat) :
    ∃ initialized ambient types live regions,
      AcceptedWorld ⟨.release, nestedCallModule⟩ initialized
        (Goose.Proofs.Exit.stepState (runModule fuel ⟨.release, nestedCallModule⟩ .initial)) ambient types live regions [] ∧
      (match runModule fuel ⟨.release, nestedCallModule⟩ .initial with
       | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  let config : EvalConfig := ⟨.release, nestedCallModule⟩
  let descriptor : Global := ⟨"answer", .int .i64, .immutable, .call 1 [] 0, 0⟩
  let calleeContext : Context := ⟨1, "outer", [], [[]], []⟩
  let entryContext : Context := ⟨0, "entry", [], [], []⟩
  apply acceptedRecursiveCallModule_allFuel fuel config (acceptedModule config nestedCall_validated)
    descriptor 1 0 calleeContext nestedCallOuter (by rfl) (by rfl) (by rfl) (Or.inl ⟨.i64, rfl⟩)
    (by rfl) (by rfl) (by rfl) (by rfl) nestedCall_graph entryContext nestedCallEntry (by rfl) (by rfl)
  · exact .nil
  · simp [nestedCallEntry, Block.stmts]
  · simp [nestedCallEntry, Block.stmts]
  · simp [nestedCallEntry, Block.stmts]
  · simp [nestedCallEntry, Block.stmts]
  · rfl

private def mixedNestedCallModule : Module := ⟨#["mixed-nested-call.goose"], #[.int .i64, .varr (.int .u8)],
  #[⟨"bytes", .varr (.int .u8), .immutable, .bytes (.varr (.int .u8)) [65] 0, 0⟩,
    ⟨"answer", .int .i64, .immutable, .call 1 [] 0, 0⟩],
  #[nestedCallEntry, nestedCallOuter, nestedCallInner],
  #[⟨0, "entry", [], [], []⟩, ⟨1, "outer", [], [[]], []⟩, ⟨2, "inner", [], [[]], []⟩],
  0, #[⟨0, 1, "call"⟩], #[], #[]⟩

private def mixedNestedCallConfig : EvalConfig := ⟨.release, mixedNestedCallModule⟩

theorem mixedNestedCall_validated : validate mixedNestedCallModule = .ok () := by cbv

theorem mixedNestedCall_graph : RegisterCallGraph mixedNestedCallConfig (.int .i64) := by
  simpa [RegisterCallGraph, RegisterCalleeForm, mixedNestedCallConfig, mixedNestedCallModule, nestedCallModule] using nestedCall_graph

private def mixedNestedCallObservation : Option Int :=
  match runModule 100 mixedNestedCallConfig .initial with
  | .ok () state => match state.objects.lookup (.global 1) with
    | some (.int .i64 value) => some value
    | _ => none
  | _ => none

theorem mixedNestedCall_result : mixedNestedCallObservation = some 7 := by decide +kernel

theorem mixedNestedCall_allFuel (fuel : Nat) :
    ∃ initialized ambient types live regions,
      AcceptedWorld mixedNestedCallConfig initialized
        (Goose.Proofs.Exit.stepState (runModule fuel mixedNestedCallConfig .initial)) ambient types live regions [] ∧
      (match runModule fuel mixedNestedCallConfig .initial with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  have scalars : FlatGlobalsAreScalar mixedNestedCallConfig := by
    intro id descriptor declared flat
    cases id with
    | zero =>
      have same : descriptor = ⟨"bytes", .varr (.int .u8), .immutable, .bytes (.varr (.int .u8)) [65] 0, 0⟩ := by
        simpa [mixedNestedCallConfig, mixedNestedCallModule] using declared.symm
      subst descriptor
      simp [Ty.flat] at flat
    | succ id =>
      cases id with
      | zero =>
        have same : descriptor = ⟨"answer", .int .i64, .immutable, .call 1 [] 0, 0⟩ := by
          simpa [mixedNestedCallConfig, mixedNestedCallModule] using declared.symm
        subst descriptor
        exact Or.inl ⟨.i64, rfl⟩
      | succ id => simp [mixedNestedCallConfig, mixedNestedCallModule] at declared
  apply acceptedRecursiveMixedGlobalModule_allFuel fuel mixedNestedCallConfig
    (acceptedModule mixedNestedCallConfig mixedNestedCall_validated) scalars ⟨0, "entry", [], [], []⟩ nestedCallEntry
  · intro id inside
    change id < 2 at inside
    cases id with
    | zero => exact ⟨_, rfl, Or.inl (Or.inr ⟨[65], 0, rfl, rfl⟩)⟩
    | succ id =>
      cases id with
      | zero => exact ⟨_, rfl, Or.inr ⟨1, 0, ⟨1, "outer", [], [[]], []⟩, nestedCallOuter,
          rfl, Or.inl ⟨.i64, rfl⟩, rfl, rfl, rfl, rfl, mixedNestedCall_graph⟩⟩
      | succ id => omega
  · rfl
  · rfl
  · exact .nil
  · simp [nestedCallEntry, Block.stmts]
  · simp [nestedCallEntry, Block.stmts]
  · simp [nestedCallEntry, Block.stmts]
  · simp [nestedCallEntry, Block.stmts]
  · rfl

#print axioms mixedNestedCall_result
#print axioms mixedNestedCall_allFuel
#print axioms mixedNestedCall_graph
#print axioms mixedNestedCall_validated
#print axioms nestedCall_module_allFuel
#print axioms nestedCall_initializer_allFuel
#print axioms nestedCall_graph
#print axioms validated_global_noDirectLocalRead
#print axioms nestedCall_validated
#print axioms nestedCall_result
end Goose.Proofs.ConstructionAcceptedExecution
