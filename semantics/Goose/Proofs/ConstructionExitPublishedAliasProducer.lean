import Goose.Proofs.ConstructionExitAliasProtection
import Goose.Proofs.ExitExecutionChecks

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst OriginId VarId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

theorem rootOf_state_independent (environment : RuntimeActivation) (id : VarId)
    (before after : ExecutionState) (root : RootInst)
    (found : rootOf environment id before = .ok root before) :
    rootOf environment id after = .ok root after := by
  simp only [rootOf] at found ⊢
  cases descriptor : environment.vars[id]? with
  | none => simp [descriptor, fault, EvalM.stop] at found
  | some desc =>
    simp only [descriptor] at found ⊢
    cases scope : environment.scopes.find? (fun entry => entry.1 == desc.scope) with
    | none => simp [scope, fault, EvalM.stop] at found
    | some entry =>
      cases entry with
      | mk scopeId scopeInst =>
        simp only [scope, pure, ExecutionStep.ok.injEq] at found ⊢
        exact found

theorem published_alias_evalProduce_fault (config : EvalConfig) (source : RuntimeActivation) (state : ExecutionState)
    (token incoming count fuel : Nat) (snapshot : PendingDestination) (localVar : VarId) (origin : OriginId)
    (root : RootInst) (stored : StoredValue)
    (waiting : state.construction.exitReservations[token]? = some (.waiting incoming))
    (present : state.construction.destinations[incoming]? = some snapshot) (published : snapshot.progress = .published count)
    (current : destinationCurrent state.construction incoming = .ok incoming)
    (rooted : rootOf source localVar state = .ok root state)
    (value : state.objects.lookup root = some (.stored stored)) (alias : stored.destination = some incoming) :
    let activated := { state with construction := { state.construction with
      exitReservations := state.construction.exitReservations.set! token (.active (.named .awaitingSource) incoming incoming snapshot) } }
    evalProduce (fuel + 2) config source [.completion token] (.resultLocal localVar origin) state = .stop (.fault .flow) activated := by
  let activated := { state with construction := { state.construction with
    exitReservations := state.construction.exitReservations.set! token (.active (.named .awaitingSource) incoming incoming snapshot) } }
  obtain ⟨actual, selected, stopped⟩ := published_alias_select_then_prepare_fault source state token incoming count snapshot localVar origin root stored
    waiting present published current rooted value alias
  have expected := selectCompletion_named_published_alias source state token incoming count snapshot localVar origin root stored
    waiting present published current rooted value alias
  have same : actual = activated := (ExecutionStep.ok.inj (selected.symm.trans expected)).2
  subst actual
  have rootAfter := rootOf_state_independent source localVar state activated root rooted
  have read : readLoc (fuel + 1) config.layout ⟨root, []⟩ activated = .ok (.stored stored) activated := by
    simp [readLoc, EvalM.get, activated, value, readValuePath, bind, pure]
  simp only [activated] at rootAfter read stopped
  simp only [evalProduce, List.mapM_cons, List.mapM_nil, bind, pure, expected, rootAfter, read, stopped]

def publishedLocalReturn (named : Option VarId) : Module := Id.run do
  let owner : Ty := .varr (.int .u8)
  let entry : Impl := ⟨"entry", #[], #[], #[⟨"v", owner, .immutable, 0, 0⟩],
    .mk 0 [.letS 0 (.call 1 [] 0) 0, .print [.view (.of (.var 0))] 0] none, .unknown⟩
  let producer : Impl := ⟨"producer", #[], #[⟨owner, .value, named⟩], #[⟨"x", owner, .immutable, 0, 0⟩],
    .mk 0 [.letS 0 (.bytes owner [65] 0) 0] (some (.resultLocal 0 0)), .unknown⟩
  return ⟨#["published-local.goose"], #[.int .u8, owner], #[], #[entry, producer],
    #[⟨0, "entry", [], [], []⟩, ⟨1, "producer", [], [[]], []⟩], 0, #[⟨0, 1, "let"⟩], #[], #[]⟩

theorem published_local_unnamed_rejected :
    (match validate (publishedLocalReturn none) with | .ok () => "" | .error rejection => rejection.message) =
      "V-RESULT: named result aliases disagree with structural eligibility" := by cbv

theorem published_local_named_validated : validate (publishedLocalReturn (some 0)) = .ok () := by cbv

theorem published_local_unnamed_execution :
    Goose.Proofs.ExitExecutionChecks.returnedObservation (eval 200 .release (publishedLocalReturn none)) =
      some ([65, 10], [.begin 0, .begin 1, .write 1 0, .publish 1, .copy (.storage 1 []) 0, .write 0 0, .publish 0]) := by cbv

theorem published_local_named_execution :
    Goose.Proofs.ExitExecutionChecks.returnedObservation (eval 200 .release (publishedLocalReturn (some 0))) =
      some ([65, 10], [.begin 0, .write 0 0, .publish 0]) := by cbv

#print axioms published_local_unnamed_rejected
#print axioms published_local_named_validated
#print axioms published_local_unnamed_execution
#print axioms published_local_named_execution
#print axioms rootOf_state_independent
#print axioms published_alias_evalProduce_fault

end Goose.Proofs.ConstructionAcceptedExecution
