import Goose.Proofs.ConstructionExitSampledBindWorld
import Goose.Proofs.ExitExecutionPathContext

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (OriginId VarId RootInst)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

theorem receive_single_completed_execution (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (localVar : VarId) (producer : Expr) (origin : OriginId) (descriptor : Goose.Construct.LocalVar)
    (id : Nat) (initial created produced published final : ExecutionState) (root : RootInst) (stored : StoredValue)
    (declared : environment.vars[localVar]? = some descriptor)
    (inline : ((expressionResultTypes? (max fuel (expressionQueryBudget producer)) ⟨config.module, environment.vars⟩ producer).bind
      (fun types => types[0]?)).filter (fun ty => ty.flat) = none)
    (nonfixed : descriptor.ty.nonfixed = true)
    (createdResult : newDestination config.layout environment.act descriptor.ty .value origin none none initial = .ok id created)
    (producerResult : evalProduce fuel config environment [.construct id] producer created = .ok [.completed id] produced)
    (publishedResult : publishCarriers origin [.completed id] produced = .ok () published)
    (rooted : rootOf environment localVar published = .ok root published)
    (sampled : storedDestination id published = .ok stored published)
    (bound : bindRoot root (.stored stored) published = .ok () final) :
    execStmt (fuel + 1) config environment (.receive [localVar] producer origin) initial = .ok (.normal .unit) final := by
  simp only [execStmt, List.zipIdx_cons, List.zipIdx_nil, List.mapM_cons, List.mapM_nil, declared, inline, nonfixed,
    ↓reduceIte, createdResult, producerResult, List.length_cons, List.length_nil, bne_self_eq_false,
    Bool.false_eq_true, List.zip_cons_cons, List.zip_nil_left, List.forIn_cons, List.forIn_nil, bind, pure,
    publishedResult, rooted, carrierValue, sampled, bound]

theorem reached_receive_single_completed_world (rootFuel fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (localVar : VarId) (producer : Expr) (origin : OriginId) (descriptor : Goose.Construct.LocalVar)
    (id : Nat) (initial created produced published : ExecutionState) (root : RootInst) (stored : StoredValue)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (reached : ExitReached rootFuel config (.statement (fuel + 1) environment (.receive [localVar] producer origin)) initial)
    (declared : environment.vars[localVar]? = some descriptor)
    (inline : ((expressionResultTypes? (max fuel (expressionQueryBudget producer)) ⟨config.module, environment.vars⟩ producer).bind
      (fun resultTypes => resultTypes[0]?)).filter (fun ty => ty.flat) = none)
    (nonfixed : descriptor.ty.nonfixed = true)
    (createdResult : newDestination config.layout environment.act descriptor.ty .value origin none none initial = .ok id created)
    (producerResult : evalProduce fuel config environment [.construct id] producer created = .ok [.completed id] produced)
    (publishedResult : publishCarriers origin [.completed id] produced = .ok () published)
    (world : AcceptedWorld config initialized published ambient types live regions pending)
    (rooted : rootOf environment localVar published = .ok root published)
    (sampled : storedDestination id published = .ok stored published)
    (compatible : RootTypeCompatible types root descriptor.ty) (conforms : LayoutConforms config.layout descriptor.ty)
    (represented : ValueRepresentation descriptor.ty (.stored stored)) (backed : StoredValueBacking config.layout published stored)
    (fresh : published.objectOrdinals.lookup root = none)
    (regionSafety : ∀ region ∈ regions, ¬ region.mutableRoots root →
      StoredBackingObservation config.layout published region.limit stored ∧
        ∀ other, stored.destination = some other → other ∉ region.mutableDestinations)
    (freshType : ∀ act scope index, root = .local act scope index → act < published.nextAct ∧ scope < published.nextScope)
    (freshSynthetic : ∀ index, root = .global index → config.module.globals.size ≤ index →
      index < config.module.globals.size + published.nextScope) :
    ∃ final, ExitReached rootFuel config (.statement (fuel + 1) environment (.receive [localVar] producer origin)) initial ∧
      execStmt (fuel + 1) config environment (.receive [localVar] producer origin) initial = .ok (.normal .unit) final ∧
      final.objects.lookup root = some (.stored stored) ∧
      AcceptedWorld config initialized final ambient (registerRootType types root descriptor.ty)
        (fun other => other = root ∨ live other) regions pending := by
  obtain ⟨final, bound, extended, accepted⟩ := bindRoot_freshStored_world config initialized published ambient types live root descriptor.ty stored
    world compatible conforms represented backed fresh regionSafety freshType freshSynthetic
  obtain ⟨other, otherBound, objects⟩ := Goose.Proofs.ConstructionRootCorrespondence.bindRoot_objects root (.stored stored) published
  have same : other = final := (ExecutionStep.ok.inj (otherBound.symm.trans bound)).2
  subst other
  have found : final.objects.lookup root = some (.stored stored) := by simp [objects]
  exact ⟨final, reached, receive_single_completed_execution fuel config environment localVar producer origin descriptor id initial created produced published final root stored
    declared inline nonfixed createdResult producerResult publishedResult rooted sampled bound, found, accepted⟩

#print axioms reached_receive_single_completed_world
#print axioms receive_single_completed_execution

end Goose.Proofs.ConstructionAcceptedExecution
