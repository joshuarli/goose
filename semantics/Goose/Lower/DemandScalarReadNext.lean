import Goose.Lower.DemandGeneratedScalarPrefix

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_scalar_read_next {cfg : Cfg} {env : Env} {place : Place} {state : St}
    (source : ExprSource cfg env (.read place) state) (form : ScalarReadPlace place)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.read place)) before)
    {required : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    {initial : GIR.Frame} {start : Pt} (point : before.pp = some start) (related : Rel cfg env cx initial before)
    (extended : ExtT (lowerExpr (.read place) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {taken : Nat} {runtime : DemandRuntimePoint} (unfinished : taken < 2)
    (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ runtime) :
    ∃ label id op, GeneratedDemandInstruction cfg.mod source.rootsEnv.access cx.fn required label runtime.point (.def id op) := by
  let le := lowerEnv cfg.mod env.vars results
  let addressed := lowerPlace place le before
  obtain ⟨child, typing, roots, canonical⟩ := source.readChild
  have childOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn le root child.path (.place place) before := by
    rw [canonical.path]
    exact .first occurrence (.expressionPlace rfl)
  have childRows : GeneratedDemandRows cfg.mod child.rootsEnv.access childOccurrence required := by
    have inherited : GeneratedDemandRows cfg.mod source.rootsEnv.access (.first occurrence (.expressionPlace rfl)) required :=
      .first (first := .expressionPlace rfl) rows
    simpa only [roots, canonical.path] using inherited
  obtain ⟨location, placed, post, firstStep⟩ := accepted_generated_scalar_place_address child form
    childOccurrence childRows point related (generated_read_place_extended extended)
  rcases steps.uncons with ⟨zero, rfl⟩ | ⟨remaining, current, count, actual, tail⟩
  · cases form with
    | global global =>
      have site := GeneratedDemandInstruction.globalAddress_auto childOccurrence childRows point (generated_read_place_extended extended)
      have parentSite : GeneratedDemandInstruction cfg.mod source.rootsEnv.access cx.fn required
          ⟨child.path, .place, .entry⟩ start (.def (lowerPlace (.global global) le before).1 (.globalAddr global)) := by
        simpa only [roots] using site
      exact ⟨_, _, _, parentSite⟩
    | slot slot =>
      have site := GeneratedDemandInstruction.slotAddress_auto childOccurrence childRows point (generated_read_place_extended extended)
      have parentSite : GeneratedDemandInstruction cfg.mod source.rootsEnv.access cx.fn required
          ⟨child.path, .place, .entry⟩ start (.def (lowerPlace (.var slot) le before).1 (.slotAddr slot)) := by
        simpa only [roots] using site
      exact ⟨_, _, _, parentSite⟩
  · obtain ⟨fuel, actualStep⟩ := runtimeStep_demandInstructionStep actual
    have same := actualStep.deterministic (firstStep fuel)
    have currentEq : current = ⟨(start.1, start.2 + 1), initial.set addressed.1 (.val (.ref location)), state⟩ := by
      cases current
      exact same
    subst current
    have remainingZero : remaining = 0 := by omega
    subst remaining
    cases tail
    have site := GeneratedDemandInstruction.load_auto occurrence rows post.pp extended
    exact ⟨_, _, _, site⟩

theorem generated_definition_maximal_stop {cx : FnCtx} {runtime : DemandRuntimePoint}
    {id : ValueId} {op : Op} {fuel : Nat} {stop : Stop} {after : St}
    (instruction : instAt cx.fn runtime.point = some (.def id op))
    (maximal : ∀ next, ¬ DemandInstructionStep cx (fuel - 1) runtime next)
    (run : GIR.runAt cx runtime.point runtime.frame fuel runtime.state = .stop stop after)
    (nonTimeout : stop ≠ .timeout) : DemandInstructionStop cx fuel runtime stop after := by
  cases fuel with
  | zero =>
    change timeout runtime.state = .stop stop after at run
    simp [timeout, M.stop] at run
    exact (nonTimeout run.1.symm).elim
  | succ fuel =>
    have noStep : ∀ next, ¬ DemandInstructionStep cx fuel runtime next := by simpa using maximal
    cases evaluated : execOp fuel cx runtime.frame op runtime.state with
    | ok value state => exact (noStep _ (.definition instruction evaluated)).elim
    | stop reason state =>
      have halted : DemandInstructionStop cx (fuel + 1) runtime reason state := .definition instruction evaluated
      have equal := halted.runAt.symm.trans run
      obtain ⟨rfl, rfl⟩ := Res.stop.inj equal
      exact halted

theorem accepted_generated_scalar_read_maximal_stop {cfg : Cfg} {env : Env} {place : Place} {state : St}
    (source : ExprSource cfg env (.read place) state) (form : ScalarReadPlace place)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.read place)) before)
    {required : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    {initial : GIR.Frame} {start : Pt} (point : before.pp = some start) (related : Rel cfg env cx initial before)
    (extended : ExtT (lowerExpr (.read place) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {taken : Nat} {runtime : DemandRuntimePoint} (unfinished : taken < 2)
    (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ runtime)
    {fuel : Nat} {stop : Stop} {after : St}
    (maximal : ∀ next, ¬ DemandInstructionStep cx (fuel - 1) runtime next)
    (run : GIR.runAt cx runtime.point runtime.frame fuel runtime.state = .stop stop after)
    (nonTimeout : stop ≠ .timeout) : DemandInstructionStop cx fuel runtime stop after := by
  obtain ⟨label, id, op, site⟩ := accepted_generated_scalar_read_next source form occurrence rows point related extended unfinished steps
  exact generated_definition_maximal_stop site.instruction maximal run nonTimeout

#print axioms accepted_generated_scalar_read_next
#print axioms generated_definition_maximal_stop
#print axioms accepted_generated_scalar_read_maximal_stop
end Goose.Lower
