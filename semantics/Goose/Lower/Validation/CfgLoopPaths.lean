import Goose.Lower.Validation.CfgIfPaths

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem paths_loopBody {condition : ValueId} {body : Nat → BlockId → B ValueId} {back : B Unit}
    (bodyAdvance : ∀ depth exit, AdvB (body depth exit))
    (bodyPaths : ∀ depth exit, BoundedRun ReachableBuilder (body depth exit))
    (backPaths : BoundedRun ReachableBuilder back)
    {env : LEnv} {before after : LS} {result : Unit} {source : BlockId}
    (run : loopBody condition body back env before = (result, after))
    (current : before.cur = some source) (paths : ReachableBuilder before)
    (bounded : LiveBound before) : ReachableBuilder after := by
  unfold loopBody at run
  simp only [bind_eq] at run
  obtain ⟨state, first, readRun, ⟨bodyBlock, exitBlock⟩, forked, forkRun,
    _, started, startRun, bodyValue, bodyEnd, bodyRun, _, backEnd, backRun, exitRun⟩ := run
  have same : first = before := (Prod.mk.inj readRun).2.symm
  subst first
  have forkPaths := paths.fork current (bounded source current) condition env
  have forkBounds := liveBound_fork current condition env
  rw [forkRun] at forkPaths forkBounds
  dsimp only at forkPaths forkBounds
  have startedPaths := forkPaths.of_blocks (setCur_blocks startRun)
  have startedBound := liveBound_setCur forkBounds.1 env
  rw [startRun] at startedBound
  have bodyEndPaths := bodyPaths _ _ env started bodyValue bodyEnd bodyRun startedPaths startedBound
  have bodyEndBound := liveBound_of_adv (bodyAdvance _ _ env started bodyValue bodyEnd bodyRun) startedBound
  have backEndPaths := backPaths env bodyEnd _ backEnd backRun bodyEndPaths bodyEndBound
  exact backEndPaths.of_blocks (setCur_blocks exitRun)

end Goose.Lower.Validation
