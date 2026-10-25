import Goose.GIR.ReplacementContentFlowProofsAssignedOriginsCallWrites
import Goose.GIR.ReplacementContentFlowProofsAssignedOriginsNormalization
import Goose.GIR.ReplacementContentFlowProofsClosure

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

private theorem edge_writes (func : Func) (state : State) (target : BlockId)
    (arguments : List ValueId) : (edge func state target arguments).writes = state.writes := by
  unfold edge
  split
  · rfl
  · apply List.foldlRecOn (motive := fun current : State => current.writes = state.writes)
    · rfl
    · intro current unchanged pair _
      exact unchanged

theorem step_writes (module : Module) (states : Array State) (func : Func)
    (types : Array (Option VTy)) (state : State) (inst : Inst) :
    (step module states func types state inst).writes =
      match inst with
      | .def _ (.call callee arguments _) =>
          (callState module states func state callee arguments).2.writes
      | .eff (.store address value _) =>
          if valRefLike types value then
            (write func (touchValues types state (accessOperands inst))
              (flowAt state.values address) (flowAt state.values value)).writes
          else state.writes
      | _ => state.writes := by
  cases inst with
  | «def» value op => cases op <;> rfl
  | eff effect =>
    cases effect <;> try rfl
    simp only [step, Id.run_pure]
    split <;> rfl
  | term terminal =>
    cases terminal <;> simp only [step, Id.run_pure, edge_writes, touchValues]
    case ret values origin => cases values with
      | nil => rfl
      | cons value values => cases values <;> rfl

private theorem call_assigned_against_final
    (module : Module) (states finalStates : Array State) (func : Func) (before final : State)
    (calleeId : FnId) (arguments : List ValueId) (callee : Func) (effects finalEffects : State)
    (calleeAt : module.funcs[calleeId]? = some callee)
    (effectsAt : states[calleeId]? = some effects)
    (finalEffectsAt : finalStates[calleeId]? = some finalEffects)
    (shape : effects.Shape callee)
    (arity : arguments.length = callee.params.length)
    (valueGrowth : ArrayExtends .unknown Roots.Extends before.values final.values)
    (writeSize : before.writes.size = final.writes.size)
    (operands : ∀ value ∈ arguments, ∃ actual, normalize func (flowAt final.values value) = some actual)
    (contents : ∀ index, (callee.roots.contents.find? (·.1 == index)).isSome = true →
      ∀ value, arguments[index]? = some value →
        content func final (flowAt final.values value) ≠ .pending)
    (writeSafety : ∀ (index : Nat) (roots : Roots), finalEffects.writes[index]? = some (.assigned roots) →
      roots = .pending ∨ ∃ actual, normalize callee roots = some actual)
    (old : ∀ index, Write.AssignedAt before.writes index → Write.ReadyAt final.writes index)
    (calleeReady : ∀ index, Write.AssignedAt effects.writes index →
      Write.ReadyAt finalEffects.writes index)
    (fixed : (callState module finalStates func final calleeId arguments).2.writes = final.writes)
    (index : Nat)
    (assigned : Write.AssignedAt (callState module states func before calleeId arguments).2.writes index) :
    Write.ReadyAt final.writes index := by
  have argumentAt : ∀ parameter ∈ callee.params.zipIdx,
      ∃ value, arguments[parameter.2]? = some value := by
    intro parameter member
    have found := List.mem_zipIdx_iff_getElem?.mp member
    have bound : parameter.2 < arguments.length := by
      have := List.getElem?_eq_some_iff.mp found |>.1
      omega
    exact ⟨arguments[parameter.2], List.getElem?_eq_getElem bound⟩
  have safe : ∀ parameter ∈ callee.params.zipIdx,
      ((arguments[parameter.2]?).map (flowAt before.values ·) |>.getD .unknown) ≠ .unknown := by
    intro parameter member
    obtain ⟨value, found⟩ := argumentAt parameter member
    obtain ⟨actual, known⟩ := operands value (List.mem_of_getElem? found)
    have finalSafe := normalize_not_unknown known
    have previousSafe : flowAt before.values value ≠ .unknown := by
      intro unknown
      have one := valueGrowth.values value
      simp only [flowAt] at unknown finalSafe
      rw [unknown] at one
      cases result : final.values[value]?.getD .unknown <;> simp_all [Roots.Extends]
    simpa [found] using previousSafe
  rw [callState_fold module states func before calleeId arguments callee effects
    calleeAt effectsAt] at assigned
  rcases callWrites_assigned_origin func before arguments effects _ callee.params.zipIdx
      index safe (fun parameter member => by
        have found := List.mem_zipIdx_iff_getElem?.mp member
        have bound := List.getElem?_eq_some_iff.mp found |>.1
        simpa [shape.writes] using bound) assigned with prior | fresh
  · exact old index prior
  · obtain ⟨parameter, member, slice, written, atoms, address, target, reference⟩ := fresh
    obtain ⟨value, found⟩ := argumentAt parameter member
    obtain ⟨actual, normalized⟩ := operands value (List.mem_of_getElem? found)
    have knownBefore : flowAt before.values value = .known atoms := by simpa [found] using address
    obtain ⟨finalAtoms, finalKnown, finalTarget⟩ :=
      (valueGrowth.values value).known_member (normalize_not_unknown normalized) knownBefore target
    obtain ⟨roots, finalWritten, ready⟩ := calleeReady parameter.2 written
    have normalizedRoots : ∃ actual, normalize callee roots = some actual := by
      rcases writeSafety parameter.2 roots finalWritten with pending | normalized
      · exact False.elim (ready pending)
      · exact normalized
    obtain ⟨result, normalizedResult⟩ := normalizedRoots
    have substitution := substitute_nonpending_of_normalized func callee final arguments roots
      result normalizedResult (fun value member => normalize_nonpending (operands value member).choose_spec)
      contents
    have bound : index < final.writes.size := by
      obtain ⟨r, present⟩ := assigned
      have b := Array.getElem?_eq_some_iff.mp present |>.1
      have sizes := (state_foldl_extends callee.params.zipIdx _
        (fun current parameter => callWriteStep_extends func before arguments effects current parameter)
        { before with touched := before.touched.join (substitute func before arguments (publicTouches effects.touched)) }).writes.size
      have finalSize := writeSize
      change before.writes.size = _ at sizes
      rw [← sizes] at b
      omega
    have result := callState_parameter_ready module finalStates func final calleeId arguments
      callee finalEffects calleeAt finalEffectsAt parameter index roots finalAtoms
      member slice finalWritten (by simpa [found, flowAt] using finalKnown) finalTarget bound reference substitution
    rwa [fixed] at result

private theorem state_at (module : Module) (states : Array State)
    (size : states.size = module.funcs.size) (index : Nat) (func : Func)
    (present : module.funcs[index]? = some func) : ∃ state, states[index]? = some state := by
  have bound := Array.getElem?_eq_some_iff.mp present |>.1
  have stateBound : index < states.size := by omega
  exact ⟨states[index], Array.getElem?_eq_getElem stateBound⟩

private theorem step_assigned_against_final
    (module : Module) (states finalStates : Array State) (func : Func)
    (types : Array (Option VTy)) (before final : State) (inst : Inst)
    (statesSize : states.size = module.funcs.size)
    (finalSize : finalStates.size = module.funcs.size)
    (stageShapes : ∀ (fn : FnId) (callee : Func) (effects : State), module.funcs[fn]? = some callee →
      states[fn]? = some effects → effects.Shape callee)
    (growth : before.Extends final)
    (operands : ∀ value ∈ inst.uses, ∃ actual, normalize func (flowAt final.values value) = some actual)
    (calls : ∀ value fn arguments origin, inst = .def value (.call fn arguments origin) →
      ∃ callee, module.funcs[fn]? = some callee ∧ arguments.length = callee.params.length)
    (contents : ∀ value fn arguments origin, inst = .def value (.call fn arguments origin) →
      ∀ callee, module.funcs[fn]? = some callee →
      ∀ index, (callee.roots.contents.find? (·.1 == index)).isSome = true →
      ∀ argument, arguments[index]? = some argument →
        content func final (flowAt final.values argument) ≠ .pending)
    (writeSafety : ∀ (fn : FnId) (callee : Func) (effects : State), module.funcs[fn]? = some callee →
      finalStates[fn]? = some effects → ∀ (index : Nat) (roots : Roots),
        effects.writes[index]? = some (.assigned roots) →
        roots = .pending ∨ ∃ actual, normalize callee roots = some actual)
    (old : ∀ index, Write.AssignedAt before.writes index → Write.ReadyAt final.writes index)
    (calleeReady : ∀ (fn : FnId) (callee : Func) (effects finalEffects : State), module.funcs[fn]? = some callee →
      states[fn]? = some effects → finalStates[fn]? = some finalEffects →
      ∀ index, Write.AssignedAt effects.writes index → Write.ReadyAt finalEffects.writes index)
    (fixed : step module finalStates func types final inst = final)
    (index : Nat) (assigned : Write.AssignedAt (step module states func types before inst).writes index) :
    Write.ReadyAt final.writes index := by
  have finalWrites := congrArg State.writes fixed
  rw [step_writes] at assigned finalWrites
  cases inst with
  | «def» value op =>
    cases op <;> try exact old index assigned
    case call fn arguments origin =>
      obtain ⟨callee, calleeAt, arity⟩ := calls value fn arguments origin rfl
      obtain ⟨effects, effectsAt⟩ := state_at module states statesSize fn callee calleeAt
      obtain ⟨finalEffects, finalEffectsAt⟩ := state_at module finalStates finalSize fn callee calleeAt
      exact call_assigned_against_final module states finalStates func
        before final
        fn arguments callee effects finalEffects calleeAt effectsAt finalEffectsAt
        (stageShapes fn callee effects calleeAt effectsAt) arity growth.values growth.writes.size
        operands (contents value fn arguments origin rfl callee calleeAt)
        (writeSafety fn callee finalEffects calleeAt finalEffectsAt) old
        (calleeReady fn callee effects finalEffects calleeAt effectsAt finalEffectsAt)
        finalWrites index assigned
  | eff effect =>
    cases effect <;> try exact old index assigned
    case store address value origin =>
      by_cases reference : valRefLike types value = true
      · simp only [reference, ite_true] at assigned finalWrites
        obtain ⟨actualAddress, addressNormalized⟩ := operands address (by simp [Inst.uses, Effect.uses])
        obtain ⟨actualValue, valueNormalized⟩ := operands value (by simp [Inst.uses, Effect.uses])
        have beforeSafe : flowAt before.values address ≠ .unknown := by
          intro unknown
          have one := growth.values.values address
          change (flowAt before.values address).Extends (flowAt final.values address) at one
          rw [unknown] at one
          cases result : flowAt final.values address <;>
            simp_all [Roots.Extends, normalize]
        rcases write_assigned_origin func _ _ _ index beforeSafe assigned with prior | fresh
        · exact old index prior
        · obtain ⟨atoms, known, target, bound, slice⟩ := fresh
          obtain ⟨finalAtoms, finalKnown, finalTarget⟩ :=
            (growth.values.values address).known_member
              (normalize_not_unknown addressNormalized) known target
          change index < before.writes.size at bound
          change flowAt final.values address = .known finalAtoms at finalKnown
          have ready := write_known_parameter_ready func
            (touchValues types final (accessOperands (.eff (.store address value origin))))
            finalAtoms (flowAt final.values value) index finalTarget
            (by change index < final.writes.size; simpa [← growth.writes.size] using bound) slice (normalize_nonpending valueNormalized)
          rw [← finalKnown] at ready
          rwa [finalWrites] at ready
      · simp only [reference] at assigned
        exact old index assigned
  | term terminal => exact old index assigned

private theorem scan_assigned {α : Type} (items : List α) (update : State → α → State)
    (growth : ∀ (current : State) (item : α), current.Extends (update current item)) (final : State)
    (advance : ∀ item ∈ items, ∀ current, (update current item).Extends final →
      (∀ index, Write.AssignedAt current.writes index → Write.ReadyAt final.writes index) →
      ∀ index, Write.AssignedAt (update current item).writes index → Write.ReadyAt final.writes index)
    (before : State) (bounded : (items.foldl update before).Extends final)
    (old : ∀ index, Write.AssignedAt before.writes index → Write.ReadyAt final.writes index) :
    ∀ index, Write.AssignedAt (items.foldl update before).writes index → Write.ReadyAt final.writes index := by
  induction items generalizing before with
  | nil => exact old
  | cons item items ih =>
    have oneBound : (update before item).Extends final :=
      (state_foldl_extends items update growth _).trans bounded
    exact ih (fun next member => advance next (List.mem_cons_of_mem _ member))
      (update before item) bounded (advance item (by simp) before oneBound old)

theorem ModuleReachable.assigned_nonpending {module : Module} {types : Array (Array (Option VTy))}
    {finalStates : Array State}
    (reachable : ModuleReachable module types (moduleStart module types) finalStates)
    (stable : moduleRound module types finalStates = finalStates)
    (operands : ∀ (fn : FnId) (func : Func) (final : State), module.funcs[fn]? = some func →
      finalStates[fn]? = some final → ∀ block ∈ func.blocks.toList, ∀ inst ∈ block.insts,
        ∀ value ∈ inst.uses, ∃ actual, normalize func (flowAt final.values value) = some actual)
    (calls : ∀ (fn : FnId) (func : Func), module.funcs[fn]? = some func →
      ∀ block ∈ func.blocks.toList, ∀ value calleeId arguments origin,
        .def value (.call calleeId arguments origin) ∈ block.insts →
        ∃ callee, module.funcs[calleeId]? = some callee ∧ arguments.length = callee.params.length)
    (contents : ∀ (fn : FnId) (func : Func) (final : State), module.funcs[fn]? = some func →
      finalStates[fn]? = some final → ∀ block ∈ func.blocks.toList, ∀ value calleeId arguments origin,
      .def value (.call calleeId arguments origin) ∈ block.insts →
      ∀ callee, module.funcs[calleeId]? = some callee →
      ∀ index, (callee.roots.contents.find? (·.1 == index)).isSome = true →
      ∀ argument, arguments[index]? = some argument →
        content func final (flowAt final.values argument) ≠ .pending)
    (writeSafety : ∀ (fn : FnId) (callee : Func) (effects : State), module.funcs[fn]? = some callee →
      finalStates[fn]? = some effects → ∀ (index : Nat) (roots : Roots),
        effects.writes[index]? = some (.assigned roots) →
        roots = .pending ∨ ∃ actual, normalize callee roots = some actual) :
    ∀ (fn : FnId) (func : Func) (final : State), module.funcs[fn]? = some func →
      finalStates[fn]? = some final → ∀ (index : Nat) (roots : Roots),
        final.writes[index]? = some (.assigned roots) → roots ≠ .pending := by
  have initialSize : (moduleStart module types).size = module.funcs.size := by simp [moduleStart]
  have finalSize := reachable.size initialSize
  have stages : ∀ (stage : Array State),
      ModuleReachable module types (moduleStart module types) stage →
      ArrayExtends State.empty State.Extends stage finalStates →
      ∀ (fn : FnId) (func : Func) (before final : State), module.funcs[fn]? = some func →
        stage[fn]? = some before → finalStates[fn]? = some final →
        ∀ index, Write.AssignedAt before.writes index → Write.ReadyAt final.writes index := by
    intro stage path
    induction path with
    | refl =>
      intro bounded fn func before final funcAt beforeAt finalAt index assigned
      simp only [moduleStart, Array.getElem?_mapIdx, funcAt, Option.map_some, Option.some.injEq] at beforeAt
      subst before
      obtain ⟨roots, written⟩ := assigned
      rw [start_components] at written
      simp only [Array.getElem?_replicate] at written
      split at written <;> cases written
    | @next currentStates path ih =>
      intro bounded fn func after final funcAt afterAt finalAt
      have currentSize := path.size initialSize
      have currentBound := ArrayExtends.trans (relation := State.Extends)
        (fun {_ _ _} left right => left.trans right)
        (moduleRound_extends (types := types) currentSize) bounded
      have priorReady := ih currentBound
      have stageShapes : ∀ (fn : FnId) (callee : Func) (effects : State),
          module.funcs[fn]? = some callee → currentStates[fn]? = some effects → effects.Shape callee := by
        intro fn callee effects calleeAt effectsAt
        have initialAt : (moduleStart module types)[fn]? = some (start callee (types[fn]?.getD #[])) := by
          simp [moduleStart, calleeAt]
        have one := (path.extends initialSize).values fn
        simp only [initialAt, effectsAt, Option.getD_some] at one
        exact one.shape (start_shape callee _)
      obtain ⟨before, beforeAt⟩ := state_at module currentStates currentSize fn func funcAt
      have produced : round module currentStates func (types[fn]?.getD #[]) before = after := by
        simpa only [moduleRound, Array.getElem?_mapIdx, funcAt, beforeAt,
          Option.map_some, Option.getD_some, Option.some.injEq] using afterAt
      have outputBound := bounded.values fn
      simp only [afterAt, finalAt, Option.getD_some] at outputBound
      have finalFixed := moduleRound_fixed_function stable fn func final funcAt finalAt
      have old := priorReady fn func before final funcAt beforeAt finalAt
      rw [← produced] at outputBound ⊢
      simp only [round, ← Array.foldl_toList]
      apply scan_assigned func.blocks.toList
        (fun current block => block.insts.foldl (step module currentStates func (types[fn]?.getD #[])) current)
        (fun current block => state_foldl_extends block.insts _ (step_extends module currentStates func _) current)
        final
      · intro block blockMember currentBlock blockBound blockOld
        apply scan_assigned block.insts (step module currentStates func (types[fn]?.getD #[]))
          (step_extends module currentStates func _) final
        · intro inst instMember currentInst instBound instOld index assigned
          exact step_assigned_against_final module currentStates finalStates func (types[fn]?.getD #[])
            currentInst final inst currentSize finalSize stageShapes
            ((step_extends module currentStates func _ currentInst inst).trans instBound)
            (operands fn func final funcAt finalAt block blockMember inst instMember)
            (fun value calleeId arguments origin same => calls fn func funcAt block blockMember
              value calleeId arguments origin (same ▸ instMember))
            (fun value calleeId arguments origin same => contents fn func final funcAt finalAt
              block blockMember value calleeId arguments origin (same ▸ instMember))
            writeSafety instOld
            (fun fn callee effects finalEffects calleeAt effectsAt finalEffectsAt =>
              priorReady fn callee effects finalEffects calleeAt effectsAt finalEffectsAt)
            (round_fixed_step module finalStates func _ final finalFixed block blockMember inst instMember)
            index assigned
        · exact blockBound
        · exact blockOld
      · simpa only [round, ← Array.foldl_toList] using outputBound
      · exact old
  intro fn func final funcAt finalAt index roots written
  obtain ⟨actual, same, ready⟩ := stages finalStates reachable
    (ArrayExtends.refl _ _ State.Extends.refl _) fn func final final funcAt finalAt finalAt
      index ⟨roots, written⟩
  have equal : actual = roots := Write.assigned.inj (Option.some.inj (same.symm.trans written))
  simpa [equal] using ready

private theorem local_assigned_nonpending {module : Module} {states : Array State}
    {func : Func} {types : Array (Option VTy)} {final : State}
    (reachable : FunctionReachable module states func types (start func types) final)
    (stable : round module states func types final = final)
    (statesSize : states.size = module.funcs.size)
    (shapes : ∀ (fn : FnId) (callee : Func) (effects : State), module.funcs[fn]? = some callee →
      states[fn]? = some effects → effects.Shape callee)
    (operands : ∀ block ∈ func.blocks.toList, ∀ inst ∈ block.insts,
      ∀ value ∈ inst.uses, ∃ actual, normalize func (flowAt final.values value) = some actual)
    (calls : ∀ block ∈ func.blocks.toList, ∀ value calleeId arguments origin,
      .def value (.call calleeId arguments origin) ∈ block.insts →
      ∃ callee, module.funcs[calleeId]? = some callee ∧ arguments.length = callee.params.length)
    (contents : ∀ block ∈ func.blocks.toList, ∀ value calleeId arguments origin,
      .def value (.call calleeId arguments origin) ∈ block.insts →
      ∀ callee, module.funcs[calleeId]? = some callee →
      ∀ index, (callee.roots.contents.find? (·.1 == index)).isSome = true →
      ∀ argument, arguments[index]? = some argument →
        content func final (flowAt final.values argument) ≠ .pending)
    (writeSafety : ∀ (fn : FnId) (callee : Func) (effects : State), module.funcs[fn]? = some callee →
      states[fn]? = some effects → ∀ (index : Nat) (roots : Roots),
        effects.writes[index]? = some (.assigned roots) →
        roots = .pending ∨ ∃ actual, normalize callee roots = some actual)
    (moduleReady : ∀ (fn : FnId) (callee : Func) (effects : State), module.funcs[fn]? = some callee →
      states[fn]? = some effects → ∀ (index : Nat) (roots : Roots),
        effects.writes[index]? = some (.assigned roots) → roots ≠ .pending) :
    ∀ (index : Nat) (roots : Roots), final.writes[index]? = some (.assigned roots) → roots ≠ .pending := by
  have stages : ∀ stage, FunctionReachable module states func types (start func types) stage →
      stage.Extends final → ∀ index, Write.AssignedAt stage.writes index → Write.ReadyAt final.writes index := by
    intro stage path
    induction path with
    | refl =>
      intro bounded index assigned
      obtain ⟨roots, written⟩ := assigned
      rw [start_components] at written
      simp only [Array.getElem?_replicate] at written
      split at written <;> cases written
    | @next current path ih =>
      intro bounded
      have old := ih ((round_extends module states func types current).trans bounded)
      simp only [round, ← Array.foldl_toList]
      apply scan_assigned func.blocks.toList
        (fun current block => block.insts.foldl (step module states func types) current)
        (fun current block => state_foldl_extends block.insts _ (step_extends module states func _) current)
        final
      · intro block blockMember currentBlock blockBound blockOld
        apply scan_assigned block.insts (step module states func types)
          (step_extends module states func _) final
        · intro inst instMember currentInst instBound instOld index assigned
          apply step_assigned_against_final module states states func types currentInst final inst
            statesSize statesSize shapes ((step_extends module states func types currentInst inst).trans instBound)
            (operands block blockMember inst instMember)
            (fun value calleeId arguments origin same => calls block blockMember value calleeId arguments origin
              (same ▸ instMember))
            (fun value calleeId arguments origin same => contents block blockMember value calleeId arguments origin
              (same ▸ instMember)) writeSafety instOld
          · intro fn callee effects finalEffects calleeAt effectsAt finalEffectsAt index assigned
            have same : effects = finalEffects := Option.some.inj (effectsAt.symm.trans finalEffectsAt)
            subst finalEffects
            obtain ⟨roots, written⟩ := assigned
            exact ⟨roots, written, moduleReady fn callee effects calleeAt effectsAt index roots written⟩
          · exact round_fixed_step module states func types final stable block blockMember inst instMember
          · exact assigned
        · exact blockBound
        · exact blockOld
      · simpa only [round, ← Array.foldl_toList] using bounded
      · exact old
  intro index roots written
  obtain ⟨actual, same, ready⟩ := stages final reachable (State.Extends.refl _) index ⟨roots, written⟩
  have equal : actual = roots := Write.assigned.inj (Option.some.inj (same.symm.trans written))
  simpa [equal] using ready

theorem FunctionReachable.assigned_nonpending
    {module : Module} {moduleTypes : Array (Array (Option VTy))} {states : Array State}
    {func : Func} {types : Array (Option VTy)} {final : State}
    (moduleReachable : ModuleReachable module moduleTypes (moduleStart module moduleTypes) states)
    (moduleStable : moduleRound module moduleTypes states = states)
    (moduleOperands : ∀ (fn : FnId) (func : Func) (final : State), module.funcs[fn]? = some func →
      states[fn]? = some final → ∀ block ∈ func.blocks.toList, ∀ inst ∈ block.insts,
        ∀ value ∈ inst.uses, ∃ actual, normalize func (flowAt final.values value) = some actual)
    (moduleCalls : ∀ (fn : FnId) (func : Func), module.funcs[fn]? = some func →
      ∀ block ∈ func.blocks.toList, ∀ value calleeId arguments origin,
      .def value (.call calleeId arguments origin) ∈ block.insts →
        ∃ callee, module.funcs[calleeId]? = some callee ∧ arguments.length = callee.params.length)
    (moduleContents : ∀ (fn : FnId) (func : Func) (final : State), module.funcs[fn]? = some func →
      states[fn]? = some final → ∀ block ∈ func.blocks.toList, ∀ value calleeId arguments origin,
      .def value (.call calleeId arguments origin) ∈ block.insts →
      ∀ callee, module.funcs[calleeId]? = some callee →
      ∀ index, (callee.roots.contents.find? (·.1 == index)).isSome = true →
      ∀ argument, arguments[index]? = some argument →
        content func final (flowAt final.values argument) ≠ .pending)
    (writeSafety : ∀ (fn : FnId) (callee : Func) (effects : State), module.funcs[fn]? = some callee →
      states[fn]? = some effects → ∀ (index : Nat) (roots : Roots),
        effects.writes[index]? = some (.assigned roots) →
        roots = .pending ∨ ∃ actual, normalize callee roots = some actual)
    (reachable : FunctionReachable module states func types (start func types) final)
    (stable : round module states func types final = final)
    (operands : ∀ block ∈ func.blocks.toList, ∀ inst ∈ block.insts,
      ∀ value ∈ inst.uses, ∃ actual, normalize func (flowAt final.values value) = some actual)
    (calls : ∀ block ∈ func.blocks.toList, ∀ value calleeId arguments origin,
      .def value (.call calleeId arguments origin) ∈ block.insts →
      ∃ callee, module.funcs[calleeId]? = some callee ∧ arguments.length = callee.params.length)
    (contents : ∀ block ∈ func.blocks.toList, ∀ value calleeId arguments origin,
      .def value (.call calleeId arguments origin) ∈ block.insts →
      ∀ callee, module.funcs[calleeId]? = some callee →
      ∀ index, (callee.roots.contents.find? (·.1 == index)).isSome = true →
      ∀ argument, arguments[index]? = some argument →
        content func final (flowAt final.values argument) ≠ .pending) :
    ∀ (index : Nat) (roots : Roots), final.writes[index]? = some (.assigned roots) → roots ≠ .pending := by
  have initialSize : (moduleStart module moduleTypes).size = module.funcs.size := by simp [moduleStart]
  apply local_assigned_nonpending reachable stable (moduleReachable.size initialSize)
  · intro fn callee effects calleeAt effectsAt
    have initialAt : (moduleStart module moduleTypes)[fn]? =
        some (start callee (moduleTypes[fn]?.getD #[])) := by simp [moduleStart, calleeAt]
    have one := (moduleReachable.extends initialSize).values fn
    simp only [initialAt, effectsAt, Option.getD_some] at one
    exact one.shape (start_shape callee _)
  · exact operands
  · exact calls
  · exact contents
  · exact writeSafety
  · exact ModuleReachable.assigned_nonpending moduleReachable moduleStable moduleOperands
      moduleCalls moduleContents writeSafety

#print axioms ModuleReachable.assigned_nonpending
#print axioms FunctionReachable.assigned_nonpending


end Goose.GIR.ReplacementContentFlow.Model
