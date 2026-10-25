import Goose.GIR.ReplacementContentFlowProofsCanonicalFacts

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem State.CanonicalWithin.ordinaryEffect {module : Module} {states : Array State}
    {func : Func} {vt : Array (Option VTy)} {provenance : Prov} {state : State} {effect : Effect}
    (before : state.CanonicalWithin func vt provenance)
    (ordinary : ∀ slot value origin, effect ≠ .slotInit slot value origin)
    (nonstore : ∀ address value origin, effect ≠ .store address value origin) :
    (step module states func vt state (.eff effect)).CanonicalWithin func vt provenance := by
  cases effect with
  | slotInit slot value origin => exact False.elim (ordinary slot value origin rfl)
  | store address value origin => exact False.elim (nonstore address value origin rfl)
  | _ => exact before.touchValues _

theorem State.CanonicalWithin.ordinaryTerminal {module : Module} {states : Array State}
    {func : Func} {vt : Array (Option VTy)} {provenance : Prov} {state : State} {term : Term}
    (before : state.CanonicalWithin func vt provenance)
    (nonbranch : ∀ target args, term ≠ .br target args)
    (nonconditional : ∀ condition thenTarget thenArgs elseTarget elseArgs,
      term ≠ .condbr condition thenTarget thenArgs elseTarget elseArgs)
    (nonreturned : ∀ value origin, term ≠ .ret [value] origin) :
    (step module states func vt state (.term term)).CanonicalWithin func vt provenance := by
  cases term with
  | br target args => exact False.elim (nonbranch target args rfl)
  | condbr condition thenTarget thenArgs elseTarget elseArgs =>
      exact False.elim (nonconditional condition thenTarget thenArgs elseTarget elseArgs rfl)
  | ret values origin =>
      cases values with
      | nil => exact before.touchValues _
      | cons value values =>
          cases values with
          | nil => exact False.elim (nonreturned value origin rfl)
          | cons value values => exact before.touchValues _
  | _ => exact before.touchValues _

theorem FunctionCanonicalFacts.start {module : Module} {func : Func} {vt : Array (Option VTy)}
    {provenance : Prov} {results : Array (List RootRef)}
    (facts : FunctionCanonicalFacts module func vt provenance results) :
    (Model.start func vt).CanonicalWithin func vt provenance :=
  start_canonicalWithin _ _ _ facts.roots.unique facts.parameters facts.seeds

theorem State.CanonicalWithin.step_closed {module : Module} {states : Array State}
    {types : Array (Array (Option VTy))} {provenances : Array Prov}
    {func : Func} {vt : Array (Option VTy)} {provenance : Prov} {results : Array (List RootRef)}
    {state : State} {block : Block} {inst : Inst}
    (before : state.CanonicalWithin func vt provenance)
    (facts : FunctionCanonicalFacts module func vt provenance results)
    (moduleFacts : ModuleCanonicalFacts module types provenances results)
    (inputs : ModuleCanonicalWithin module types provenances states)
    (supported : ModuleSupported module states)
    (blockMember : block ∈ func.blocks.toList) (member : inst ∈ block.insts) :
    (step module states func vt state inst).CanonicalWithin func vt provenance := by
  have typed := facts.typing block blockMember inst member
  have uses := facts.uses block blockMember inst member
  have quiet := facts.quiet block blockMember inst member
  have valueBound : ∀ value, value ∈ inst.uses → value < state.values.size := by
    intro value valueMember
    rw [before.shape.values]
    exact uses value valueMember
  cases typed with
  | definition value op type typed canonical =>
      have bound : value < provenance.vals.size := by
        rw [facts.valuesSize]
        exact facts.definitions block blockMember value op member
      by_cases called : ∃ fn args origin, op = .call fn args origin
      · obtain ⟨fn,args,origin,rfl⟩ := called
        obtain ⟨site⟩ := facts.calls block blockMember value fn args origin member
        obtain ⟨effects,effectsAt,calleeBounded⟩ := inputs.2 fn site.callee site.calleeAt
        have calleeFacts := moduleFacts.functions fn site.callee site.calleeAt
        have calleeSupported := supported fn site.callee effects site.calleeAt effectsAt
        rcases facts.callResults block blockMember value fn args origin member site.callee site.calleeAt with
          ⟨empty,canonicalUnit⟩ | ⟨result,resultType,canonicalResult⟩
        · let exposed := state
          have initial : exposed.CanonicalWithin func vt provenance := before
          have mutated := initial.callState_closed site.calleeAt effectsAt calleeBounded calleeSupported
            calleeFacts.roots.unique facts.roots.closed facts.roots.parameters calleeFacts.roots.contentExternal
            site.contracts calleeFacts.roots.contentTypes site.arguments site.references site.observed
            facts.admitted blockMember member
          have assigned : ({ (ReplacementContentFlow.Model.callState module states func exposed fn args).2 with
              values := addFlow (ReplacementContentFlow.Model.callState module states func exposed fn args).2.values value (.known []) } : State).CanonicalWithin
              func vt provenance := by
            apply mutated.addValue (.known_empty _ _)
            · intro mutability payload type reference
              simp [HolderRoots,Roots.AtomsWithin]
            · intro mutability payload type owner
              simp [OwnerOrigins,Roots.AtomsWithin]
          have scalar : valRefLike vt value = false := by simp [valRefLike,canonicalUnit,VTy.refLike,Ty.isRefLike]
          simpa only [step,Id.run_pure,scalar,Bool.false_eq_true,ite_false,exposed] using assigned.touchValues
            (interiorLoadedResults vt (.def value (.call fn args origin)))
        · exact before.call site.calleeAt effectsAt calleeBounded calleeSupported calleeFacts.roots.unique
            facts.roots.closed facts.roots.parameters calleeFacts.roots.contentExternal calleeFacts.roots.resultExternal
            site.contracts calleeFacts.roots.contentTypes site.arguments site.references site.observed
            resultType canonicalResult (calleeFacts.roots.resultNotHolder result (by simp [resultType]))
            (fun reference => moduleFacts.resultFloors fn site.callee site.calleeAt
              (by simp [resultType,reference])) bound quiet facts.admitted blockMember member
      · have classified := DefinitionTyping.of_resultTy (env := {module.tyEnv func with vals := vt}) facts.valuesShape facts.globalStorage facts.fields op typed
        apply before.noncallDefinition classified canonical rfl rfl
          (fun fn args origin same => called ⟨fn,args,origin,same⟩) facts.roots.unique facts.roots.parameters
          uses bound quiet
        intro source identical reference index target formal
        subst op
        apply facts.loadObserved block blockMember value source member
          (by simp [valRefLike,canonical,reference]) index target formal
  | slotInit slot value origin storage row canonical =>
      exact before.slotInit row canonical (valueBound value (by simp [Inst.uses,Effect.uses])) facts.slotsSize quiet
  | store address value origin mutability payload addressType valueType =>
      exact before.store facts.roots.unique facts.roots.closed facts.roots.parameters valueType addressType
        (valueBound value (by simp [Inst.uses,Effect.uses]))
        (valueBound address (by simp [Inst.uses,Effect.uses])) facts.slotsSize quiet facts.admitted blockMember member
  | branch target args targetBlock targetAt types bounds =>
      exact before.br_closed targetAt types (by simpa [facts.valuesSize] using bounds) quiet
  | conditional condition thenTarget elseTarget thenArgs elseArgs thenBlock elseBlock thenAt elseAt
      thenTypes elseTypes thenBounds elseBounds =>
      exact before.condbr_closed thenAt elseAt thenTypes elseTypes
        (by simpa [facts.valuesSize] using thenBounds) (by simpa [facts.valuesSize] using elseBounds) quiet
  | returned value origin type result canonical =>
      exact before.ret result canonical (valueBound value (by simp [Inst.uses,Term.uses]))
        facts.admitted blockMember member
  | effect effect ordinary nonstore => exact before.ordinaryEffect ordinary nonstore
  | terminal term nonbranch nonconditional nonreturned =>
      exact before.ordinaryTerminal nonbranch nonconditional nonreturned

#print axioms State.CanonicalWithin.step_closed

end Goose.GIR.ReplacementContentFlow.Model
