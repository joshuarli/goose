import Goose.GIR.ReplacementContentFlowProofsSliceOrigins

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem SymbolicRootsRefine.normalizableAtoms {func : Func} {roots : Roots} {upper : List RootRef}
    (bounded : SymbolicRootsRefine func roots upper) :
    roots.AtomsWithin (fun atom => (normalizeAtom func atom).isSome = true) := by
  rcases bounded with rfl | ⟨actual,known,_⟩
  · trivial
  · obtain ⟨atoms,rfl⟩ := normalize_known_shape known
    intro atom member
    obtain ⟨mapped,mappedKnown,_⟩ := (normalize_fold_atoms _ atoms [] actual known).2 atom member
    cases atom with
    | «local» slot | global global | param index => rfl
    | contents index =>
        cases row : func.roots.contents.find? (·.1 == index) with
        | none => simp [normalizeAtom,row] at mappedKnown
        | some row => simp [normalizeAtom,row]

theorem Roots.AtomsWithin.normalize {func : Func} {roots : Roots}
    (bounded : roots.AtomsWithin (fun atom => (normalizeAtom func atom).isSome = true))
    (ready : roots ≠ .pending) : ∃ actual, normalize func roots = some actual := by
  cases roots with
  | pending => exact False.elim (ready rfl)
  | unknown => exact False.elim bounded
  | known atoms =>
      obtain ⟨actual,known,_⟩ := normalize_fold_within func atoms
        (atoms.flatMap fun atom => (normalizeAtom func atom).getD []) (by
          intro atom member
          obtain ⟨mapped,mappedKnown⟩ := Option.isSome_iff_exists.mp (bounded atom member)
          refine ⟨mapped,mappedKnown,?_⟩
          intro root included
          exact List.mem_flatMap.mpr ⟨atom,member,by simpa only [mappedKnown,Option.getD_some] using included⟩)
        [] (by simp)
      exact ⟨actual,known⟩

theorem touchValues_normalizableAtoms {func : Func} {vt : Array (Option VTy)} {state : State}
    {values : List ValueId}
    (before : state.touched.AtomsWithin (fun atom => (normalizeAtom func atom).isSome = true))
    (sources : ∀ value ∈ values, valRefLike vt value = true →
      (flowAt state.values value).AtomsWithin (fun atom => (normalizeAtom func atom).isSome = true)) :
    (touchValues vt state values).touched.AtomsWithin (fun atom => (normalizeAtom func atom).isSome = true) := by
  unfold touchValues
  apply List.foldlRecOn (motive := fun roots : Roots =>
    roots.AtomsWithin (fun atom => (normalizeAtom func atom).isSome = true)) values _ before
  intro current valid value member
  split
  · rename_i reference
    exact valid.join (sources value member reference)
  · exact valid

theorem HolderRoots.write_touched {func : Func} {state : State} {address roots : Roots}
    {payload : Ty} {upper : List RootRef} (physical : HolderRoots func payload upper address) :
    (write func state address roots).touched = state.touched := by
  cases address with
  | pending => rfl
  | unknown => exact False.elim physical
  | known atoms =>
      simp only [write]
      apply List.foldlRecOn (motive := fun current : State => current.touched = state.touched) atoms _ rfl
      intro current preserved atom member
      cases physical atom member with
      | slot => exact preserved
      | parameter index mu row target =>
          dsimp only
          split <;> exact preserved

theorem publicTouches_normalizableAtoms {func : Func} {roots : Roots}
    (bounded : roots.AtomsWithin (fun atom => (normalizeAtom func atom).isSome = true)) :
    (publicTouches roots).AtomsWithin (fun atom =>
      (normalizeAtom func atom).isSome = true ∧ ∀ slot, atom ≠ .local slot) := by
  cases roots with
  | pending => trivial
  | unknown => exact False.elim bounded
  | known atoms =>
      apply Roots.AtomsWithin.bind_known
      intro atom member
      cases atom with
      | «local» slot => simp [Roots.AtomsWithin]
      | global global | param index | contents index =>
          all_goals intro actual singleton
          all_goals simp only [List.mem_singleton] at singleton
          all_goals subst actual
          all_goals exact ⟨bounded _ member,by intros; simp⟩

theorem substitute_normalizableAtoms {module : Module} {callee func : Func} {state : State}
    {args : List ValueId} {roots : Roots}
    (bounded : roots.AtomsWithin (fun atom =>
      (normalizeAtom callee atom).isSome = true ∧ ∀ slot, atom ≠ .local slot))
    (supported : roots.Supported (atomUniverse module callee))
    (arguments : ∀ index, index < callee.params.length →
      ∃ value, args[index]? = some value ∧
        (flowAt state.values value).AtomsWithin (fun atom => (normalizeAtom func atom).isSome = true))
    (contents : ∀ index row, index < callee.params.length →
      callee.roots.contents.find? (·.1 == index) = some (index,row) →
      ∃ value, args[index]? = some value ∧
        (content func state (flowAt state.values value)).AtomsWithin (fun atom => (normalizeAtom func atom).isSome = true)) :
    (substitute func state args roots).AtomsWithin (fun atom => (normalizeAtom func atom).isSome = true) := by
  cases roots with
  | pending => trivial
  | unknown => exact False.elim bounded
  | known atoms =>
      apply Roots.AtomsWithin.bind_known
      intro atom member
      have valid := bounded atom member
      cases atom with
      | «local» slot => exact False.elim (valid.2 slot rfl)
      | global global => simp [Roots.AtomsWithin,normalizeAtom]
      | param index =>
          obtain ⟨value,argument,ready⟩ := arguments index
            ((atomUniverse_param module callee index).mp (supported.2 member))
          simpa only [argument,Option.map_some,Option.getD_some] using ready
      | contents index =>
          cases annotation : callee.roots.contents.find? (·.1 == index) with
          | none => simp [normalizeAtom,annotation] at valid
          | some row =>
              have selection := Array.find?_some annotation
              have identity : row.1 = index := by simpa only [beq_iff_eq] using selection
              rcases row with ⟨selected,ceiling⟩
              change selected = index at identity
              subst selected
              obtain ⟨value,argument,ready⟩ := contents index ceiling
                ((atomUniverse_contents module callee index).mp (supported.2 member)) annotation
              simpa only [argument,Option.map_some,Option.getD_some] using ready

private theorem slice_forIn_preserves {α : Type} (values : List α) (predicate : State → Prop)
    (update : α → State → Id (ForInStep State))
    (preserved : ∀ value ∈ values, ∀ state, predicate state → match (update value state).run with
      | .done after | .yield after => predicate after)
    (state : State) (initial : predicate state) : predicate (forIn values state update).run := by
  induction values generalizing state with
  | nil => exact initial
  | cons value values ih =>
      have one := preserved value (by simp) state initial
      cases equation : (update value state).run with
      | done after => simpa [List.forIn_cons,equation] using one
      | yield after =>
          have next : predicate after := by simpa [equation] using one
          simpa [List.forIn_cons,equation] using ih
            (fun value member => preserved value (List.mem_cons_of_mem _ member)) after next

theorem callState_touched_of_holders {module : Module} {states : Array State} {func callee : Func}
    {state effects : State} {fn : FnId} {args : List ValueId}
    (calleeAt : module.funcs[fn]? = some callee) (effectsAt : states[fn]? = some effects)
    (holders : ∀ type index, (type,index) ∈ callee.params.zipIdx → type.isRefSlice = true →
      ∃ value payload upper, args[index]? = some value ∧
        HolderRoots func payload upper (flowAt state.values value)) :
    (callState module states func state fn args).2.touched =
      state.touched.join (substitute func state args (publicTouches effects.touched)) := by
  simp only [callState,calleeAt,effectsAt,Id.run_bind,Id.run_pure]
  apply slice_forIn_preserves _ (fun current => current.touched =
    state.touched.join (substitute func state args (publicTouches effects.touched))) _ _ _ rfl
  intro parameter member current preserved
  by_cases reference : parameter.1.isRefSlice = true
  · simp only [reference,ite_true]
    cases assigned : effects.writes[parameter.2]?.getD (.assigned .unknown) with
    | unchanged => exact preserved
    | assigned roots =>
        obtain ⟨value,payload,upper,argument,physical⟩ := holders parameter.1 parameter.2 member reference
        simpa [argument] using
          (physical.write_touched (state := current) (roots := substitute func state args roots)).trans preserved
  · simpa [reference] using preserved

theorem State.CanonicalWithin.callTouched_normalizableAtoms {module : Module} {states : Array State}
    {func : Func} {vt : Array (Option VTy)} {provenance : Prov} {results : Array (List RootRef)}
    {state effects : State} {fn value : ValueId} {args : List ValueId} {origin : Option OriginId}
    (before : state.CanonicalWithin func vt provenance)
    (facts : FunctionCanonicalFacts module func vt provenance results)
    (site : CallSiteFacts module func vt provenance fn args)
    (calleeFacts : FunctionRootFacts site.callee)
    (effectsAt : states[fn]? = some effects)
    (supported : effects.Supported (atomUniverse module site.callee))
    (touched : state.touched.AtomsWithin (fun atom => (normalizeAtom func atom).isSome = true))
    (calleeTouched : effects.touched.AtomsWithin (fun atom => (normalizeAtom site.callee atom).isSome = true))
    {block : Block} (blockMember : block ∈ func.blocks.toList)
    (called : Inst.def value (.call fn args origin) ∈ block.insts) :
    (Model.callState module states func state fn args).2.touched.AtomsWithin
      (fun atom => (normalizeAtom func atom).isSome = true) := by
  have contentArguments := before.callContentArguments site.calleeAt facts.roots.closed facts.roots.parameters
    calleeFacts.contentTypes site.references site.observed facts.admitted blockMember called
  have substituted : (substitute func state args (publicTouches effects.touched)).AtomsWithin
      (fun atom => (normalizeAtom func atom).isSome = true) := by
    apply substitute_normalizableAtoms (publicTouches_normalizableAtoms calleeTouched)
      (publicTouches_supported supported.touched)
    · intro index bounded
      obtain ⟨argument,argumentAt,argumentBound⟩ := site.arguments index bounded
      refine ⟨argument,argumentAt,?_⟩
      exact (before.values argument (by rw [before.shape.values]; exact argumentBound)).normalizableAtoms
    · intro index row bounded annotation
      obtain ⟨argument,argumentAt,contentBound⟩ := contentArguments index row bounded annotation
      exact ⟨argument,argumentAt,contentBound.normalizableAtoms⟩
  rw [callState_touched_of_holders site.calleeAt effectsAt]
  · exact touched.join substituted
  · intro type index member reference
    have formal := List.mem_zipIdx_iff_getElem?.mp member
    obtain ⟨outer,inner,element,same,flat⟩ := isRefSlice_shape reference
    subst type
    obtain ⟨argument,actualMutability,argumentAt,canonical,bounded⟩ := site.references index outer _ formal
    refine ⟨argument,.slice inner element,rootsAt provenance.vals argument,argumentAt,?_⟩
    exact before.holderValues argument (by rw [before.shape.values]; exact bounded)
      actualMutability (.slice inner element) canonical rfl

#print axioms SymbolicRootsRefine.normalizableAtoms
#print axioms Roots.AtomsWithin.normalize
#print axioms touchValues_normalizableAtoms
#print axioms HolderRoots.write_touched

end Goose.GIR.ReplacementContentFlow.Model
