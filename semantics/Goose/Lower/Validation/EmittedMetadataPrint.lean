import Goose.Lower.Validation.EmittedMetadataTransfers

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

def EmittedPrintValue (state : LS) (value : ValueId) : Prop :=
  (∃ integer, state.vals[value]? = some (some (.data (.int integer)))) ∨
    state.vals[value]? = some (some (.data .bool))

theorem EmittedPrintValue.retained {before after : LS} {value : ValueId}
    (typed : EmittedPrintValue before value) (preserved : TypePrefix before after) : EmittedPrintValue after value := by
  rcases typed with ⟨integer, row⟩ | row
  · exact Or.inl ⟨integer, preserved _ _ row⟩
  · exact Or.inr (preserved _ _ row)

theorem metadata_dead_printArgs : ∀ args, DeadRun (lowerPrintArgs args)
  | [] => .pure []
  | .text text :: rest => DeadRun.bind (metadata_dead_printArgs rest) fun parts => .pure (.text text :: parts)
  | .expr expr :: rest => DeadRun.bind (dead_lowerExpr expr) fun value =>
      DeadRun.bind (metadata_dead_printArgs rest) fun parts => .pure (.val value :: parts)

theorem metadata_printArguments {le : LEnv} (args : List PrintArg)
    (children : ∀ expr, PrintArg.expr expr ∈ args → ∀ before value after,
      GeneratedBuilderState before → lowerExpr expr le before = (value, after) → EmittedMetadata le before →
      EmittedMetadata le after ∧ (after.cur.isSome = true → EmittedPrintValue after value))
    {before after : LS} {parts : List PrintPart} (generated : GeneratedBuilderState before)
    (run : lowerPrintArgs args le before = (parts, after)) (checked : EmittedMetadata le before) :
    EmittedMetadata le after ∧ (after.cur.isSome = true →
      ∀ value, PrintPart.val value ∈ parts → EmittedPrintValue after value) := by
  induction args generalizing before parts after with
  | nil =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
    exact ⟨checked, by intro live value member; cases member⟩
  | cons arg rest inductionHypothesis =>
    cases arg with
    | text text =>
      obtain ⟨tail, tailState, tailRun, finalRun⟩ := bind_eq.mp run
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj finalRun
      have tailMetadata := inductionHypothesis (fun expr member => children expr (by simp [member])) generated tailRun checked
      refine ⟨tailMetadata.1, ?_⟩
      intro live value member
      have prior : PrintPart.val value ∈ tail := by simpa using member
      exact tailMetadata.2 live value prior
    | expr expr =>
      obtain ⟨value, valueState, valueRun, tail, tailState, tailRun, finalRun⟩ := by
        simpa only [lowerPrintArgs, bind_eq] using run
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj finalRun
      have valueMetadata := children expr (by simp) before value valueState generated valueRun checked
      have valueGenerated := generated.lowerExpr expr valueRun
      have tailMetadata := inductionHypothesis (fun expr member => children expr (by simp [member])) valueGenerated tailRun valueMetadata.1
      refine ⟨tailMetadata.1, ?_⟩
      intro live candidate member
      rcases List.mem_cons.mp member with same | prior
      · have same := PrintPart.val.inj same
        subst candidate
        have inputLive := (metadata_dead_printArgs rest).live_before tailRun live
        exact (valueMetadata.2 inputLive).retained (types_lowerPrintArgs rest le valueState tail tailState tailRun)
      · exact tailMetadata.2 live candidate prior

theorem metadata_source_print {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (args : List PrintArg) (origin : OriginId)
    (children : ∀ expr, PrintArg.expr expr ∈ args → EmittedMetadataSourceExpression env results expr) :
    EmittedMetadataSourceStatement env results scope (.print args origin) := by
  intro agreement output start finish source loop before result after generated loopBounds loopTypes run checked
  have printSource := (tyStmt_print_children source).1
  change (do let parts ← lowerPrintArgs args; emitEffect (.print parts (some origin)))
    (lowerEnv env.mod env.vars results) before = (result, after) at run
  obtain ⟨parts, partsState, partsRun, emitted⟩ := bind_eq.mp run
  have partsMetadata := metadata_printArguments args (fun expr member before value after generated run checked => by
    obtain ⟨type, childStart, childFinish, childSource, shape⟩ := tyPrintArgs_expr_children printSource member
    refine ⟨children expr member agreement childSource before value after generated trivial trivial run checked, ?_⟩
    intro live
    have row := lowerExpr_generated_typed expr childSource run live generated
    rcases shape with rfl | ⟨integer, rfl⟩
    · exact Or.inr row
    · exact Or.inl ⟨integer, row⟩) generated partsRun checked
  have finished := partsMetadata.1.emitEffect (.print parts (some origin)) (fun live => .print (partsMetadata.2 live))
  simpa only [emitted] using finished

end Goose.Lower.Validation
