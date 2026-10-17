import Goose.Lower.Validation.ExpressionTypingAggregateOps
import Goose.Lower.Validation.ValueTypes

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

inductive EmittedEffectTyped (le : LEnv) (state : LS) : Effect → Prop where
  | slotInit {slot value origin descriptor}
      (slotAt : le.slots[slot]? = some descriptor)
      (valueAt : state.vals[value]? = some (some (.data descriptor.ty))) :
      EmittedEffectTyped le state (.slotInit slot value origin)
  | store {owner value origin mu type}
      (ownerAt : state.vals[owner]? = some (some (.data (.ref mu type))))
      (valueAt : state.vals[value]? = some (some (.data type))) :
      EmittedEffectTyped le state (.store owner value origin)
  | append {owner value origin mu type viewMu element}
      (ownerAt : state.vals[owner]? = some (some (.data (.ref mu type))))
      (ownerType : type = .grow element ∨ type = .growshrink element ∨ ∃ capacity, type = .limited element capacity)
      (valueAt : state.vals[value]? = some (some (.view viewMu element))) :
      EmittedEffectTyped le state (.append owner value origin)
  | popN {owner count origin mu type element integer}
      (ownerAt : state.vals[owner]? = some (some (.data (.ref mu type))))
      (ownerType : type.ownerElem? = some element)
      (countAt : state.vals[count]? = some (some (.data (.int integer)))) :
      EmittedEffectTyped le state (.popN owner count origin)
  | resize {owner size fill origin mu type element integer}
      (ownerAt : state.vals[owner]? = some (some (.data (.ref mu type))))
      (ownerType : type.ownerElem? = some element)
      (sizeAt : state.vals[size]? = some (some (.data (.int integer))))
      (fillAt : ∀ value, fill = some value → state.vals[value]? = some (some (.data element))) :
      EmittedEffectTyped le state (.resize owner size fill origin)
  | clear {owner origin mu type element}
      (ownerAt : state.vals[owner]? = some (some (.data (.ref mu type))))
      (ownerType : type.ownerElem? = some element) : EmittedEffectTyped le state (.clear owner origin)
  | replace {owner value origin mu type}
      (ownerAt : state.vals[owner]? = some (some (.data (.ref mu type))))
      (ownerType : (∃ element, type = .grow element) ∨ ∃ element, type = .growshrink element)
      (valueAt : state.vals[value]? = some (some (.data type))) :
      EmittedEffectTyped le state (.replace owner value origin)
  | print {parts origin}
      (values : ∀ value, PrintPart.val value ∈ parts →
        (∃ integer, state.vals[value]? = some (some (.data (.int integer)))) ∨
          state.vals[value]? = some (some (.data .bool))) :
      EmittedEffectTyped le state (.print parts origin)
  | enter (scope : ScopeId) : EmittedEffectTyped le state (.enter scope)
  | leave (scope : ScopeId) : EmittedEffectTyped le state (.leave scope)

inductive EmittedTermTyped (results : List Ty) (state : LS) : Term → Prop where
  | condbr {condition yes yesArgs no noArgs}
      (conditionAt : state.vals[condition]? = some (some (.data .bool))) :
      EmittedTermTyped results state (.condbr condition yes yesArgs no noArgs)
  | ret {values origin} (typed : TypedValues state results values) :
      EmittedTermTyped results state (.ret values origin)
  | exit {value origin integer} (valueAt : state.vals[value]? = some (some (.data (.int integer)))) :
      EmittedTermTyped results state (.exit value origin)
  | br (target : BlockId) (args : List ValueId) : EmittedTermTyped results state (.br target args)
  | abort (kind : AbortKind) (origin : Option OriginId) : EmittedTermTyped results state (.abort kind origin)
  | unreachable : EmittedTermTyped results state .unreachable

theorem EmittedEffectTyped.retained {le : LEnv} {before after : LS} {effect : Effect}
    (typed : EmittedEffectTyped le before effect) (preserved : TypePrefix before after) :
    EmittedEffectTyped le after effect := by
  cases typed with
  | slotInit slotAt valueAt => exact .slotInit slotAt (preserved _ _ valueAt)
  | store ownerAt valueAt => exact .store (preserved _ _ ownerAt) (preserved _ _ valueAt)
  | append ownerAt ownerType valueAt => exact .append (preserved _ _ ownerAt) ownerType (preserved _ _ valueAt)
  | popN ownerAt ownerType countAt => exact .popN (preserved _ _ ownerAt) ownerType (preserved _ _ countAt)
  | resize ownerAt ownerType sizeAt fillAt =>
    exact .resize (preserved _ _ ownerAt) ownerType (preserved _ _ sizeAt) (fun value same => preserved _ _ (fillAt value same))
  | clear ownerAt ownerType => exact .clear (preserved _ _ ownerAt) ownerType
  | replace ownerAt ownerType valueAt => exact .replace (preserved _ _ ownerAt) ownerType (preserved _ _ valueAt)
  | print values =>
    apply EmittedEffectTyped.print
    intro value member
    rcases values value member with ⟨integer, row⟩ | row
    · exact Or.inl ⟨integer, preserved _ _ row⟩
    · exact Or.inr (preserved _ _ row)
  | enter scope => exact .enter scope
  | leave scope => exact .leave scope

theorem TypedValues.metadata_retained {before after : LS} {types : List Ty} {values : List ValueId}
    (typed : TypedValues before types values) (preserved : TypePrefix before after) :
    TypedValues after types values := by
  induction typed with
  | nil => exact .nil
  | cons row _ tail => exact .cons (preserved _ _ row) tail

theorem EmittedTermTyped.retained {results : List Ty} {before after : LS} {term : Term}
    (typed : EmittedTermTyped results before term) (preserved : TypePrefix before after) :
    EmittedTermTyped results after term := by
  cases typed with
  | condbr row => exact .condbr (preserved _ _ row)
  | ret values => exact .ret (values.metadata_retained preserved)
  | exit row => exact .exit (preserved _ _ row)
  | br target args => exact .br target args
  | abort kind origin => exact .abort kind origin
  | unreachable => exact .unreachable

end Goose.Lower.Validation
