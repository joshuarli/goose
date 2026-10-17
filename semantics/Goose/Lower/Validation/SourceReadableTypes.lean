import Goose.Core.Sound.Lemmas

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound

theorem source_storable_refLike_readable {type : Ty}
    (stored : type.storable = true) (reference : type.isRefLike = true) :
    type.readable = true := by
  cases type <;> simp_all [Ty.storable, Ty.isRefLike, Ty.readable]

theorem source_readable_storable {type : Ty} (readable : type.readable = true) :
    type.storable = true := by
  cases type <;> simp_all [Ty.storable, Ty.readable, Ty.flat]

theorem source_passable_readable_eq {actual expected : Ty}
    (passable : actual.passableTo expected = true) : actual.readable = expected.readable := by
  cases actual <;> cases expected <;>
    simp_all [Ty.passableTo, Ty.readable, Ty.refTarget, Ty.flat, Bool.and_eq_true, beq_iff_eq]

theorem source_passable_refLike_eq {actual expected : Ty}
    (passable : actual.passableTo expected = true) : actual.isRefLike = expected.isRefLike := by
  cases actual <;> cases expected <;>
    simp_all [Ty.passableTo, Ty.isRefLike, Bool.and_eq_true, beq_iff_eq]

theorem source_passable_readable {actual expected : Ty}
    (passable : actual.passableTo expected = true) (readable : actual.readable = true) :
    expected.readable = true := by
  rw [← source_passable_readable_eq passable]
  exact readable

#print axioms source_passable_readable

end Goose.Lower.Validation
