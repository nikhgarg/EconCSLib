import Mathlib.Algebra.Order.Group.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Max

variable {ValueType : Type*} [LinearOrderedAddCommGroup ValueType]

def isComp [DecidableRel ((· ≤ ·) : ValueType → ValueType → Prop)] (x y : ValueType) : Bool := if x ≤ y then true else false
