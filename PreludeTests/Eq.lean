import Prelude
import Prelude.Eq

set_option autoImplicit false

open Prelude
open scoped Prelude

namespace PreludeTests.Eq

universe u

def identityFromEq {A : Type u} {x y : A} (p : x = y) : x ≡ y := Identity.ofEq p

def unique {A : Type u} {x y : A} (p q : x ≡ y) : p ≡ q := Identity.unique p q

-- A Lean equality decision supplies a decision of identity.
abbrev stringDecision : DecEq String := inferInstance

#guard (decideEq "a" "a").isYes
#guard !(decideEq "a" "b").isYes

-- The reverse adapter works with a solely Type-valued dictionary.
inductive Token where | only

instance : DecEq Token where
  decEq a b := match a, b with | .only, .only => .yes .refl

def tokenDecision (a b : Token) : Decidable (a = b) :=
  letI := DecEq.toDecidableEq (α := Token)
  inferInstance

end PreludeTests.Eq
