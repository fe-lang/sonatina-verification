import Draft.Diagram

/-! The interface of a diagram.

A diagram is an implementation of its own interface by calls of the interface of its signature.
The interface of a diagram has one operation: a shape is the values of the context, and a
position is an exit with its values. With a number of unrollings of each loop and a computation
at the limit, the function meaning of a diagram is that implementation.

A derivation in a rule set that holds after the substitution of a lowering gives a map of
verified implementations of one specification. The agreement that the derivation gives is its
plain part, and the verification moves along it. -/

set_option autoImplicit false
set_option genInjectivity false

universe w z p w'

open Prelude Container

namespace Draft

variable {Ty : Type} {S : Signature Ty} {X : Ty → Type}

/-- The interface of a diagram: a shape is the values of its context, and a position is an
exit with its values. -/
def Diagram.interface (X : Ty → Type) (Γ : List Ty) (Qs : Exits Ty) : Container.{0, 0} :=
  ⟨All X Γ, fun _ => Qs.At X⟩

/-- A diagram is an implementation of its interface by calls of the interface of its
signature. -/
def Diagram.impl {Γ : List Ty} {Qs : Exits Ty} (stop : Free (S.interface X) (Qs.At X)) (n : Nat)
    (d : Diagram S Γ Qs) : Impl (Diagram.interface X Γ Qs) (S.interface X) :=
  fun env => d.meaning stop n env

/-- A derivation in a rule set that holds after the substitution of a lowering gives a map of
verified implementations of one specification. The agreement that the derivation gives is its
plain part, and the lift moves along it. -/
def Diagram.Derivation.lift {D : Container.{0, 0}} {lower : Impl (S.interface X) D}
    {R : Rules S} {Γ : List Ty} {Qs : Exits Ty}
    (ok : R.Sound (Free.Congruence.subst (α := Qs.At X) lower))
    {d e : Diagram S Γ Qs} (h : Diagram.Derivation R d e)
    {q : DepPoly.{0, 0, w', p} (Diagram.interface X Γ Qs)} {t : DepPoly.{0, 0, w, z} D}
    (stop : Free (S.interface X) (Qs.At X)) (n : Nat)
    (ff : ImplDep q t ((d.impl stop n).trans lower)) :
    ImplDep q t ((e.impl stop n).trans lower) :=
  ImplDep.reindex (fun env => Diagram.Derivation.sound stop n ok h env .pure) ff

end Draft
