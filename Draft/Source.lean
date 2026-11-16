import Draft.Diagram

/-! Source diagrams of the fragment with fixed occurrences.

A diagram of the fragment is one sequence of steps and one exit. The output boundary of each
step has one case: the type of its cases has a center, and each case is identical to the
center. The evidence is a function of the diagram, by a recursion on it. The action of a port
map keeps the fragment. The operations of a diagram of the fragment are a list, in the order of
its steps. -/

set_option autoImplicit false
set_option genInjectivity false

open Prelude Container

namespace Draft

variable {Ty : Type} {S : Signature Ty}

/-- The evidence that a diagram is one sequence of steps and one exit. A step has the center
of the cases of its output boundary, the identity of each case with the center, and the
evidence of its rest at the center. -/
def Diagram.Straight : {Γ : List Ty} → {Qs : Exits Ty} → Diagram S Γ Qs → Type
  | _, _, .exit _ => Unit
  | _, _, .step call rest =>
      (center : (S.output call.1).Case) ×
        (((c : (S.output call.1).Case) → center ≡ c) × Diagram.Straight (rest center))
  | _, _, .seq _ _ => Empty

/-- The action of a port map keeps the fragment. -/
def Diagram.Straight.rename : {Γ Δ : List Ty} → {Qs : Exits Ty} → (ρ : PortMap Γ Δ) →
    (d : Diagram S Δ Qs) → d.Straight → (d.rename ρ).Straight
  | _, _, _, _, .exit _, _ => ()
  | _, _, _, ρ, .step _ rest, h => ⟨h.1, h.2.1, rename (ρ.lift h.1.1) (rest h.1) h.2.2⟩
  | _, _, _, _, .seq _ _, h => nomatch h

/-- The operations of a diagram of the fragment, in the order of its steps. -/
def Diagram.ops : {Γ : List Ty} → {Qs : Exits Ty} → (d : Diagram S Γ Qs) → d.Straight →
    List S.Op
  | _, _, .exit _, _ => []
  | _, _, .step call rest, h => call.1 :: Diagram.ops (rest h.1) h.2.2
  | _, _, .seq _ _, _ => []

end Draft
