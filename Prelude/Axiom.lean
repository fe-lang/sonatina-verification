import Prelude.Eq

/-! Optional axiom-backed function extensionality. This module is not imported by `Prelude`.
Function extensionality depends on `Quot.sound`, so an identity that it gives does not
compute.
-/

set_option autoImplicit false

universe u v

namespace Prelude.Axiom

/-- Function extensionality inherited from Lean's quotient-based equality theorem. -/
def funext {α : Type u} {P : α → Type v} {f g : (x : α) → P x}
    (p : (x : α) → f x ≡ g x) : f ≡ g :=
  Identity.ofEq (_root_.funext fun x => (p x).toEq)

end Prelude.Axiom
