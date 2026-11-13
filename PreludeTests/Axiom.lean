import Prelude.Axiom

set_option autoImplicit false

namespace PreludeTests.Axiom

open Prelude

universe u v

/-- Check the explicitly imported observational API. -/
def functionExtensionality {A : Type u} {P : A → Type v} {f g : (x : A) → P x}
    (h : Homotopy f g) : Identity f g := Prelude.Axiom.funext h

end PreludeTests.Axiom
