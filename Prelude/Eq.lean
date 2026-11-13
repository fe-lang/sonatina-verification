import Prelude.Decision

/-! Adapters from Lean's Prop-valued equality to Type-valued identity.
`import Prelude` does not include this module. An identity built by `ofEq`
carries a proof that the kernel does not inspect: it reduces only when its
endpoints are definitionally equal. Its use is at boundaries with libraries
that state their results in `Prop`.
-/

set_option autoImplicit false
set_option genInjectivity false

universe u

namespace Prelude

namespace Identity

variable {α : Type u} {a b : α}

/-- Lift Lean equality to a Type-valued witness. -/
def ofEq (p : a = b) : a ≡ b :=
  match p with
  | rfl => .refl

def ofEqToEq (p : a ≡ b) : ofEq p.toEq ≡ p :=
  match p with
  | .refl => .refl

@[simp] theorem toEq_ofEq (p : a = b) : (ofEq p).toEq = p := rfl

theorem nonempty_iff : Nonempty (a ≡ b) ↔ a = b :=
  ⟨fun ⟨p⟩ => p.toEq, fun p => ⟨ofEq p⟩⟩

/-- Lean's proof irrelevance implies uniqueness of identity witnesses. -/
def unique (p q : a ≡ b) : p ≡ q :=
  p.ofEqToEq.symm.trans q.ofEqToEq

end Identity

namespace DecEq

/-- Lift an ordinary Lean equality decision. -/
abbrev ofDecidableEq {α : Type u} [DecidableEq α] : DecEq α where
  decEq a b := if h : a = b then .yes (Identity.ofEq h)
    else .no (fun p => (h p.toEq).elim)

instance (priority := low) {α : Type u} [DecidableEq α] : DecEq α := ofDecidableEq

/-- Install locally with `letI := DecEq.toDecidableEq (α := α)`. -/
def toDecidableEq {α : Type u} [DecEq α] : DecidableEq α := fun a b =>
  match decEq a b with
  | .yes p => isTrue p.toEq
  | .no refute => isFalse (fun p => (refute (Identity.ofEq p)).elim)

end DecEq

end Prelude
