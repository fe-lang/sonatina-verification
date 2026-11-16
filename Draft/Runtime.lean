import Draft.Diagram

/-! The runner of a computation with a runtime.

A handler of an interface has a runtime. For a call and a runtime, it gives a response with the
next runtime, or it stops with a value. The run of a computation with a handler is a recursion
on the computation: it has the runtime at each call in sequence, and it stops at the first call
that stops. The handler of a signature gives a relation of calls with a runtime, which is the
graph of the handler at the calls that give a response. -/

set_option autoImplicit false
set_option genInjectivity false

universe s p u r e

open Prelude Container

namespace Draft

/-- A handler of an interface with a runtime `R`. For a call and a runtime, it stops with a
value of `E`, or it gives a response with the next runtime. -/
abbrev Handler (C : Container.{s, p}) (R : Type r) (E : Type e) : Type (max s p r e) :=
  (a : C.Shape) → R → E ⊕ (C.Pos a × R)

namespace Handler

variable {C : Container.{s, p}} {R : Type r} {E : Type e} {α : Type u}

/-- The run of a computation with a handler, from a runtime. It stops at the first call that
stops, and it gives the returned value with the last runtime. -/
def run (h : Handler C R E) : Free C α → R → E ⊕ (α × R)
  | .pure a, s => .inr (a, s)
  | .request a k, s =>
      match h a s with
      | .inl stopped => .inl stopped
      | .inr next => run h (k next.1) next.2

/-- The run of a returned value has the value and the runtime. -/
def runPure (h : Handler C R E) (a : α) (s : R) : h.run (.pure a) s ≡ .inr (a, s) := .refl

end Handler

/-- The relation of calls of a handler of a signature: the graph of the handler at the calls
that give a response. -/
def Handler.calls {Ty : Type} {S : Signature Ty} {X : Ty → Type} {R : Type} {E : Type}
    (h : Handler (S.interface X) R E) : Signature.Calls.{0, 0} S X R :=
  fun a s i s' => h a s ≡ .inr (i, s')

end Draft
