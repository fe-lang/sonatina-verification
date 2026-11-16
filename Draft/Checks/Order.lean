import Draft.Checks.Verified

/-! Two orders of pure calls.
An operation is pure when its implementation returns without a call. Two computations call the
same two pure operations and one effectful operation in different orders. After the
substitution of the implementations, only the effectful call stays, and the two computations
are identical. The evidence of each order becomes evidence of that one computation, and the
two give the same payload for arbitrary responses. The evidence of one order also gives
evidence of the other order, because the specification of each pure operation here fixes its
response.
-/

set_option autoImplicit false
set_option genInjectivity false
set_option smartUnfolding false

open Prelude

namespace Draft.Checks.Order

open Container Free
open Dependent (Receipt)
open Verified (spec verify)

inductive Op where
  | double (a : Nat)
  | add (a b : Nat)

def eval : Op → Nat
  | .double a => a + a
  | .add a b => a + b

/-- The interface of the pure operations. -/
def arithmetic : Container := ⟨Op, fun _ => Nat⟩

/-- The response of a pure operation is identical to its value. -/
def arithmeticSpec : DepPoly arithmetic where
  Pre _ := Unit
  Post op _ response := Identity response (eval op)

inductive Kind where
  | pure
  | effect

def family : Kind → Container
  | .pure => arithmetic
  | .effect => store

def specs : (k : Kind) → DepPoly (family k)
  | .pure => arithmeticSpec
  | .effect => spec

/-- A pure operation returns its value without a call. An effectful operation is one call. -/
def lower : (k : Kind) → Impl (family k) store
  | .pure => Impl.ofSection eval
  | .effect => Impl.id store

def lowerDep : (k : Kind) → ImplDep (specs k) spec (lower k)
  | .pure => ImplDep.ofEvidence (r := arithmeticSpec) (f := eval) (fun _ _ => .refl)
  | .effect => ImplDep.id spec

def implementation : Impl (sigma family) store := Impl.copair lower

def implementationDep : ImplDep (DepPoly.sigma specs) spec implementation :=
  ImplDep.copair lowerDep

/-- The two pure calls, and then the effectful call. -/
def early (a b : Nat) : Free (sigma family) (Nat × Nat × Nat) :=
  .request ⟨.pure, .double a⟩ fun (x : Nat) =>
    .request ⟨.pure, .add b 1⟩ fun (y : Nat) =>
      .request ⟨.effect, .one⟩ fun (z : Nat) => .pure (x, y, z)

/-- The effectful call, and then the two pure calls in the other order. -/
def late (a b : Nat) : Free (sigma family) (Nat × Nat × Nat) :=
  .request ⟨.effect, .one⟩ fun (z : Nat) =>
    .request ⟨.pure, .add b 1⟩ fun (y : Nat) =>
      .request ⟨.pure, .double a⟩ fun (x : Nat) => .pure (x, y, z)

/-- After the substitution, the two orders are one computation. -/
def sameComputation (a b : Nat) :
    Identity ((early a b).subst implementation) ((late a b).subst implementation) := .refl

/-- That computation has the effectful call only. -/
def oneCall (a b : Nat) :
    Identity ((early a b).subst implementation)
      (.request .one fun (z : Nat) => .pure (a + a, b + 1, z)) := .refl

/-- The evidence at a result: the first component is the double, and the receipt of the read
has the sum in its key. -/
abbrev Result (a b : Nat) (result : Nat × Nat × Nat) : Type :=
  Identity result.1 (a + a) × Receipt (result.2.2 + (b + 1))

/-- The admission of the read has the response of the pure sum as its key. -/
def earlyDep (a b : Nat) : FreeDep (DepPoly.sigma specs) (Result a b) (early a b) :=
  .request () fun _ doubled =>
    .request () fun (y : Nat) summed =>
      .request (.first y) fun (z : Nat) receipt =>
        .pure (doubled,
          ⟨receipt.actual, receipt.agrees.trans (Identity.cong (fun k => z + k) summed)⟩)

/-- The read is first, so its admission has the value of the sum as its key. -/
def lateDep (a b : Nat) : FreeDep (DepPoly.sigma specs) (Result a b) (late a b) :=
  .request (.first (b + 1)) fun _ receipt =>
    .request () fun _ _ =>
      .request () fun _ doubled => .pure (doubled, receipt)

/-- The evidence of each order is evidence of the one computation. -/
def earlyLow (a b : Nat) : FreeDep spec (Result a b) ((late a b).subst implementation) :=
  (earlyDep a b).subst implementationDep

def lateLow (a b : Nat) : FreeDep spec (Result a b) ((late a b).subst implementation) :=
  (lateDep a b).subst implementationDep

/-- The payload eliminates the identity of the double and the identity of the receipt. -/
def payload {a b : Nat} {result : Nat × Nat × Nat} (e : Result a b result) : Nat :=
  (Identity.transport (fun n => Fin (n + 1)) e.1 ⟨result.1, Nat.lt_succ_self _⟩).val + e.2.read

def readEarly (flag : Bool) (x y a b : Nat) : Nat :=
  payload ((earlyLow a b).run (verify flag x y))

def readLate (flag : Bool) (x y a b : Nat) : Nat :=
  payload ((lateLow a b).run (verify flag x y))

def earlyPayload (flag : Bool) (x y a b : Nat) :
    Identity (readEarly flag x y a b) (a + a + (x + (b + 1))) := .refl

def latePayload (flag : Bool) (x y a b : Nat) :
    Identity (readLate flag x y a b) (a + a + (x + (b + 1))) := .refl

/-- Evidence of the computation after the substitution gives evidence of a computation that
has the pure calls. The specification of a pure operation fixes its response, so the evidence
at the value of the operation moves to each response. -/
def raise {α : Type} {Q : α → Type} : (x : Free (sigma family) α) →
    FreeDep spec Q (x.subst implementation) → FreeDep (DepPoly.sigma specs) Q x
  | .pure _, h => .pure h.result
  | .request ⟨.pure, op⟩ k, h =>
      .request () fun _ same =>
        Identity.transport (fun y => FreeDep (DepPoly.sigma specs) Q (k y)) same.symm
          (raise (k (eval op)) h)
  | .request ⟨.effect, _⟩ k, h =>
      .request h.parts.1 fun i post => raise (k i) (h.parts.2 i post)

/-- The evidence of the late order, constructed from the evidence of the early order. -/
def lateFromEarly (a b : Nat) : FreeDep (DepPoly.sigma specs) (Result a b) (late a b) :=
  raise (late a b) ((earlyDep a b).subst implementationDep)

def movedPayload (flag : Bool) (x y a b : Nat) :
    Identity (payload ((lateFromEarly a b).run (implementationDep.run (verify flag x y))))
      (a + a + (x + (b + 1))) := .refl

/-- A computation with pure calls only agrees with the value of its run. -/
def sums (a b : Nat) : Free arithmetic Nat :=
  .request (.double a) fun (x : Nat) => .request (.add x b) .pure

def pureOnly (a b : Nat) :
    Identity (Identity.transport (fun n => Fin (n + 1))
      ((Free.substOfSection (C := arithmetic) (D := store) eval (sums a b)).run
        (f := provider false 0 0) (fun _ => .refl))
      ⟨a + a + b, Nat.lt_succ_self _⟩).val (a + a + b) := .refl

-- Compiled observations supplement the kernel consumers above.
#guard readEarly false 3 4 5 6 == 20
#guard readLate true 3 4 5 6 == 20

end Draft.Checks.Order
