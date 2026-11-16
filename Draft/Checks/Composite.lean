import Draft.Checks.Verified

/-! Verified implementations under repeated substitution.
The three implementations of `Draft.Checks.Free` have lifts. The receipt of each response is
the key of the next admission, and the two cases of the test use different admission
constructors. The evidence of a result records its case, so a consumer branches on it. The
checks run the lift of the composite with arbitrary responses and arbitrary keys, and they
move it along the associativity agreement of the composition.
-/

set_option autoImplicit false
set_option genInjectivity false
set_option smartUnfolding false

open Prelude

namespace Draft.Checks.Composite

open Container Polynomial Free
open Dependent (Admission Receipt expected)
open Verified (spec verify)

/-- The test has the receipt of the flag for its negated response. -/
def testSpec : DepPoly (family .test) where
  Pre _ := Admission
  Post _ pre (b : Bool) := Receipt (expected pre (cond b 0 1))

/-- The single case has the receipt of its response. The pair case has a hidden response,
and its receipt has the receipt of the first call in its key. -/
def DataPost : (a : Bool) → Admission → Ports a → Type
  | false, pre, n => Receipt (expected pre n)
  | true, pre, q => (hidden : Nat) × Receipt (q.2 + expected pre (hidden + q.1))

def dataSpec : DepPoly (family .data) := ⟨fun _ => Admission, DataPost⟩

def familySpec : (l : Label) → DepPoly (family l)
  | .test => testSpec
  | .data => dataSpec

def lowerDep : (l : Label) → ImplDep (familySpec l) spec (lower l)
  | .test => fun _ pre => .request pre fun
      | false, flagged => .pure flagged
      | true, flagged => .pure flagged
  | .data => fun
      | false, pre => .request pre fun _ receipt => .pure receipt
      | true, pre => .request pre fun (q : Nat × Nat) pair =>
          .request (.first pair.actual) fun (a : Nat) single =>
            .pure ⟨q.1, single.actual,
              single.agrees.trans (Identity.cong (fun k => a + k) pair.agrees)⟩

/-- The evidence of a result of `program`: its case, the responses, and a receipt whose key
has the receipt of the test. -/
inductive Outcome (pre : Admission) (n result : Nat) : Type where
  | single (m : Nat) (same : Identity result (n + m))
      (receipt : Receipt (m + expected pre 1))
  | pair (hidden u v : Nat) (same : Identity result (n + u + v))
      (receipt : Receipt (v + (expected pre 0 + (hidden + u) + 1)))

/-- The payload of an outcome, in each case. -/
def Outcome.key {pre : Admission} {n result : Nat} : Outcome pre n result → Nat
  | .single _ _ receipt => receipt.read
  | .pair _ _ _ _ receipt => receipt.read

def numberSpec : DepPoly number := ⟨fun _ => Admission, fun n pre => Outcome pre n⟩

def programDep : ImplDep numberSpec (DepPoly.sigma familySpec) program := fun _ pre =>
  .request pre fun
    | false, tested => .request (.first tested.actual) fun (m : Nat) got =>
        .pure (.single m .refl
          ⟨got.actual, got.agrees.trans (Identity.cong (fun k => m + k) tested.agrees)⟩)
    | true, tested => .request (.second tested.actual) fun (q : Nat × Nat) got =>
        .pure (.pair got.1 q.1 q.2 .refl
          ⟨got.2.actual, got.2.agrees.trans
            (Identity.cong (fun k => q.2 + (k + (got.1 + q.1) + 1)) tested.agrees)⟩)

/-- The evidence of a result of `user`: the two outcomes. The payload of the first outcome is
the key of the second admission. -/
structure Summary (pre : Admission) (result : Nat) : Type where
  a : Nat
  first : Outcome pre 1 a
  b : Nat
  second : Outcome (.first first.key) a b
  same : Identity result (a + b)

def taskSpec : DepPoly task := ⟨fun _ => Admission, fun _ pre result => Summary pre result⟩

def userDep : ImplDep taskSpec numberSpec user := fun _ pre =>
  .request pre fun a first =>
    .request (.first first.key) fun b second => .pure ⟨a, first, b, second, .refl⟩

def closedDep : ImplDep numberSpec spec closed := programDep.trans (ImplDep.copair lowerDep)

def leftDep : ImplDep taskSpec spec left :=
  (userDep.trans programDep).trans (ImplDep.copair lowerDep)

def rightDep : ImplDep taskSpec spec right := userDep.trans closedDep

/-- The payload of the second outcome, from a run of a lift. -/
def consume {f : Impl task store} (ff : ImplDep taskSpec spec f) (flag : Bool) (x y : Nat)
    (pre : Admission) : Nat :=
  (ff.run (verify flag x y) () pre).second.key

/-- Kernel checks of the two cases with arbitrary responses and keys. -/
def rightSingle (x y key : Nat) :
    Identity (consume rightDep true x y (.first key)) (x + (1 + (x + (1 + key)))) := .refl

def rightPair (x y key : Nat) :
    Identity (consume rightDep false x y (.second key))
      (x + (0 + (x + (key + 0 + 1 + (x + y) + 1)) + (x + y) + 1)) := .refl

def leftSingle (x y key : Nat) :
    Identity (consume leftDep true x y (.first key)) (x + (1 + (x + (1 + key)))) := .refl

def leftPair (x y key : Nat) :
    Identity (consume leftDep false x y (.second key))
      (x + (0 + (x + (key + 0 + 1 + (x + y) + 1)) + (x + y) + 1)) := .refl

/-- The second admission constructor for the inputs of `rightSingle`, and the first admission
constructor for the inputs of `rightPair`. The two constructors give different payloads. -/
def rightSingleSecond (x y key : Nat) :
    Identity (consume rightDep true x y (.second key)) (x + (1 + (x + (key + 1 + 1)))) := .refl

def rightPairFirst (x y key : Nat) :
    Identity (consume rightDep false x y (.first key))
      (x + (0 + (x + (0 + key + (x + y) + 1)) + (x + y) + 1)) := .refl

/-- The lift of the left form, moved along the associativity agreement. -/
def movedDep : ImplDep taskSpec spec right := leftDep.reindex assoc

def movedSingle (x y key : Nat) :
    Identity (consume movedDep true x y (.first key)) (x + (1 + (x + (1 + key)))) := .refl

def movedPair (x y key : Nat) :
    Identity (consume movedDep false x y (.second key))
      (x + (0 + (x + (key + 0 + 1 + (x + y) + 1)) + (x + y) + 1)) := .refl

/-- The identity of `runTrans` is consumed through a dependent payload. -/
def consumeRunTrans (x y key : Nat) :
    Identity (Identity.transport (fun n => Fin (n + 1))
      (Identity.cong (fun summary => summary.second.key)
        (ImplDep.runTrans userDep closedDep (verify false x y) () (.second key)))
      ⟨0, Nat.zero_lt_succ _⟩).val 0 := .refl

-- Compiled observations supplement the kernel consumers above.
#guard consume rightDep true 3 4 (.first 5) == 13
#guard consume leftDep true 3 4 (.first 5) == 13
#guard consume rightDep false 3 4 (.second 5) == 28
#guard consume movedDep false 3 4 (.second 5) == 28

end Draft.Checks.Composite
