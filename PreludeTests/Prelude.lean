import Prelude

set_option autoImplicit false
set_option genInjectivity false

open Prelude
open scoped Prelude

namespace PreludeTests

universe u v

-- Identity has the same universe level as its carrier.
def identityUniverse {A : Type u} (x y : A) : Type u := x ≡ y
def identityToEq {A : Type u} {x y : A} (p : x ≡ y) : x = y := p.toEq

-- Based induction permits a motive that observes the identity witness.
def basedInductionComputes {A : Type u} {x : A} (P : (y : A) → x ≡ y → Type v)
    (r : P x .refl) : Identity.ind P r Identity.refl = r := rfl

-- The induction with the second element fixed computes at the reflexivity proof.
def endInductionComputes {A : Type u} {y : A} (P : (x : A) → x ≡ y → Type v)
    (r : P y .refl) : Identity.indEnd P r Identity.refl ≡ r := .refl

-- The identity of two pairs computes at reflexivity proofs, for arbitrary elements.
def pairComputes {A : Type u} {B : Type v} (x : A) (y : B) :
    Identity.cong₂ Prod.mk (.refl : x ≡ x) (.refl : y ≡ y) ≡ .refl := .refl

def identityChain {A : Type u} {x y z : A} (p : x ≡ y) (q : y ≡ z) : x ≡ z := calc
  x ≡ y := p
  _ ≡ z := q

-- Dependent transport changes the index of ordinary Lean datatypes.
def resize {n m : Nat} (p : n ≡ m) (i : Fin n) : Fin m :=
  Identity.transport Fin p i

#guard (resize Identity.refl (⟨2, by decide⟩ : Fin 3)).val == 2

def dependentPair {A : Type u} {P : A → Type v} {x y : A} {a : P x} {b : P y}
    (p : x ≡ y) (q : Identity.transport P p a ≡ b) :
    (⟨x, a⟩ : Sigma P) ≡ ⟨y, b⟩ := Identity.sigma p q

/-- error: Unknown identifier `Prelude.Axiom.funext` -/
#guard_msgs in
#check Prelude.Axiom.funext

/-- error: Unknown constant `Prelude.Identity.ofEq` -/
#guard_msgs in
#check @Prelude.Identity.ofEq

-- Standard Lean equality, identity monad, and decision instances remain available.
def arithmeticReduction : 2 + 3 = 5 := rfl
def identityMonad : Id Nat := do pure 7
def listFiniteDecision : DecidableEq (List (Fin 4)) := inferInstance

#guard (decideEq (3 : Nat) 3).isYes
#guard !(decideEq (3 : Nat) 4).isYes
#guard (decideEq [some true, none] [some true, none]).isYes
#guard !(decideEq [some true, none] [none, some true]).isYes
#guard (Dec.ofDecidable (2 < 3)).isYes
#guard !(Dec.ofDecidable (3 < 2)).isYes
#guard (Dec.product (decideEq true true) (decideEq false false)).isYes
#guard !(Dec.product (decideEq true false) (decideEq false false)).isYes
#guard (Dec.sum (decideEq true false) (decideEq false false)).isYes
#guard !(Dec.sum (decideEq true false) (decideEq false true)).isYes
#guard (Dec.negate (decideEq true false)).isYes

-- Equality decisions reduce in the kernel, and their witnesses are consumed.
def decideNat : Identity (decideEq (3 : Nat) 3).isYes true := .refl
def refuteNat : Identity (decideEq (3 : Nat) 4).isYes false := .refl
def decideList : Identity (decideEq [some (1 : Nat), none] [some 1, none]).isYes true := .refl
def decideFin : Identity (decideEq (2 : Fin 5) 2).isYes true := .refl
def decideSum : Identity (decideEq (Sum.inl 1 : Sum Nat Bool) (.inr true)).isYes false := .refl

def decidedIndex (n m : Nat) (i : Fin (n + 1)) : Option (Fin (m + 1)) :=
  match decideEq n m with
  | .yes p => some (Identity.transport (fun k => Fin (k + 1)) p i)
  | .no _ => none

def consumeDecision :
    Identity ((decidedIndex 4 4 ⟨3, by decide⟩).map Fin.val) (some 3) := .refl

-- Repeated types in a context retain distinct positions and values.
inductive Ty where | nat | bool

abbrev Ty.denote : Ty → Type
  | .nat => Nat
  | .bool => Bool

def env : All Ty.denote [.nat, .bool, .nat] :=
  .cons 7 (.cons true (.cons 11 .nil))

def first : Elem Ty.nat [.nat, .bool, .nat] := .here
def third : Elem Ty.nat [.nat, .bool, .nat] := .there (.there .here)

#guard env.lookup first == 7
#guard env.lookup third == 11
#guard first.toFin.val == 0
#guard third.toFin.val == 2

def distinctPositions : first ≡ third → Empty := fun p =>
  False.elim (by have h := (Identity.cong (fun i => i.toFin.val) p).toEq; cases h)

def tabulatedLookup : (All.tabulate _ (fun _ i => env.lookup i)).lookup third ≡ 11 :=
  All.lookupTabulate (fun _ i => env.lookup i) third

/-- The positions of the two parts of a concatenation, with an arbitrary second part. -/
def leftLookup (extra : All Ty.denote [Ty.bool]) :
    (env.append extra).lookup first.left ≡ 7 := .refl

def rightLookup (b : Bool) :
    (env.append (.cons b .nil : All Ty.denote [Ty.bool])).lookup
        (Elem.right [Ty.nat, Ty.bool, Ty.nat] (.here : Elem Ty.bool [Ty.bool])) ≡ b := .refl

def arbitrary (n m : Nat) (b : Bool) : All Ty.denote [Ty.nat, Ty.bool, Ty.nat] :=
  .cons n (.cons b (.cons m .nil))

/-- A selection repeats one position and omits one. -/
def selected (n m : Nat) (b : Bool) :
    (arbitrary n m b).select (.cons third (.cons third (.cons first .nil))) ≡
      (.cons m (.cons m (.cons n .nil)) : All Ty.denote [Ty.nat, Ty.nat, Ty.nat]) := .refl

/-- The selection at a concatenation of two lists of positions. -/
def selectedAppend (n m : Nat) (b : Bool) :
    All.selectAppend (arbitrary n m b) (.cons third .nil) (.cons first (.cons third .nil)) ≡
      .refl := .refl

/-- The two laws of `map`, with arbitrary values. -/
def mappedTwice (n m : Nat) (b : Bool) :
    All.mapMap (Q := fun _ => Nat) (R := fun _ => Nat) (fun _ _ => n) (fun _ k => k + m)
      (arbitrary n m b) ≡ .refl := .refl

def mappedSame (n m : Nat) (b : Bool) :
    All.mapCongr (Q := fun _ => Nat) (f := fun _ _ => n + 0) (g := fun _ _ => n)
      (fun _ _ => .refl) (arbitrary n m b) ≡ .refl := .refl

/-- A table of the positions of the second part of a concatenation selects that part. The
identity is consumed through a dependent payload. -/
def selectedTable (n m : Nat) (b c : Bool) :
    (Identity.transport (fun k => Fin (k + 1))
      (Identity.cong (fun (out : All Ty.denote [Ty.nat, Ty.bool, Ty.nat]) => out.lookup third)
        (All.selectTabulate ((.cons c .nil : All Ty.denote [Ty.bool]).append (arbitrary n m b))
          (arbitrary n m b) (fun _ i => i.right [Ty.bool])
          (fun _ i => All.lookupRight (.cons c .nil : All Ty.denote [Ty.bool])
            (arbitrary n m b) i)))
      ⟨m, Nat.lt_succ_self _⟩).val ≡ m := .refl

/-- The first value and the other values of an environment, with arbitrary values. -/
def headValue (n m : Nat) (b : Bool) : (arbitrary n m b).head ≡ n := .refl

def tailValue (n m : Nat) (b : Bool) :
    (arbitrary n m b).tail ≡ (.cons b (.cons m .nil) : All Ty.denote [Ty.bool, Ty.nat]) := .refl

/-- The value of a map at a position, and the selection at selected positions. -/
def mappedLookup (n m : Nat) (b : Bool) :
    All.lookupMap (Q := fun _ => Nat) (fun _ _ => n + m) (arbitrary n m b) third ≡ .refl := .refl

def selectedTwice (n m : Nat) (b : Bool) :
    All.selectSelect (arbitrary n m b) (.cons third (.cons first .nil))
      (.cons (.there .here) (.cons .here .nil) : All (fun a => Elem a [Ty.nat, Ty.nat]) _) ≡
      .refl := .refl

/-- The decision of the identity of two positions of one element, and of two lists of
positions. -/
def samePosition : ((Elem.decide third third).isYes, (Elem.decide first third).isYes) ≡
    (true, false) := .refl

def positions : All (fun a => Elem a [Ty.nat, Ty.bool, Ty.nat]) [.nat, .nat] :=
  .cons third (.cons first .nil)

def samePositions :
    ((All.decide (fun _ => Elem.decide) positions positions).isYes,
        (All.decide (fun _ => Elem.decide) positions (.cons first (.cons first .nil))).isYes) ≡
      (true, false) := .refl

/-- The identity of a decision is consumed through a dependent payload. -/
def decidedPayload : Dec (positions ≡ positions) → Nat
  | .yes p =>
      (Identity.transport
        (fun (q : All (fun a => Elem a [Ty.nat, Ty.bool, Ty.nat]) [.nat, .nat]) =>
          Fin (q.head.toFin.val + 1))
        p ⟨2, Nat.lt_succ_self _⟩).val
  | .no _ => 0

def decidedSelection :
    decidedPayload (All.decide (fun _ => Elem.decide) positions positions) ≡ 2 := .refl

/-- The part of a position of the second part of a concatenation is that position. -/
def splitOfRight : Elem.splitRight [Ty.bool, Ty.bool] third ≡ .refl := .refl

/-- The number of each pair with a true flag. -/
def flagged (x : Bool × Nat) : Option Nat :=
  match x.1 with
  | true => some x.2
  | false => none

/-- A position of the list of the values of a partial function, with arbitrary values. -/
def filteredPosition (n m k : Nat) :
    (Elem.ofFilterMap (f := flagged) (y := k) (xs := [(false, n), (true, m), (true, k)])
      (.there (.there .here)) .refl).toFin.val ≡ 1 := .refl

/-- A position of the concatenation of the lists of values, with arbitrary values. -/
def flatPosition (n m : Nat) :
    (Elem.ofFlatMap (f := fun (x : Nat) => [x, x]) (xs := [n, m]) (.there .here)
      (.there .here)).toFin.val ≡ 3 := .refl

/-- A selection is a table of its values, with arbitrary values. -/
def selectionIsTable (n m : Nat) (b : Bool) :
    All.selectValues (arbitrary n m b) positions
      (fun (_ : Ty) (i : Elem _ [Ty.nat, Ty.nat]) => (arbitrary n m b).lookup (positions.lookup i))
      (fun _ _ => .refl) ≡ .refl := .refl

/-- The values at the image of a list, with arbitrary values. -/
def imageValues (n m : Nat) (b : Bool) :
    All.image (T := fun (_ : Unit) => Nat) (fun _ => ()) (fun _ _ => n + m) (arbitrary n m b) ≡
      .cons (n + m) (.cons (n + m) (.cons (n + m) .nil)) := .refl

/-- A list with no element at two positions, from its tail and the evidence that its first
element has no position in the tail. -/
def distinctTypes : Elem.Distinct [Ty.nat, Ty.bool] :=
  Elem.Distinct.cons (Elem.Distinct.cons (fun _ i _ => i.ofNil) (fun i => i.ofNil)) fun i =>
    match Elem.uncons i with
    | .inl p =>
        Identity.transport (fun t => match t with | Ty.nat => Unit | Ty.bool => Empty) p ()
    | .inr j => j.ofNil

def distinctHere : distinctTypes Ty.nat .here .here ≡ .refl := .refl

def distinctTail : distinctTypes.tail Ty.bool .here .here ≡ .refl := .refl

/-- The value of an option under a function, with an arbitrary value. -/
def mappedValue (n : Nat) :
    (Identity.ofMapSome (f := Nat.succ) (some n) (y := n + 1) .refl).1 ≡ n := .refl

/-- Two identity proofs of two numbers are one proof, from the decision of the identity of two
numbers. -/
def oneProof (n : Nat) (p : n ≡ n) : p ≡ .refl := Dec.unique DecEq.nat p .refl

/-- The proof computes for closed numbers. -/
def oneProofClosed : oneProof 3 .refl ≡ .refl := .refl

/-- Two positions with one number are one position. -/
def sameThird : Elem.sameNumber third third .refl ≡ .refl := .refl

/-- info: 'PreludeTests.endInductionComputes' does not depend on any axioms -/
#guard_msgs in
#print axioms endInductionComputes

/-- info: 'PreludeTests.pairComputes' does not depend on any axioms -/
#guard_msgs in
#print axioms pairComputes

/-- info: 'PreludeTests.splitOfRight' does not depend on any axioms -/
#guard_msgs in
#print axioms splitOfRight

/-- info: 'PreludeTests.filteredPosition' does not depend on any axioms -/
#guard_msgs in
#print axioms filteredPosition

/-- info: 'PreludeTests.flatPosition' does not depend on any axioms -/
#guard_msgs in
#print axioms flatPosition

/-- info: 'PreludeTests.oneProof' does not depend on any axioms -/
#guard_msgs in
#print axioms oneProof

/-- info: 'PreludeTests.sameThird' does not depend on any axioms -/
#guard_msgs in
#print axioms sameThird

/-- info: 'PreludeTests.distinctTail' does not depend on any axioms -/
#guard_msgs in
#print axioms distinctTail

/-- info: 'PreludeTests.mappedValue' does not depend on any axioms -/
#guard_msgs in
#print axioms mappedValue

/-- info: 'PreludeTests.decidedSelection' does not depend on any axioms -/
#guard_msgs in
#print axioms decidedSelection

/-- info: 'PreludeTests.imageValues' does not depend on any axioms -/
#guard_msgs in
#print axioms imageValues

/-- info: 'Prelude.Identity.transport' does not depend on any axioms -/
#guard_msgs in
#print axioms Identity.transport

/-- info: 'Prelude.All.lookupTabulate' does not depend on any axioms -/
#guard_msgs in
#print axioms All.lookupTabulate

end PreludeTests

namespace PreludeTests.IdentityChecks

inductive Stamp : Nat → Type where
  | mark (n : Nat) (payload : Nat) : Stamp n

def read {n : Nat} : Stamp n → Nat
  | .mark _ payload => payload

/-- The payload is recovered after eliminating both a transport and its inverse. -/
def roundTrip (n payload : Nat) :
    Identity (read (Identity.transport Stamp (Identity.symm (Identity.refl (a := n)))
      (Identity.transport Stamp .refl (.mark n payload)))) payload := .refl

def consumeRoundTrip {n m : Nat} (h : Identity n m) (payload : Nat) :
    Identity (read (Identity.transport Stamp (Identity.symm h)
      (Identity.transport Stamp h (.mark n payload)))) payload :=
  Identity.cong read (Identity.transportSymm Stamp h (.mark n payload))

def branch (b : Bool) (n : Nat) : Identity n n :=
  match b with
  | false => .refl
  | true => Identity.trans .refl .refl

def consumeFalse (n payload : Nat) :
    Identity (read (Identity.transport Stamp (branch false n) (.mark n payload))) payload := .refl

def consumeTrue (n payload : Nat) :
    Identity (read (Identity.transport Stamp (branch true n) (.mark n payload))) payload := .refl

/-- A homotopy between two functions that are not syntactically equal. -/
def addZero (f : Nat → Nat) : Homotopy f (fun n => f n + 0) := fun _ => .refl

-- A composed homotopy and its inverse are consumed at an arbitrary point.
def consumeHomotopy (f : Nat → Nat) (n payload : Nat) :
    Identity (read (Identity.transport Stamp
      (((addZero f).trans (addZero _)).trans ((addZero f).trans (addZero _)).symm n)
      (.mark (f n) payload))) payload := .refl

end PreludeTests.IdentityChecks
