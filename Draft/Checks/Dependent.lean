import Draft.Checks.Polynomial

/-! Witness-dependent verification under repeated one-call substitution.
Both response branches and both admission constructors carry arbitrary data.
`consume` must eliminate the response path and the receipt's own Type-valued
identity to recover its payload. Whole diagrams belong to D2, and their
substitution belongs to D5.
-/

set_option autoImplicit false
set_option genInjectivity false
set_option smartUnfolding false

open Prelude

namespace Draft.Checks.Dependent

open Container Polynomial

inductive Admission where
  | first (key : Nat)
  | second (key : Nat)

def expected (pre : Admission) (value : Nat) : Nat :=
  match pre with
  | .first key => value + key
  | .second key => key + value + 1

def observe : (a : Bool) → Ports a → Nat
  | false, n => n
  | true, (x, y) => x + y

structure Receipt (expected : Nat) where
  actual : Nat
  agrees : Identity actual expected

/-- The dependent `Fin` payload forces elimination of the receipt's identity. -/
def Receipt.read {n : Nat} (e : Receipt n) : Nat :=
  (Identity.transport (fun n => Fin (n + 1)) e.agrees
    ⟨e.actual, Nat.lt_succ_self e.actual⟩).val

def Post (a : Bool) (pre : Admission) (response : Ports a) : Type :=
  Receipt (expected pre (observe a response))

/-- Each call has an admission, and each response has a receipt for the expected value. -/
def spec : DepPoly boundary := ⟨fun _ => Admission, Post⟩

def verify (s : Section boundary) : Evidence spec s :=
  fun a pre => ⟨expected pre (observe a (s a)), .refl⟩

def calls : Nat → Hom boundary boundary
  | 0 => Hom.id boundary
  | n + 1 => (swap.trans swap).trans (calls n)

def normalized : Nat → Hom boundary boundary
  | 0 => Hom.id boundary
  | n + 1 => double.trans (normalized n)

def agreement : (n : Nat) → Hom.Agreement (calls n) (normalized n)
  | 0 => Hom.Agreement.refl _
  | n + 1 => Hom.transCongr doubleAgree (agreement n)

def responseAgreement (depth x y : Nat) :
    Homotopy ((calls depth).run (provider x y)) ((normalized depth).run (provider x y)) :=
  Hom.runCongr (agreement depth) (fun _ => .refl)

def verified (depth x y : Nat) :
    Evidence spec ((normalized depth).run (provider x y)) :=
  Evidence.reindex (responseAgreement depth x y)
    (verify ((calls depth).run (provider x y)))

def consume (depth x y : Nat) (branch : Bool) (pre : Admission) : Nat :=
  (verified depth x y branch pre).read

/-- Kernel checks with arbitrary response data and an arbitrary admission witness. -/
def singleBranch (x y : Nat) (pre : Admission) :
    Identity (consume 1 x y false pre) (expected pre x) := .refl

def pairBranch (x y : Nat) (pre : Admission) :
    Identity (consume 1 x y true pre) (expected pre (x + x)) := .refl

def firstWitness (x y key : Nat) :
    Identity (consume 2 x y true (.first key)) ((x + x) + key) := .refl

def secondWitness (x y key : Nat) :
    Identity (consume 2 x y true (.second key)) (key + (x + x) + 1) := .refl

/-- Generic inverse reindexing is consumed through its evidence path as well. -/
def roundTrip (depth x y : Nat) (branch : Bool) (pre : Admission) :
    Identity ((Evidence.reindex (responseAgreement depth x y).symm
      (verified depth x y)) branch pre).read
      (expected pre (observe branch ((calls depth).run (provider x y) branch))) :=
  Identity.cong Receipt.read
    (Evidence.reindexSymm (responseAgreement depth x y)
      (verify ((calls depth).run (provider x y))) branch pre)

def consumeRoundTrip (x y key : Nat) :
    Identity (Identity.transport (fun n => Fin (n + 1)) (roundTrip 2 x y true (.second key))
      ⟨0, Nat.zero_lt_succ _⟩).val 0 := .refl

def consumeAssoc (x y key : Nat) :
    Identity ((Evidence.reindex
      (Hom.runCongr (Hom.Agreement.ofIdentity (Hom.transAssoc swap swap swap))
        (fun _ => .refl))
      (verify (((swap.trans swap).trans swap).run (provider x y)))) true (.first key)).read
      ((x + x) + key) := .refl

def consumeTrans (x y key : Nat) :
    Identity (Identity.transport (fun n => Fin (n + 1))
      (Identity.cong Receipt.read (Evidence.reindexTrans
        (responseAgreement 2 x y)
        (Hom.runCongr (Hom.Agreement.ofIdentity (Hom.transId (normalized 2)))
          (fun _ => .refl))
        (verify ((calls 2).run (provider x y))) true (.first key)))
      ⟨0, Nat.zero_lt_succ _⟩).val 0 := .refl

-- Compiled observations supplement the kernel consumers above.
#guard consume 2 7 99 false (.first 3) == 10
#guard consume 2 7 99 false (.second 3) == 11
#guard consume 2 7 99 true (.first 3) == 17
#guard consume 2 7 99 true (.second 3) == 18

end Draft.Checks.Dependent

/-- info: 'Draft.Checks.Dependent.consumeRoundTrip' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependent.consumeRoundTrip

/-- info: 'Draft.Checks.Dependent.consumeAssoc' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependent.consumeAssoc

/-- info: 'Draft.Checks.Dependent.consumeTrans' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependent.consumeTrans
