import Draft.Checks.Dependent
import Draft.Checks.Free

/-! Verified computations with branching and repeated binds.
The response of the first call selects the next call. The receipt of each response gives the
key of the next admission, and the two cases use different admission constructors. The checks
run the evidence with arbitrary responses and arbitrary keys, and they eliminate the identity
of each receipt to recover its payload. They also move the evidence along the agreements of
the bind laws.
-/

set_option autoImplicit false
set_option genInjectivity false
set_option smartUnfolding false

open Prelude

namespace Draft.Checks.Verified

open Container Dependent Free

def observe : (a : Key) → Reply a → Nat
  | .flag, b => cond b 1 0
  | .one, n => n
  | .two, q => q.1 + q.2

/-- Each call has an admission, and each response has a receipt for the value that the
admission expects. -/
def spec : DepPoly store where
  Pre _ := Admission
  Post a pre reply := Receipt (expected pre (observe a reply))

def verify (flag : Bool) (x y : Nat) : Evidence spec (provider flag x y) :=
  fun a pre => ⟨expected pre (observe a (provider flag x y a)), .refl⟩

/-- The flag selects the next call. The result has the case and the value of the response. -/
def branch : Free store (Bool × Nat) :=
  .request .flag fun
    | false => .request .one fun m => .pure (false, m)
    | true => .request .two fun q => .pure (true, q.1 + q.2)

/-- The value that the receipts of the two calls give for a result. -/
def target (pre : Admission) : Bool × Nat → Nat
  | (false, v) => v + expected pre 0
  | (true, v) => expected pre 1 + v + 1

/-- The receipt of the flag is the key of the next admission. -/
def branchDep (pre : Admission) :
    FreeDep spec (fun result => Receipt (target pre result)) branch :=
  .request pre fun
    | false, flagged => .request (.first flagged.actual) fun (m : Nat) receipt =>
        .pure ⟨receipt.actual,
          receipt.agrees.trans (Identity.cong (fun k => m + k) flagged.agrees)⟩
    | true, flagged => .request (.second flagged.actual) fun (q : Nat × Nat) receipt =>
        .pure ⟨receipt.actual,
          receipt.agrees.trans (Identity.cong (fun k => k + (q.1 + q.2) + 1) flagged.agrees)⟩

def consume (flag : Bool) (x y : Nat) (pre : Admission) : Nat :=
  ((branchDep pre).run (verify flag x y)).read

/-- Kernel checks of the two cases and the two admission constructors. -/
def singleFirst (x y key : Nat) : Identity (consume false x y (.first key)) (x + (0 + key)) :=
  .refl

def singleSecond (x y key : Nat) :
    Identity (consume false x y (.second key)) (x + (key + 0 + 1)) := .refl

def pairFirst (x y key : Nat) :
    Identity (consume true x y (.first key)) (1 + key + (x + y) + 1) := .refl

def pairSecond (x y key : Nat) :
    Identity (consume true x y (.second key)) (key + 1 + 1 + (x + y) + 1) := .refl

/-- One more call. The result keeps the prior result. -/
def more (prior : Bool × Nat) : Free store ((Bool × Nat) × Nat) :=
  .request .one fun m => .pure (prior, m)

def twice : Free store ((Bool × Nat) × Nat) := branch.bind more

abbrev Total (pre : Admission) (result : (Bool × Nat) × Nat) : Type :=
  Receipt (target pre result.1 + result.2 + 1)

/-- The receipt of the prior result is the key of the admission. -/
def moreDep (pre : Admission) (prior : Bool × Nat) (receipt : Receipt (target pre prior)) :
    FreeDep spec (Total pre) (more prior) :=
  .request (.second receipt.actual) fun (m : Nat) second =>
    .pure ⟨second.actual,
      second.agrees.trans (Identity.cong (fun k => k + m + 1) receipt.agrees)⟩

def twiceDep (pre : Admission) : FreeDep spec (Total pre) twice :=
  (branchDep pre).bind (moreDep pre)

def consumeTwice (flag : Bool) (x y : Nat) (pre : Admission) : Nat :=
  ((twiceDep pre).run (verify flag x y)).read

def twiceSingle (x y key : Nat) :
    Identity (consumeTwice false x y (.first key)) (x + (0 + key) + x + 1) := .refl

def twicePair (x y key : Nat) :
    Identity (consumeTwice true x y (.second key)) (key + 1 + 1 + (x + y) + 1 + x + 1) := .refl

/-- The run of the bind and the run of its two stages give the same evidence. -/
def staged (flag : Bool) (x y : Nat) (pre : Admission) :=
  FreeDep.runBind (verify flag x y) (moreDep pre) (branchDep pre)

/-- The identity of `runBind` is consumed through a dependent payload. -/
def consumeStaged (x y key : Nat) :
    Identity (Identity.transport (fun n => Fin (n + 1))
      (Identity.cong Receipt.read (staged true x y (.first key)))
      ⟨0, Nat.zero_lt_succ _⟩).val 0 := .refl

/-- A last call. The result keeps the prior result and the response. -/
def third (prior : (Bool × Nat) × Nat) : Free store (((Bool × Nat) × Nat) × Bool) :=
  .request .flag fun b => .pure (prior, b)

abbrev Final (pre : Admission) (result : ((Bool × Nat) × Nat) × Bool) : Type :=
  Receipt (cond result.2 1 0 + (target pre result.1.1 + result.1.2 + 1))

def thirdDep (pre : Admission) (prior : (Bool × Nat) × Nat) (total : Total pre prior) :
    FreeDep spec (Final pre) (third prior) :=
  .request (.first total.actual) fun (b : Bool) last =>
    .pure ⟨last.actual,
      last.agrees.trans (Identity.cong (fun k => cond b 1 0 + k) total.agrees)⟩

/-- The associativity agreement of the three stages. -/
def assoc : Free.Agreement ((branch.bind more).bind third)
    (branch.bind (fun prior => (more prior).bind third)) :=
  Free.bindAssoc more third branch

/-- The evidence of the left form, moved to the right form. -/
def movedDep (pre : Admission) :
    FreeDep spec (Final pre) (branch.bind (fun prior => (more prior).bind third)) :=
  ((twiceDep pre).bind (thirdDep pre)).reindex assoc

def consumeMoved (flag : Bool) (x y : Nat) (pre : Admission) : Nat :=
  ((movedDep pre).run (verify flag x y)).read

def movedSingle (x y key : Nat) :
    Identity (consumeMoved false x y (.first key)) (0 + (x + (0 + key) + x + 1)) := .refl

def movedPair (x y key : Nat) :
    Identity (consumeMoved true x y (.second key))
      (1 + (key + 1 + 1 + (x + y) + 1 + x + 1)) := .refl

/-- The evidence that the right form constructs directly gives the same payload. -/
def directDep (pre : Admission) :
    FreeDep spec (Final pre) (branch.bind (fun prior => (more prior).bind third)) :=
  (branchDep pre).bind (fun prior receipt => (moreDep pre prior receipt).bind (thirdDep pre))

def movedDirect (flag : Bool) (x y key : Nat) :
    Identity (consumeMoved flag x y (.second key))
      ((directDep (.second key)).run (verify flag x y)).read :=
  match flag with
  | false => .refl
  | true => .refl

/-- The identity of `runReindex` is consumed through a dependent payload. -/
def consumeRunReindex (x y key : Nat) :
    Identity (Identity.transport (fun n => Fin (n + 1))
      (Identity.cong Receipt.read
        (FreeDep.runReindex (verify true x y) assoc
          ((twiceDep (.first key)).bind (thirdDep (.first key)))))
      ⟨0, Nat.zero_lt_succ _⟩).val 0 := .refl

/-- The unit agreement moves the evidence of a bind with `pure` to the computation. -/
def unitDep (pre : Admission) : FreeDep spec (Total pre) twice :=
  ((twiceDep pre).bind (fun _ total => .pure total)).reindex (Free.bindPure twice)

def unitSingle (x y key : Nat) :
    Identity ((unitDep (.first key)).run (verify false x y)).read (x + (0 + key) + x + 1) :=
  .refl

-- Compiled observations supplement the kernel consumers above.
#guard consume false 3 4 (.first 5) == 8
#guard consume true 3 4 (.second 5) == 15
#guard consumeTwice false 3 4 (.first 5) == 12
#guard consumeTwice true 3 4 (.second 5) == 19
#guard consumeMoved false 3 4 (.first 5) == 12
#guard consumeMoved true 3 4 (.second 5) == 20

end Draft.Checks.Verified

/-- info: 'Draft.Checks.Verified.consumeRunReindex' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Verified.consumeRunReindex

/-- info: 'Draft.Checks.Verified.unitDep' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Verified.unitDep

/-- info: 'Draft.Checks.Verified.unitSingle' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Verified.unitSingle
