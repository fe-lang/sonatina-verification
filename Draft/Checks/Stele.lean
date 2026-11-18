import Draft.Stele

/-! Compiled programs of the Stele fragment.

Each program is a function body of the fragment. Its diagram is the translation of the body,
and a run of the diagram has the handler of the operations with the storage as its runtime. A
run gives the returned integer with the last storage, no value at the limit of a loop, or a
stop at a `revert`.

The first program has a declaration, a write of storage, and a read of storage. Its check has
arbitrary arguments and an arbitrary storage. The second program has an `if` with an assignment
in one path, and the two paths have one continuation. The third program has a `while` with two
assignments in its body, and the fourth has a `while` that writes storage in its body. The
fifth group has a `require` and a division, and each of the two stops at a zero divisor. The
last group has `&&`, `||`, and the conditional expression: the expression that the test does
not select has no step in the run, so its division by zero does not stop the run.

A check with a test of a value has closed arguments. -/

set_option autoImplicit false
set_option genInjectivity false

open Prelude

namespace Draft.Checks.Stele

open Container
open Draft.Stele

/-! A declaration, a write of storage, and a read of storage. -/

/-- `let z = x * y + 3; slot0 = uint256(slot0 + z); return slot0 - x;` -/
def update : Stmt [.int, .int] :=
  .letDecl (.arith .add (.arith .mul (.var .here) (.var (.there .here))) (.intLit 3))
    (.assignStorage 0 (.wrap 256 (.arith .add (.storage 0) (.var .here)))
      (.ret (.arith .sub (.storage 0) (.var (.there .here)))))

def args₂ (x y : Int) : All Val [.int, .int] := .cons x (.cons y .nil)

set_option smartUnfolding false in
/-- The run has the written value at the read, for arbitrary arguments, an arbitrary storage,
and an arbitrary number of unrollings. -/
def updateRun (n : Nat) (x y : Int) (s : Store) :
    run update n (args₂ x y) s ≡
      .inr (some (wrap 256 (s 0 + (x * y + 3)) - x), s.write 0 (wrap 256 (s 0 + (x * y + 3)))) :=
  .refl

/-- The diagram has 9 steps: a product, a literal, and a sum for the declaration, a read, a
sum, a reduction to 256 bits, and a write for the assignment, and a read and a difference for
the return. -/
def updateSize : update.diagram.size ≡ 9 := .refl

/-! An `if` with an assignment in one path. -/

/-- `let m = x; if (x < y) { m = y; } return m;` -/
def larger : Stmt [.int, .int] :=
  .letDecl (.var .here)
    (.ite (.compare .lt (.var (.there .here)) (.var (.there (.there .here))))
      (.assign .here (.var (.there (.there .here))) .skip)
      .skip
      (.ret (.var .here)))

set_option smartUnfolding false in
def largerSecond (n : Nat) (s : Store) : run larger n (args₂ 3 5) s ≡ .inr (some 5, s) := .refl

set_option smartUnfolding false in
def largerFirst (n : Nat) (s : Store) : run larger n (args₂ 7 2) s ≡ .inr (some 7, s) := .refl

/-! A `while` with two assignments in its body. -/

/-- `let acc = 0; let i = k; while (0 < i) { acc = acc + i; i = i - 1; } return acc;` -/
def sum : Stmt [.int] :=
  .letDecl (.intLit 0)
    (.letDecl (.var (.there .here))
      (.whileDo (.compare .lt (.intLit 0) (.var .here))
        (.assign (.there .here) (.arith .add (.var (.there .here)) (.var .here))
          (.assign .here (.arith .sub (.var .here) (.intLit 1)) .skip))
        (.ret (.var (.there .here)))))

def args₁ (k : Int) : All Val [.int] := .cons k .nil

set_option smartUnfolding false in
/-- From 4, the loop has four iterations, and five or more unrollings give the sum. -/
def sumRun (n : Nat) (s : Store) : run sum (n + 5) (args₁ 4) s ≡ .inr (some 10, s) := .refl

set_option smartUnfolding false in
/-- With four unrollings, the run is at the limit of the loop. -/
def sumLimit (s : Store) : run sum 4 (args₁ 4) s ≡ .inr (none, s) := .refl

/-! A `while` that writes storage in its body. -/

/-- `let i = k; while (0 < i) { slot1 = slot1 + i; i = i - 1; } return slot1;` -/
def accumulate : Stmt [.int] :=
  .letDecl (.var .here)
    (.whileDo (.compare .lt (.intLit 0) (.var .here))
      (.assignStorage 1 (.arith .add (.storage 1) (.var .here))
        (.assign .here (.arith .sub (.var .here) (.intLit 1)) .skip))
      (.ret (.storage 1)))

set_option smartUnfolding false in
/-- From 2, the two writes add 2 and then 1 to the slot, for an arbitrary storage. -/
def accumulateRun (n : Nat) (s : Store) :
    run accumulate (n + 3) (args₁ 2) s ≡
      .inr (some (s 1 + 2 + 1), (s.write 1 (s 1 + 2)).write 1 (s 1 + 2 + 1)) := .refl

/-! A `require` and a division. -/

/-- `require(!(y == 0)); return x / y;` -/
def guarded : Stmt [.int, .int] :=
  .require (.not (.compare .eq (.var (.there .here)) (.intLit 0)))
    (.ret (.divide .div (.var .here) (.var (.there .here))))

/-- `return x / y;` -/
def quotient : Stmt [.int, .int] := .ret (.divide .div (.var .here) (.var (.there .here)))

set_option smartUnfolding false in
def guardedRun (n : Nat) (s : Store) : run guarded n (args₂ 7 2) s ≡ .inr (some 3, s) := .refl

set_option smartUnfolding false in
/-- The `require` stops at a zero divisor. -/
def guardedStop (n : Nat) (s : Store) : run guarded n (args₂ 7 0) s ≡ .inl () := .refl

set_option smartUnfolding false in
/-- The division stops at a zero divisor. -/
def quotientStop (n : Nat) (s : Store) : run quotient n (args₂ 7 0) s ≡ .inl () := .refl

set_option smartUnfolding false in
/-- Division is Euclidean. -/
def quotientNegative (n : Nat) (s : Store) :
    run quotient n (args₂ (-7) 2) s ≡ .inr (some (-4), s) := .refl

/-! `&&`, `||`, and the conditional expression. -/

/-- `x / y == 0` -/
def divides : Expr [.int, .int] .bool :=
  .compare .eq (.divide .div (.var .here) (.var (.there .here))) (.intLit 0)

/-- `return (!(y == 0) && x / y == 0) ? 1 : 2;` -/
def both : Stmt [.int, .int] :=
  .ret (.ite (.and (.not (.compare .eq (.var (.there .here)) (.intLit 0))) divides)
    (.intLit 1) (.intLit 2))

/-- `return (y == 0 || x / y == 0) ? 1 : 2;` -/
def either : Stmt [.int, .int] :=
  .ret (.ite (.or (.compare .eq (.var (.there .here)) (.intLit 0)) divides)
    (.intLit 1) (.intLit 2))

set_option smartUnfolding false in
/-- At a zero divisor, `&&` does not evaluate the division, and the run does not stop. -/
def bothZero (n : Nat) (s : Store) : run both n (args₂ 7 0) s ≡ .inr (some 2, s) := .refl

set_option smartUnfolding false in
def bothSmall (n : Nat) (s : Store) : run both n (args₂ 1 2) s ≡ .inr (some 1, s) := .refl

set_option smartUnfolding false in
/-- At a zero divisor, `||` does not evaluate the division. -/
def eitherZero (n : Nat) (s : Store) : run either n (args₂ 7 0) s ≡ .inr (some 1, s) := .refl

set_option smartUnfolding false in
def eitherLarge (n : Nat) (s : Store) : run either n (args₂ 7 2) s ≡ .inr (some 2, s) := .refl

section Pipeline

/-- Store the negation of the argument and return the same negation. The write separates
the two equal pure calls. -/
def writeNegation : Stmt [.int] :=
  .assignStorage 0 (.neg (.var .here)) (.ret (.neg (.var .here)))

private def expected (x : All Val [.int] × Store) : Unit ⊕ (Option Int × Store) :=
  let value := -(x.1.lookup .here : Int)
  .inr (some value, x.2.write 0 value)

abbrev Ticket := (bound : Nat) × Fin (bound + 1)

/-- The caller chooses a bound and a ticket at that bound. A completed run gives the
returned integer and the updated storage, together with a ticket at the supplied bound. -/
def contract : DepPoly ((Diagram.interface Val [.int] [Ret]).runtime Store Unit) where
  Pre _ := Ticket
  Post x admission o := (outcome o ≡ expected x) × Fin (admission.1 + 1)

set_option smartUnfolding false in
def writeNegationRun (n : Nat) (v : Int) (s : Store) :
    run writeNegation n (args₁ v) s ≡ expected (args₁ v, s) := .refl

abbrev Issue := (k : Nat) → Fin (k + 1) → Fin (k + 1)

/-- Source evidence consumes the Stele observation and issues a ticket at the admission's bound. -/
def sourceEvidence (issue : Issue) : contract.Map writeNegation.behavior :=
  fun ⟨.cons v .nil, s⟩ admission =>
    ⟨(), fun _ completed =>
      ⟨completed.2.symm.trans (writeNegationRun completed.1 v s), issue admission.1 admission.2⟩⟩

private def uniqueCase (Γ : List Ty) : IsContr (Boundary.one Γ).Case :=
  ⟨Boundary.only _, fun | ⟨_, .here⟩ => .refl⟩

def straight (issue : Issue) : (writeNegation.compile (sourceEvidence issue)).diagram.Straight :=
  ⟨uniqueCase _, uniqueCase _, uniqueCase _, ()⟩

set_option smartUnfolding false in
def mergeSizes (issue : Issue) :
    let compiled := writeNegation.compile (sourceEvidence issue)
    (compiled.diagram.size, (Diagram.merge compiled (straight issue) mergeSound).diagram.size) ≡
      (3, 2) := .refl

/-- The compiled implementation and its evidence, down to the residual storage interface. -/
def lowered (issue : Issue) : VerifiedImpl contract storageMachine.graph :=
  writeNegation.lowerStraight (sourceEvidence issue) (straight issue)

set_option smartUnfolding false in
def loweredWrite (issue : Issue) (v : Int) (s : Store) :
    ((lowered issue).impl (args₁ v, s)).run storageMachine ≡
      .inr (⟨_, .here, Boundary.only _, .cons (-v) .nil⟩, s.write 0 (-v)) := .refl

set_option smartUnfolding false in
def loweredReceipt (issue : Issue) (v : Int) (s : Store) (k : Nat) (ticket : Fin (k + 1)) :
    ((lowered issue).verification.run storageMachine.graphEvidence (args₁ v, s) ⟨k, ticket⟩).2 ≡ issue k ticket := .refl

set_option smartUnfolding false in
def loweredObservation (issue : Issue) (v : Int) (s : Store) (admit : Ticket) :
    Identity ((lowered issue).verification.run storageMachine.graphEvidence (args₁ v, s) admit).1 .refl := .refl

set_option smartUnfolding false in
/-- Falling off the end of a function produces a completed revert observation. -/
def revertObservation (s : Store) :
    let body : Stmt [] := .skip
    let issued := (body.compile (DepPoly.Map.id body.behavior)).verification (.nil, s) ()
    Identity (issued.2 (.inl ()) ⟨.inl (), .refl, ⟨.refl⟩⟩).2 .refl := .refl

set_option smartUnfolding false in
/-- An open statement receives the caller's fallthrough ports and exit observer. -/
def fallthroughObservation (v : Int) (s : Store) :
    let body : Stmt [.int] := .skip
    let fall := fun (Δ : List Ty) (ports : PortMap Δ [.int]) => Diagram.exitOne ports
    let compiled := body.compileIn .here [.int] (PortMap.id _) fall returned (DepPoly.Map.id _)
    let issued := compiled.verification (args₁ v, s) ()
    Identity (issued.2 (.inr (⟨_, .here, Boundary.only _, args₁ v⟩, s)) ⟨.refl⟩).2 .refl := .refl

end Pipeline

end Draft.Checks.Stele

/-- info: 'Draft.Checks.Stele.updateRun' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Stele.updateRun

/-- info: 'Draft.Checks.Stele.largerSecond' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Stele.largerSecond

/-- info: 'Draft.Checks.Stele.sumRun' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Stele.sumRun

/-- info: 'Draft.Checks.Stele.accumulateRun' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Stele.accumulateRun

/-- info: 'Draft.Checks.Stele.quotientNegative' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Stele.quotientNegative

/-- info: 'Draft.Checks.Stele.bothZero' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Stele.bothZero

/-- info: 'Draft.Checks.Stele.eitherLarge' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Stele.eitherLarge

/-- info: 'Draft.Checks.Stele.mergeSizes' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Stele.mergeSizes

/-- info: 'Draft.Checks.Stele.loweredWrite' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Stele.loweredWrite

/-- info: 'Draft.Checks.Stele.loweredReceipt' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Stele.loweredReceipt

/-- info: 'Draft.Checks.Stele.loweredObservation' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Stele.loweredObservation

/-- info: 'Draft.Checks.Stele.revertObservation' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Stele.revertObservation

/-- info: 'Draft.Checks.Stele.fallthroughObservation' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Stele.fallthroughObservation
