import Draft.Diagram
import Draft.Runtime

/-! A typed fragment of Stele, and its translation to diagrams.

The fragment has integers and booleans. An expression has a context of typed local variables
and a type, and a variable is a position of the context. A statement list has the rest of the
list as a part of each statement. The constructs are those of Stele: literals, variables, a
read of a storage variable, the arithmetic and comparison operations, negation, Euclidean
division and remainder, the reduction of an integer to a number of bits, the logic operations,
the conditional expression, a declaration, an assignment to a local variable or to a storage
variable, `require`, `if`, `while`, and `return`. A storage variable is a slot number.

The signature has one operation for each construct that computes. An operation that reads or
writes storage is effectful, and `revert` is an effectful operation with no output case, so no
diagram follows it. Division and remainder are pure, and their output boundary has a case for
a zero divisor. A test of a boolean is pure, and its output boundary has two cases.

The translation is a recursion on the syntax. The translation of an expression is a sequence
of steps, with the diagram of the rest as an argument. The steps of the operands are in order
from the left. `&&`, `||`, and the conditional expression evaluate one of two expressions: the
two paths of a test exit to one case of the boundary of a continuation, with the value and the
ports of the context, and the continuation has the rest.

A table gives the port of the present value of each local variable. An assignment changes the
table, and it adds no step of its own. The two paths of an `if` exit to one case of the
boundary of a continuation, with the present value of each variable at its ports, and the
continuation has the rest. A `while` is a loop whose entrance has the variables, and its body
exits to the entrance or to the continuation that has the rest. A `return` exits to the
boundary of the returned value.

The handler of the operations has the storage as its runtime, and it stops at `revert`. -/

set_option autoImplicit false
set_option genInjectivity false

open Prelude Container

namespace Draft.Stele

/-- The value types of the fragment. -/
inductive Ty where
  | int
  | bool

/-- The values of each type. Integers have no bound. -/
abbrev Val : Ty → Type
  | .int => Int
  | .bool => Bool

inductive Arith where
  | add
  | sub
  | mul

inductive Divide where
  | div
  | mod

inductive Compare where
  | eq
  | ne
  | lt
  | le
  | gt
  | ge

/-- The operations of the fragment. -/
inductive Op where
  | intLit (n : Int)
  | boolLit (b : Bool)
  | arith (f : Arith)
  | divide (f : Divide)
  | neg
  | wrap (bits : Nat)
  | compare (f : Compare)
  | not
  | branch
  | load (slot : Nat)
  | store (slot : Nat)
  | revert

/-- The signature of the fragment. `divide` has a case with the result and a case for a zero
divisor. `wrap` reduces an integer to a number of bits. `branch` has a case for `true` and a
case for `false`. `load` and `store` are effectful. `revert` is effectful and has no output
case. -/
def sig : Signature Ty where
  Op := Op
  kind
    | .intLit _ => .pure
    | .boolLit _ => .pure
    | .arith _ => .pure
    | .divide _ => .pure
    | .neg => .pure
    | .wrap _ => .pure
    | .compare _ => .pure
    | .not => .pure
    | .branch => .pure
    | .load _ => .effectful
    | .store _ => .effectful
    | .revert => .effectful
  input
    | .intLit _ => []
    | .boolLit _ => []
    | .arith _ => [.int, .int]
    | .divide _ => [.int, .int]
    | .neg => [.int]
    | .wrap _ => [.int]
    | .compare _ => [.int, .int]
    | .not => [.bool]
    | .branch => [.bool]
    | .load _ => []
    | .store _ => [.int]
    | .revert => []
  output
    | .intLit _ => .one [.int]
    | .boolLit _ => .one [.bool]
    | .arith _ => .one [.int]
    | .divide _ => [[.int], []]
    | .neg => .one [.int]
    | .wrap _ => .one [.int]
    | .compare _ => .one [.bool]
    | .not => .one [.bool]
    | .branch => [[], []]
    | .load _ => .one [.int]
    | .store _ => .one []
    | .revert => []

/-- An expression with a context of local variables and a type. -/
inductive Expr (Γ : List Ty) : Ty → Type where
  | intLit (n : Int) : Expr Γ .int
  | boolLit (b : Bool) : Expr Γ .bool
  | var {t : Ty} (x : Port Γ t) : Expr Γ t
  | storage (slot : Nat) : Expr Γ .int
  | arith (f : Arith) (a b : Expr Γ .int) : Expr Γ .int
  | divide (f : Divide) (a b : Expr Γ .int) : Expr Γ .int
  | neg (a : Expr Γ .int) : Expr Γ .int
  | wrap (bits : Nat) (a : Expr Γ .int) : Expr Γ .int
  | compare (f : Compare) (a b : Expr Γ .int) : Expr Γ .bool
  | not (a : Expr Γ .bool) : Expr Γ .bool
  | and (a b : Expr Γ .bool) : Expr Γ .bool
  | or (a b : Expr Γ .bool) : Expr Γ .bool
  | ite {t : Ty} (c : Expr Γ .bool) (a b : Expr Γ t) : Expr Γ t

/-- A statement list with a context of local variables. Each statement has the rest of the
list. A declaration adds a variable for the rest of its list. -/
inductive Stmt : List Ty → Type where
  | skip {Γ : List Ty} : Stmt Γ
  | letDecl {Γ : List Ty} {t : Ty} (e : Expr Γ t) (rest : Stmt (t :: Γ)) : Stmt Γ
  | assign {Γ : List Ty} {t : Ty} (x : Port Γ t) (e : Expr Γ t) (rest : Stmt Γ) : Stmt Γ
  | assignStorage {Γ : List Ty} (slot : Nat) (e : Expr Γ .int) (rest : Stmt Γ) : Stmt Γ
  | require {Γ : List Ty} (e : Expr Γ .bool) (rest : Stmt Γ) : Stmt Γ
  | ite {Γ : List Ty} (c : Expr Γ .bool) (yes no rest : Stmt Γ) : Stmt Γ
  | whileDo {Γ : List Ty} (c : Expr Γ .bool) (body rest : Stmt Γ) : Stmt Γ
  | ret {Γ : List Ty} (e : Expr Γ .int) : Stmt Γ

/-- The boundary of a return: one case with the returned integer. -/
abbrev Ret : Boundary Ty := .one [.int]

/-- The step of `revert`. No diagram follows it. -/
def revert {Δ : List Ty} {Qs : Exits Ty} : Diagram sig Δ Qs :=
  .step ⟨Op.revert, .nil⟩ fun c => c.2.ofNil

/-- The exit of a path of a test to the boundary of the continuation of the test, with a value
and the ports of the context of the test. -/
def join {Δ Δ' : List Ty} {t : Ty} {Qs : Exits Ty} (up : {s : Ty} → Port Δ s → Port Δ' s)
    (p : Port Δ' t) : Diagram sig Δ' (.one (t :: Δ) :: Qs) :=
  .exit (Exits.At.here ⟨Boundary.only (t :: Δ), .cons p ((PortMap.id Δ).map fun _ q => up q)⟩)

/-- The translation of an expression in a context `Δ`, with the port of each local variable.
The diagram of the rest has a context with more ports, the map from each port of `Δ`, and the
port of the value of the expression. -/
def Expr.compile {Γ : List Ty} : {t : Ty} → Expr Γ t → {Qs : Exits Ty} → (Δ : List Ty) →
    PortMap Δ Γ →
    ((Δ' : List Ty) → ({s : Ty} → Port Δ s → Port Δ' s) → Port Δ' t → Diagram sig Δ' Qs) →
    Diagram sig Δ Qs
  | _, .intLit n, _, Δ, _, rest =>
      .step ⟨Op.intLit n, .nil⟩ (.one (rest (.int :: Δ) .there .here))
  | _, .boolLit b, _, Δ, _, rest =>
      .step ⟨Op.boolLit b, .nil⟩ (.one (rest (.bool :: Δ) .there .here))
  | _, .var x, _, Δ, ρ, rest => rest Δ (fun p => p) (ρ.lookup x)
  | _, .storage slot, _, Δ, _, rest =>
      .step ⟨Op.load slot, .nil⟩ (.one (rest (.int :: Δ) .there .here))
  | _, .arith f a b, _, Δ, ρ, rest =>
      a.compile Δ ρ fun Δ₁ up₁ pa =>
        b.compile Δ₁ (ρ.map fun _ p => up₁ p) fun Δ₂ up₂ pb =>
          .step ⟨Op.arith f, .cons (up₂ pa) (.cons pb .nil)⟩
            (.one (rest (.int :: Δ₂) (fun p => .there (up₂ (up₁ p))) .here))
  | _, .divide f a b, _, Δ, ρ, rest =>
      a.compile Δ ρ fun Δ₁ up₁ pa =>
        b.compile Δ₁ (ρ.map fun _ p => up₁ p) fun Δ₂ up₂ pb =>
          .step ⟨Op.divide f, .cons (up₂ pa) (.cons pb .nil)⟩ fun
            | ⟨_, .here⟩ => rest (.int :: Δ₂) (fun p => .there (up₂ (up₁ p))) .here
            | ⟨_, .there .here⟩ => revert
  | _, .neg a, _, Δ, ρ, rest =>
      a.compile Δ ρ fun Δ₁ up₁ pa =>
        .step ⟨Op.neg, .cons pa .nil⟩
          (.one (rest (.int :: Δ₁) (fun p => .there (up₁ p)) .here))
  | _, .wrap bits a, _, Δ, ρ, rest =>
      a.compile Δ ρ fun Δ₁ up₁ pa =>
        .step ⟨Op.wrap bits, .cons pa .nil⟩
          (.one (rest (.int :: Δ₁) (fun p => .there (up₁ p)) .here))
  | _, .compare f a b, _, Δ, ρ, rest =>
      a.compile Δ ρ fun Δ₁ up₁ pa =>
        b.compile Δ₁ (ρ.map fun _ p => up₁ p) fun Δ₂ up₂ pb =>
          .step ⟨Op.compare f, .cons (up₂ pa) (.cons pb .nil)⟩
            (.one (rest (.bool :: Δ₂) (fun p => .there (up₂ (up₁ p))) .here))
  | _, .not a, _, Δ, ρ, rest =>
      a.compile Δ ρ fun Δ₁ up₁ pa =>
        .step ⟨Op.not, .cons pa .nil⟩
          (.one (rest (.bool :: Δ₁) (fun p => .there (up₁ p)) .here))
  | _, .and a b, _, Δ, ρ, rest =>
      a.compile Δ ρ fun Δ₁ up₁ pa =>
        .seq
          (.step ⟨Op.branch, .cons pa .nil⟩ fun
            | ⟨_, .here⟩ =>
                b.compile Δ₁ (ρ.map fun _ p => up₁ p) fun _ up₂ pb => join up₂ pb
            | ⟨_, .there .here⟩ =>
                .step ⟨Op.boolLit false, .nil⟩ (.one (join .there .here)))
          (.one (rest (.bool :: Δ₁) (fun p => .there (up₁ p)) .here))
  | _, .or a b, _, Δ, ρ, rest =>
      a.compile Δ ρ fun Δ₁ up₁ pa =>
        .seq
          (.step ⟨Op.branch, .cons pa .nil⟩ fun
            | ⟨_, .here⟩ => .step ⟨Op.boolLit true, .nil⟩ (.one (join .there .here))
            | ⟨_, .there .here⟩ =>
                b.compile Δ₁ (ρ.map fun _ p => up₁ p) fun _ up₂ pb => join up₂ pb)
          (.one (rest (.bool :: Δ₁) (fun p => .there (up₁ p)) .here))
  | t, .ite c a b, _, Δ, ρ, rest =>
      c.compile Δ ρ fun Δ₁ up₁ pc =>
        .seq
          (.step ⟨Op.branch, .cons pc .nil⟩ fun
            | ⟨_, .here⟩ =>
                a.compile Δ₁ (ρ.map fun _ p => up₁ p) fun _ up₂ pa => join up₂ pa
            | ⟨_, .there .here⟩ =>
                b.compile Δ₁ (ρ.map fun _ p => up₁ p) fun _ up₂ pb => join up₂ pb)
          (.one (rest (t :: Δ₁) (fun p => .there (up₁ p)) .here))

/-- The translation of a statement list in a context `Δ`, with the port of each local
variable and the position of the boundary of a return. The diagram of the end of the list has a
context with more ports and the port of each local variable. -/
def Stmt.compile : {Γ : List Ty} → Stmt Γ → {Qs : Exits Ty} → Elem Ret Qs → (Δ : List Ty) →
    PortMap Δ Γ → ((Δ' : List Ty) → PortMap Δ' Γ → Diagram sig Δ' Qs) → Diagram sig Δ Qs
  | _, .skip, _, _, Δ, ρ, fall => fall Δ ρ
  | _, .letDecl e rest, _, out, Δ, ρ, fall =>
      e.compile Δ ρ fun Δ' up p =>
        rest.compile out Δ' (.cons p (ρ.map fun _ q => up q)) fun Δ'' ρ' => fall Δ'' ρ'.tail
  | _, .assign x e rest, _, out, Δ, ρ, fall =>
      e.compile Δ ρ fun Δ' up p =>
        rest.compile out Δ' ((ρ.map fun _ q => up q).set x p) fall
  | _, .assignStorage slot e rest, _, out, Δ, ρ, fall =>
      e.compile Δ ρ fun Δ' up p =>
        .step ⟨Op.store slot, .cons p .nil⟩
          (.one (rest.compile out Δ' (ρ.map fun _ q => up q) fall))
  | _, .require e rest, _, out, Δ, ρ, fall =>
      e.compile Δ ρ fun Δ' up p =>
        .step ⟨Op.branch, .cons p .nil⟩ fun
          | ⟨_, .here⟩ => rest.compile out Δ' (ρ.map fun _ q => up q) fall
          | ⟨_, .there .here⟩ => revert
  | Γ, .ite c yes no rest, _, out, Δ, ρ, fall =>
      .seq
        (c.compile Δ ρ fun Δ' up p =>
          .step ⟨Op.branch, .cons p .nil⟩ fun
            | ⟨_, .here⟩ =>
                yes.compile (.there out) Δ' (ρ.map fun _ q => up q) fun _ ρ' =>
                  .exit (Exits.At.here ⟨Boundary.only Γ, ρ'⟩)
            | ⟨_, .there .here⟩ =>
                no.compile (.there out) Δ' (ρ.map fun _ q => up q) fun _ ρ' =>
                  .exit (Exits.At.here ⟨Boundary.only Γ, ρ'⟩))
        (.one (rest.compile out Γ (PortMap.id Γ) fall))
  | Γ, .whileDo c body rest, _, out, _, ρ, fall =>
      .seq
        (.seq (.exit (Exits.At.here ⟨Boundary.only Γ, ρ⟩))
          (.loop (.one
            (c.compile Γ (PortMap.id Γ) fun Δ' up p =>
              .step ⟨Op.branch, .cons p .nil⟩ fun
                | ⟨_, .here⟩ =>
                    body.compile (.there (.there out)) Δ' ((PortMap.id Γ).map fun _ q => up q)
                      fun _ ρ' => .exit (Exits.At.here ⟨Boundary.only Γ, ρ'⟩)
                | ⟨_, .there .here⟩ =>
                    .exit ⟨_, .there .here, Boundary.only Γ,
                      (PortMap.id Γ).map fun _ q => up q⟩))))
        (.one (rest.compile out Γ (PortMap.id Γ) fall))
  | _, .ret e, _, out, Δ, ρ, _ =>
      e.compile Δ ρ fun _ _ p => .exit ⟨_, out, Boundary.only _, .cons p .nil⟩

/-- The diagram of a function body. Its context has the parameters, and its one exit has the
returned integer. The end of the list is a `revert`. -/
def Stmt.diagram {Γ : List Ty} (body : Stmt Γ) : Diagram sig Γ [Ret] :=
  body.compile .here Γ (PortMap.id Γ) fun _ _ => revert

/-! The handler of the operations. -/

/-- The runtime: the value of each storage slot. -/
abbrev Store : Type := Nat → Int

/-- The storage with a new value at one slot. -/
def Store.write (s : Store) (slot : Nat) (v : Int) : Store :=
  fun k => cond (Nat.beq k slot) v (s k)

/-- The response with one value. -/
def one {t : Ty} (v : Val t) : (Boundary.one [t]).At Val := ⟨Boundary.only _, .cons v .nil⟩

def evalArith : Arith → Int → Int → Int
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b

/-- Euclidean division and remainder. -/
def evalDivide : Divide → Int → Int → Int
  | .div, a, b => a / b
  | .mod, a, b => a % b

def evalCompare : Compare → Int → Int → Bool
  | .eq, a, b => decide (a = b)
  | .ne, a, b => !decide (a = b)
  | .lt, a, b => decide (a < b)
  | .le, a, b => decide (a ≤ b)
  | .gt, a, b => decide (a > b)
  | .ge, a, b => decide (a ≥ b)

/-- An integer reduced to a number of bits: the remainder of the division by that power of
two. -/
def wrap (bits : Nat) (a : Int) : Int := a % ((2 ^ bits : Nat) : Int)

/-- The handler of the operations, with the storage as its runtime. `divide` has the second
case at a zero divisor. `load` and `store` read and write one slot. `revert` stops. -/
def handle : Handler (sig.interface Val) Store Unit
  | ⟨.intLit n, _⟩, s => .inr (one (t := .int) n, s)
  | ⟨.boolLit b, _⟩, s => .inr (one (t := .bool) b, s)
  | ⟨.arith f, args⟩, s =>
      .inr (one (t := .int) (evalArith f (args.lookup .here) (args.lookup (.there .here))), s)
  | ⟨.divide f, args⟩, s =>
      match decide ((args.lookup (.there .here) : Int) = 0) with
      | true => .inr (⟨⟨_, .there .here⟩, .nil⟩, s)
      | false =>
          .inr (⟨⟨_, .here⟩,
            .cons (evalDivide f (args.lookup .here) (args.lookup (.there .here))) .nil⟩, s)
  | ⟨.neg, args⟩, s => .inr (one (t := .int) (-(args.lookup .here : Int)), s)
  | ⟨.wrap bits, args⟩, s => .inr (one (t := .int) (wrap bits (args.lookup .here)), s)
  | ⟨.compare f, args⟩, s =>
      .inr (one (t := .bool) (evalCompare f (args.lookup .here) (args.lookup (.there .here))), s)
  | ⟨.not, args⟩, s => .inr (one (t := .bool) (!(args.lookup .here : Bool)), s)
  | ⟨.branch, args⟩, s =>
      match (args.lookup .here : Bool) with
      | true => .inr (⟨⟨_, .here⟩, .nil⟩, s)
      | false => .inr (⟨⟨_, .there .here⟩, .nil⟩, s)
  | ⟨.load slot, _⟩, s => .inr (one (t := .int) (s slot), s)
  | ⟨.store slot, args⟩, s => .inr (⟨Boundary.only _, .nil⟩, s.write slot (args.lookup .here))
  | ⟨.revert, _⟩, _ => .inl ()

/-- The returned integer of the one exit. -/
def returned : Exits.At [Ret] Val → Int
  | ⟨_, .here, ⟨_, .here⟩, out⟩ => out.lookup .here

/-- The run of a function body with a number of unrollings of each loop, from the arguments
and a storage: a stop at a `revert`, or the returned integer with the last storage. The
integer has no value at the limit of a loop. -/
def run {Γ : List Ty} (body : Stmt Γ) (n : Nat) (args : All Val Γ) (s : Store) :
    Unit ⊕ (Option Int × Store) :=
  handle.run (body.diagram.run (.pure none) n args fun r => .pure (some (returned r))) s

end Draft.Stele
