import Draft.Diagram

/-! A typed fragment of Stele, and its translation to diagrams.

The fragment has integers and booleans. An expression has a context of typed local variables
and a type, and a variable is a position of the context. A statement list has the rest of the
list as a part of each statement. The constructs are those of Stele: literals, variables, a
read of a storage variable, the arithmetic, comparison, and logic operations, division, a
declaration, an assignment to a local variable or to a storage variable, `require`, `if`,
`while`, and `return`. A storage variable is a slot number.

The signature has one operation for each construct that computes. An operation that reads or
writes storage is effectful, and `revert` is an effectful operation with no output case, so no
diagram follows it. Division is pure, and its output boundary has a case for a zero divisor.
A test of a boolean is pure, and its output boundary has two cases.

The translation is a recursion on the syntax. The translation of an expression is a sequence
of steps, with the diagram of the rest as an argument. A table gives the port of the present
value of each local variable. An assignment changes the table, and it adds no step of its own.
The two paths of an `if` exit to one case of the boundary of a continuation, with the present
value of each variable at its ports, and the continuation has the rest. A `while` is a loop
whose entrance has the variables, and its body exits to the entrance or to the continuation
that has the rest. A `return` exits to the boundary of the returned value. -/

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

inductive Compare where
  | eq
  | lt
  | le

inductive Logic where
  | and
  | or

/-- The operations of the fragment. -/
inductive Op where
  | intLit (n : Int)
  | boolLit (b : Bool)
  | arith (f : Arith)
  | div
  | compare (f : Compare)
  | logic (f : Logic)
  | not
  | branch
  | load (slot : Nat)
  | store (slot : Nat)
  | revert

/-- The signature of the fragment. `div` has a case with the quotient and a case for a zero
divisor. `branch` has a case for `true` and a case for `false`. `load` and `store` are
effectful. `revert` is effectful and has no output case. -/
def sig : Signature Ty where
  Op := Op
  kind
    | .intLit _ => .pure
    | .boolLit _ => .pure
    | .arith _ => .pure
    | .div => .pure
    | .compare _ => .pure
    | .logic _ => .pure
    | .not => .pure
    | .branch => .pure
    | .load _ => .effectful
    | .store _ => .effectful
    | .revert => .effectful
  input
    | .intLit _ => []
    | .boolLit _ => []
    | .arith _ => [.int, .int]
    | .div => [.int, .int]
    | .compare _ => [.int, .int]
    | .logic _ => [.bool, .bool]
    | .not => [.bool]
    | .branch => [.bool]
    | .load _ => []
    | .store _ => [.int]
    | .revert => []
  output
    | .intLit _ => .one [.int]
    | .boolLit _ => .one [.bool]
    | .arith _ => .one [.int]
    | .div => [[.int], []]
    | .compare _ => .one [.bool]
    | .logic _ => .one [.bool]
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
  | div (a b : Expr Γ .int) : Expr Γ .int
  | compare (f : Compare) (a b : Expr Γ .int) : Expr Γ .bool
  | logic (f : Logic) (a b : Expr Γ .bool) : Expr Γ .bool
  | not (a : Expr Γ .bool) : Expr Γ .bool

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

/-- The translation of an expression in a context `Δ`, with the port of each local variable.
The diagram of the rest has a context with more ports, the map from each port of `Δ`, and the
port of the value of the expression. The steps of the operands are in order from the left. -/
def Expr.compile {Γ : List Ty} {Qs : Exits Ty} : {t : Ty} → Expr Γ t → (Δ : List Ty) →
    PortMap Δ Γ →
    ((Δ' : List Ty) → ({s : Ty} → Port Δ s → Port Δ' s) → Port Δ' t → Diagram sig Δ' Qs) →
    Diagram sig Δ Qs
  | _, .intLit n, Δ, _, rest =>
      .step ⟨Op.intLit n, .nil⟩ (.one (rest (.int :: Δ) .there .here))
  | _, .boolLit b, Δ, _, rest =>
      .step ⟨Op.boolLit b, .nil⟩ (.one (rest (.bool :: Δ) .there .here))
  | _, .var x, Δ, ρ, rest => rest Δ (fun p => p) (ρ.lookup x)
  | _, .storage slot, Δ, _, rest =>
      .step ⟨Op.load slot, .nil⟩ (.one (rest (.int :: Δ) .there .here))
  | _, .arith f a b, Δ, ρ, rest =>
      a.compile Δ ρ fun Δ₁ up₁ pa =>
        b.compile Δ₁ (ρ.map fun _ p => up₁ p) fun Δ₂ up₂ pb =>
          .step ⟨Op.arith f, .cons (up₂ pa) (.cons pb .nil)⟩
            (.one (rest (.int :: Δ₂) (fun p => .there (up₂ (up₁ p))) .here))
  | _, .div a b, Δ, ρ, rest =>
      a.compile Δ ρ fun Δ₁ up₁ pa =>
        b.compile Δ₁ (ρ.map fun _ p => up₁ p) fun Δ₂ up₂ pb =>
          .step ⟨Op.div, .cons (up₂ pa) (.cons pb .nil)⟩ fun
            | ⟨_, .here⟩ => rest (.int :: Δ₂) (fun p => .there (up₂ (up₁ p))) .here
            | ⟨_, .there .here⟩ => revert
  | _, .compare f a b, Δ, ρ, rest =>
      a.compile Δ ρ fun Δ₁ up₁ pa =>
        b.compile Δ₁ (ρ.map fun _ p => up₁ p) fun Δ₂ up₂ pb =>
          .step ⟨Op.compare f, .cons (up₂ pa) (.cons pb .nil)⟩
            (.one (rest (.bool :: Δ₂) (fun p => .there (up₂ (up₁ p))) .here))
  | _, .logic f a b, Δ, ρ, rest =>
      a.compile Δ ρ fun Δ₁ up₁ pa =>
        b.compile Δ₁ (ρ.map fun _ p => up₁ p) fun Δ₂ up₂ pb =>
          .step ⟨Op.logic f, .cons (up₂ pa) (.cons pb .nil)⟩
            (.one (rest (.bool :: Δ₂) (fun p => .there (up₂ (up₁ p))) .here))
  | _, .not a, Δ, ρ, rest =>
      a.compile Δ ρ fun Δ₁ up₁ pa =>
        .step ⟨Op.not, .cons pa .nil⟩
          (.one (rest (.bool :: Δ₁) (fun p => .there (up₁ p)) .here))

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

/-- A function body: a statement list in the context of its parameters. Each path ends with a
`return` or a `revert`. -/
abbrev Body (Γ : List Ty) : Type := Stmt Γ

/-- The diagram of a function body. Its context has the parameters, and its one exit has the
returned integer. The end of the list is a `revert`. -/
def Stmt.diagram {Γ : List Ty} (body : Stmt Γ) : Diagram sig Γ [Ret] :=
  body.compile .here Γ (PortMap.id Γ) fun _ _ => revert

end Draft.Stele
