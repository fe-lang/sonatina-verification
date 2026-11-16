import Stele.Notation
import Frontend.Stele

/-! Functions of a Stele contract, compiled to diagrams.

The contract is in the notation of EquiVM. Each check translates a transition to the typed
fragment, takes the diagram of the result, and runs it with the handler of the operations. The
observation of a run has the returned integer and the values of the first storage slots, the
limit of a loop, a stop at a `revert`, or the reason for which the translation rejects the
transition.

These checks are compiled observations. -/

set_option autoImplicit false

open Prelude

namespace Frontend.Checks

open Stele.Notation

def demo : Stele.ContractDecl := solidity% contract Demo {
  uint256 total;
  uint8 small;
  constructor() payable { }

  function update(uint256 x, uint256 y) external returns (uint256) {
    uint256 z = x * y + 3;
    total = total + z;
    return total - x;
  }

  function larger(uint256 x, uint256 y) external returns (uint256) {
    uint256 m = x;
    if (x < y) { m = y; }
    return m;
  }

  function sum(uint256 k) external returns (uint256) {
    uint256 acc = 0;
    uint256 i = k;
    while (0 < i) { acc = acc + i; i = i - 1; }
    return acc;
  }

  function guarded(uint256 x, uint256 y) external returns (uint256) {
    require(!(y == 0));
    bool ok = true && (x >= y || x != y);
    return x / y;
  }

  function lazy(uint256 x, uint256 y) external returns (uint256) {
    if (y != 0 && x / y == 0) { return 1; }
    return 2;
  }

  function narrow(uint256 x) external returns (uint256) {
    small = x;
    return small;
  }

  function shadow(uint256 x) external returns (uint256) {
    uint256 x = 1;
    return x;
  }

  function leak(uint256 x) external returns (uint256) {
    if (x == 0) { uint256 t = 1; }
    return t;
  }
}

/-- The observation of a run. -/
inductive Observation where
  | returned (value : Int) (slots : List Int)
  | limit
  | reverted
  | rejected (reason : Error)
  deriving BEq, Repr

/-- An argument of a function. -/
inductive Arg where
  | int (n : Int)
  | bool (b : Bool)

/-- The values of a context, from a list of arguments. -/
def values : (Γ : List Ty) → List Arg → Option (All Draft.Stele.Val Γ)
  | [], [] => some .nil
  | .int :: Γ, .int n :: rest => (values Γ rest).map fun vs => .cons (a := Draft.Stele.Ty.int) n vs
  | .bool :: Γ, .bool b :: rest => (values Γ rest).map fun vs => .cons (a := Draft.Stele.Ty.bool) b vs
  | _, _ => none

/-- The run of a transition of the contract, with a number of unrollings of each loop. The
arguments have the value of the call and then the parameters, and the storage has the listed
values at its first slots. -/
def observe (name : String) (n : Nat) (args : List Arg) (slots : List Int) : Observation :=
  match elabFunction demo name with
  | .error reason => .rejected reason
  | .ok f =>
      match values f.context args with
      | none => .rejected .type
      | some vs =>
          match Draft.Stele.run f.body n vs (fun k => slots.getD k 0) with
          | .inl _ => .reverted
          | .inr (none, _) => .limit
          | .inr (some v, s) => .returned v ((List.range slots.length).map s)

-- A declaration, a write of storage, and a read of storage.
#guard observe "update" 0 [.int 0, .int 3, .int 4] [10, 0] == .returned 22 [25, 0]

-- A nonzero value of the call stops at the first `require` of the function.
#guard observe "update" 0 [.int 1, .int 3, .int 4] [10, 0] == .reverted

-- A write of storage reduces the value to 256 bits.
#guard observe "update" 0 [.int 0, .int 1, .int (2 ^ 256 - 1)] [0, 0]
  == .returned 1 [2, 0]

-- An `if` with an assignment in one path.
#guard observe "larger" 0 [.int 0, .int 3, .int 5] [] == .returned 5 []
#guard observe "larger" 0 [.int 0, .int 7, .int 2] [] == .returned 7 []

-- A `while`, with enough unrollings and at the limit.
#guard observe "sum" 5 [.int 0, .int 4] [] == .returned 10 []
#guard observe "sum" 4 [.int 0, .int 4] [] == .limit

-- A `require`, `&&`, `||`, and a division.
#guard observe "guarded" 0 [.int 0, .int 7, .int 2] [] == .returned 3 []
#guard observe "guarded" 0 [.int 0, .int 7, .int 0] [] == .reverted

-- `&&` does not evaluate the division at a zero divisor.
#guard observe "lazy" 0 [.int 0, .int 7, .int 0] [] == .returned 2 []
#guard observe "lazy" 0 [.int 0, .int 1, .int 2] [] == .returned 1 []

-- A write of a storage variable with 8 bits.
#guard observe "narrow" 0 [.int 0, .int 300] [0, 0] == .returned 44 [0, 44]

-- The translation rejects a declaration of a name in scope, and a use after the block of a
-- declaration.
#guard observe "shadow" 0 [.int 0, .int 5] [] == .rejected (.declared "x")
#guard observe "leak" 0 [.int 0, .int 5] [] == .rejected (.unbound "t")

/-- The number of steps of the diagram of a transition. -/
def steps (name : String) : Option Nat :=
  match elabFunction demo name with
  | .error _ => none
  | .ok f => some f.body.diagram.size

#guard steps "update" == some 13
#guard steps "sum" == some 11

end Frontend.Checks
