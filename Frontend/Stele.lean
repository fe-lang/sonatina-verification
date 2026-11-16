import Stele
import Draft.Stele

/-! The translation from the Stele syntax of EquiVM to the typed fragment.

The translation resolves each name and checks each type. A local variable is a position of the
context of the fragment, and a storage variable is a slot: the position of its declaration in
the contract. The value of the call is a variable with no name, at the first position of the
context of a function, and the parameters follow it in the order of their declarations.

The fragment covers the integer types and `bool` for parameters and local variables, and the
unsigned integer types for storage variables. A write of a storage variable reduces the value
to the bits of the variable, as the storage of Stele does.

The locals of Stele are one map for a function, and a declaration in a block stays after the
block. The fragment ends the scope of a declaration with its block. The translation rejects a
declaration of a name that is in scope, and a use of a name after the block of its declaration
has no variable. For a program that the translation accepts, the two rules give the same
variable for each use.

A function of the fragment returns one integer, and its body ends with a `return`. -/

set_option autoImplicit false
set_option backward.match.sparseCases false

open Prelude

namespace Frontend

abbrev Ty := Draft.Stele.Ty
abbrev Port := @Draft.Port Ty
abbrev FExpr := Draft.Stele.Expr
abbrev FStmt := Draft.Stele.Stmt

instance : DecidableEq Ty
  | .int, .int => isTrue rfl
  | .bool, .bool => isTrue rfl
  | .int, .bool => isFalse nofun
  | .bool, .int => isFalse nofun

/-- The reasons for which the translation rejects a program. -/
inductive Error where
  /-- A use of a name that is not a local variable in scope. -/
  | unbound (name : String)
  /-- A declaration of a name that is in scope. -/
  | declared (name : String)
  /-- A use of the value of the call out of a function. -/
  | noCallvalue
  /-- A reference to storage that is not a storage variable with an unsigned integer type. -/
  | storage (name : String)
  /-- A reference to a part of a local variable. -/
  | localRef (name : String)
  /-- A storage variable with a type that is not in the fragment. -/
  | storageType (name : String)
  | notInt
  | notBool
  /-- A declaration whose type differs from the type of its expression. -/
  | declType (name : String)
  /-- An assignment whose expression has a different type from its variable. -/
  | assignType (name : String)
  /-- A conditional expression whose two cases have different types. -/
  | branchTypes
  /-- A type, an operation, an expression, or a statement that is not in the fragment. -/
  | type
  | operation
  | expression
  | statement
  /-- A function that does not return one integer. -/
  | returnType
  /-- A function whose body does not end with a `return` of one value. -/
  | noReturn
  | noTransition (name : String)
  deriving BEq, Repr

/-- The name of each local variable of a context. The variable of the value of the call has no
name. -/
abbrev Names (Γ : List Ty) : Type := All (fun _ : Ty => Option String) Γ

/-- The variable with a name: its type and its position. -/
def Names.find : {Γ : List Ty} → Names Γ → String → Option ((t : Ty) × Port Γ t)
  | [], _, _ => none
  | t :: _, names, x =>
      if names.head == some x then some ⟨t, .here⟩
      else (find names.tail x).map fun r => ⟨r.1, .there r.2⟩

/-- The scope of a translation: the names of the local variables, the storage variables in the
order of their declarations with their bits, and the variable of the value of the call. -/
structure Scope (Γ : List Ty) where
  names : Names Γ
  slots : List (String × Nat)
  callvalue : Option (Port Γ .int)

/-- The scope with one more local variable. -/
def Scope.push {Γ : List Ty} (scope : Scope Γ) (x : String) (t : Ty) : Scope (t :: Γ) where
  names := .cons (some x) scope.names
  slots := scope.slots
  callvalue := scope.callvalue.map .there

/-- The slot and the bits of a storage variable. -/
def slotOf : List (String × Nat) → String → Option (Nat × Nat)
  | [], _ => none
  | (y, bits) :: rest, x =>
      if x == y then some (0, bits) else (slotOf rest x).map fun r => (r.1 + 1, r.2)

/-- The type of the fragment for a type of a parameter or of a local variable. -/
def elabType : ABI.ABIType → Except Error Ty
  | .elem (.int _) => .ok .int
  | .elem .bool => .ok .bool
  | _ => .error .type

abbrev Typed (Γ : List Ty) : Type := (t : Ty) × FExpr Γ t

def asInt {Γ : List Ty} : Typed Γ → Except Error (FExpr Γ .int)
  | ⟨.int, e⟩ => .ok e
  | ⟨.bool, _⟩ => .error .notInt

def asBool {Γ : List Ty} : Typed Γ → Except Error (FExpr Γ .bool)
  | ⟨.bool, e⟩ => .ok e
  | ⟨.int, _⟩ => .error .notBool

/-- The expression of an operation with two operands. -/
def elabBinary {Γ : List Ty} : Stele.BinaryOp → Typed Γ → Typed Γ → Except Error (Typed Γ)
  | .add, a, b => do pure ⟨.int, .arith .add (← asInt a) (← asInt b)⟩
  | .sub, a, b => do pure ⟨.int, .arith .sub (← asInt a) (← asInt b)⟩
  | .mul, a, b => do pure ⟨.int, .arith .mul (← asInt a) (← asInt b)⟩
  | .div, a, b => do pure ⟨.int, .divide .div (← asInt a) (← asInt b)⟩
  | .mod, a, b => do pure ⟨.int, .divide .mod (← asInt a) (← asInt b)⟩
  | .eq, a, b => do pure ⟨.bool, .compare .eq (← asInt a) (← asInt b)⟩
  | .ne, a, b => do pure ⟨.bool, .compare .ne (← asInt a) (← asInt b)⟩
  | .lt, a, b => do pure ⟨.bool, .compare .lt (← asInt a) (← asInt b)⟩
  | .le, a, b => do pure ⟨.bool, .compare .le (← asInt a) (← asInt b)⟩
  | .gt, a, b => do pure ⟨.bool, .compare .gt (← asInt a) (← asInt b)⟩
  | .ge, a, b => do pure ⟨.bool, .compare .ge (← asInt a) (← asInt b)⟩
  | .and, a, b => do pure ⟨.bool, .and (← asBool a) (← asBool b)⟩
  | .or, a, b => do pure ⟨.bool, .or (← asBool a) (← asBool b)⟩
  | _, _, _ => .error .operation

/-- The expression of the fragment for an expression of Stele, with its type. -/
def elabExpr {Γ : List Ty} (scope : Scope Γ) : Stele.Expr → Except Error (Typed Γ)
  | .intLit n => .ok ⟨.int, .intLit n⟩
  | .boolLit b => .ok ⟨.bool, .boolLit b⟩
  | .var x =>
      match scope.names.find x with
      | some r => .ok ⟨r.1, .var r.2⟩
      | none => .error (.unbound x)
  | .env .callvalue =>
      match scope.callvalue with
      | some p => .ok ⟨.int, .var p⟩
      | none => .error .noCallvalue
  | .storage ref =>
      match ref.steps, slotOf scope.slots ref.base with
      | [], some r => .ok ⟨.int, .storage r.1⟩
      | _, _ => .error (.storage ref.base)
  | .unary .not a => do pure ⟨.bool, .not (← asBool (← elabExpr scope a))⟩
  | .unary .neg a => do pure ⟨.int, .neg (← asInt (← elabExpr scope a))⟩
  | .binary op a b => do elabBinary op (← elabExpr scope a) (← elabExpr scope b)
  | .ite c a b => do
      let c' ← asBool (← elabExpr scope c)
      let a' ← elabExpr scope a
      let b' ← elabExpr scope b
      if h : a'.1 = b'.1 then pure ⟨b'.1, .ite c' (h ▸ a'.2) b'.2⟩
      else throw .branchTypes
  | .cast e (.elem (.int (.uint bits))) => do
      pure ⟨.int, .wrap bits.val (← asInt (← elabExpr scope e))⟩
  | _ => .error .expression

mutual

/-- The statement list of the fragment for one statement of Stele, with the translation of the
rest of its list in a scope. -/
def elabStmt : {Γ : List Ty} → Scope Γ → Stele.Stmt →
    ({Γ' : List Ty} → Scope Γ' → Except Error (FStmt Γ')) → Except Error (FStmt Γ)
  | _, scope, .letDecl x ty e, rest => do
      if (scope.names.find x).isSome then
        throw (.declared x)
      let e' ← elabExpr scope e
      match ty with
      | some ty =>
          if (← elabType ty) ≠ e'.1 then
            throw (.declType x)
      | none => pure ()
      pure (.letDecl e'.2 (← rest (scope.push x e'.1)))
  | _, scope, .assign .localVar ref e, rest => do
      match ref.steps, scope.names.find ref.base with
      | [], some r =>
          let e' ← elabExpr scope e
          if h : e'.1 = r.1 then pure (.assign r.2 (h ▸ e'.2) (← rest scope))
          else throw (.assignType ref.base)
      | _, _ => throw (.localRef ref.base)
  | _, scope, .assign .storage ref e, rest => do
      match ref.steps, slotOf scope.slots ref.base with
      | [], some r =>
          let e' ← asInt (← elabExpr scope e)
          pure (.assignStorage r.1 (.wrap r.2 e') (← rest scope))
      | _, _ => throw (.storage ref.base)
  | _, scope, .require e, rest => do
      pure (.require (← asBool (← elabExpr scope e)) (← rest scope))
  | _, scope, .ite c yes no, rest => do
      pure (.ite (← asBool (← elabExpr scope c)) (← elabStmts scope yes) (← elabStmts scope no)
        (← rest scope))
  | _, scope, .while c body, rest => do
      pure (.whileDo (← asBool (← elabExpr scope c)) (← elabStmts scope body) (← rest scope))
  | _, scope, .return [e], _ => do pure (.ret (← asInt (← elabExpr scope e)))
  | _, _, _, _ => .error .statement

/-- The statement list of the fragment for a statement list of Stele. -/
def elabStmts : {Γ : List Ty} → Scope Γ → List Stele.Stmt → Except Error (FStmt Γ)
  | _, _, [] => .ok .skip
  | _, scope, s :: rest => elabStmt scope s fun scope' => elabStmts scope' rest

end

/-- The parameters of a function: the context of their types, and their names. -/
def elabParams : List Stele.Param → Except Error ((Γ : List Ty) × Names Γ)
  | [] => .ok ⟨[], .nil⟩
  | p :: rest => do
      let t ← elabType p.ty
      let r ← elabParams rest
      pure ⟨t :: r.1, .cons (some p.name) r.2⟩

/-- The storage variables of a contract, with their bits. -/
def elabSlots : List Stele.StorageDecl → Except Error (List (String × Nat))
  | [] => .ok []
  | d :: rest =>
      match d.ty with
      | .elem (.int (.uint bits)) => do pure ((d.name, bits.val) :: (← elabSlots rest))
      | _ => .error (.storageType d.name)

/-- A statement list ends with a `return` of one value. -/
def endsWithReturn : List Stele.Stmt → Bool
  | [] => false
  | [.return [_]] => true
  | _ :: rest => endsWithReturn rest

/-- A function of the fragment: the context of its arguments, and its body. -/
structure Function where
  context : List Ty
  body : FStmt context

/-- The function of the fragment for a transition of a contract. The context has the value of
the call, and then the parameters. -/
def elabTransition (contract : Stele.ContractDecl) (t : Stele.TransitionDecl) :
    Except Error Function := do
  let slots ← elabSlots contract.storage
  let params ← elabParams t.params
  match t.returnType with
  | [ty] =>
      if (← elabType ty) ≠ .int then throw .returnType
  | _ => throw .returnType
  if !endsWithReturn t.body then throw .noReturn
  let scope : Scope (.int :: params.1) :=
    { names := .cons none params.2, slots := slots, callvalue := some .here }
  pure ⟨.int :: params.1, ← elabStmts scope t.body⟩

/-- The function of the fragment for the transition of a contract with a name. -/
def elabFunction (contract : Stele.ContractDecl) (name : String) : Except Error Function :=
  match contract.transitions.find? (·.name == name) with
  | some t => elabTransition contract t
  | none => .error (.noTransition name)

end Frontend

/-- info: 'Frontend.elabFunction' does not depend on any axioms -/
#guard_msgs in
#print axioms Frontend.elabFunction
