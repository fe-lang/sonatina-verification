import Prelude

/-! A shape-changing map with genuinely different response types in its branches.
The double call duplicates the first component in the pair branch; it is not an
identity. Tests distinguish that behavior while consuming structural evidence.
-/

set_option autoImplicit false
set_option genInjectivity false
set_option smartUnfolding false

open Prelude

namespace Draft.Checks.Polynomial

open Container

def Ports : Bool → Type
  | false => Nat
  | true => Nat × Nat

def boundary : Container := ⟨Bool, Ports⟩

def swap : Hom boundary boundary where
  shape
    | false => true
    | true => false
  position
    | false, p => p.1
    | true, n => (n, n)

def double : Hom boundary boundary where
  shape := id
  position
    | false, n => n
    | true, p => (p.1, p.1)

def doubleAgree : Hom.Agreement (swap.trans swap) double
  | false => ⟨.refl, fun _ => .refl⟩
  | true => ⟨.refl, fun _ => .refl⟩

def provider (x y : Nat) : Section boundary
  | false => x
  | true => (x, y)

def runFalse (x y : Nat) : Identity ((swap.trans swap).run (provider x y) false) x := .refl

def runTrue (x y : Nat) :
    Identity ((swap.trans swap).run (provider x y) true) (x, x) := .refl

def runCongruence (x y : Nat) :
    Homotopy ((swap.trans swap).run (provider x y)) (double.run (provider x y)) :=
  Hom.runCongr doubleAgree (fun _ => .refl)

/-- Inspect the actual shape path produced by congruence, then route a response. -/
def consumeShapeFalse (x : Nat) :
    Identity (Identity.transport Ports (doubleAgree false).shape x) x := .refl

def consumeShapeTrue (x y : Nat) :
    Identity (Identity.transport Ports (doubleAgree true).shape (x, y)) (x, y) := .refl

/-- Congruence is also consumed by value action; the valuation may be any function. -/
def actFalse (v : Nat → Nat) (x y : Nat) :
    Identity ((swap.apply (⟨false, v⟩ : Ext boundary Nat)).2 (x, y)) (v x) := .refl

def actTrue (v : Nat × Nat → Nat) (x : Nat) :
    Identity ((swap.apply (⟨true, v⟩ : Ext boundary Nat)).2 x) (v (x, x)) := .refl

def consumeActCongruence (v : Nat → Nat) (x : Nat) :
    Identity (Identity.transport (fun n => Fin (n + 1))
      ((doubleAgree.apply (Ext.Agreement.refl (⟨false, v⟩ : Ext boundary Nat))).values x)
      ⟨0, Nat.zero_lt_succ (v x)⟩).val 0 := .refl

def composeCongruence : Hom.Agreement
    ((swap.trans swap).trans (swap.trans swap)) (double.trans double) :=
  Hom.transCongr doubleAgree doubleAgree

def consumeComposedTrue (x y : Nat) :
    Identity (Identity.transport Ports (composeCongruence true).shape (x, y)) (x, y) := .refl

end Draft.Checks.Polynomial
