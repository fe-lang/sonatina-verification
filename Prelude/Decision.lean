import Prelude.Identity

/-! Decisions carrying Type-valued evidence. -/

set_option autoImplicit false
set_option genInjectivity false

universe u v

namespace Prelude

abbrev Refute (α : Type u) := α → Empty

inductive Dec (α : Type u) : Type u where
  | yes : α → Dec α
  | no : Refute α → Dec α

namespace Dec

variable {α : Type u} {β : Type v}

def isYes : Dec α → Bool
  | .yes _ => true
  | .no _ => false

/-- Transport a decision along maps in both directions. -/
def map (f : α → β) (g : β → α) : Dec α → Dec β
  | .yes a => .yes (f a)
  | .no refute => .no (fun b => refute (g b))

def product (a : Dec α) (b : Dec β) : Dec (α × β) :=
  match a, b with
  | .yes x, .yes y => .yes (x, y)
  | .no refute, _ => .no (fun p => refute p.1)
  | _, .no refute => .no (fun p => refute p.2)

def sum (a : Dec α) (b : Dec β) : Dec (Sum α β) :=
  match a, b with
  | .yes x, _ => .yes (.inl x)
  | _, .yes y => .yes (.inr y)
  | .no na, .no nb => .no (fun s => match s with
      | .inl x => na x
      | .inr y => nb y)

def negate : Dec α → Dec (Refute α)
  | .yes a => .no (fun refute => refute a)
  | .no refute => .yes refute

/-- Decide inhabitation without extracting data from a Prop-valued existential. -/
def toDecidable : Dec α → Decidable (Nonempty α)
  | .yes a => isTrue ⟨a⟩
  | .no refute => isFalse (fun ⟨a⟩ => (refute a).elim)

def ofDecidable (p : Prop) [Decidable p] : Dec (PLift p) :=
  if h : p then .yes ⟨h⟩ else .no (fun x => (h x.down).elim)

def toPropDecidable {p : Prop} : Dec (PLift p) → Decidable p
  | .yes x => isTrue x.down
  | .no refute => isFalse (fun h => (refute ⟨h⟩).elim)

/-- The identity proof of a decision of an identity. It does not use the given proof when the
decision has a proof. -/
def path {a b : α} : Dec (a ≡ b) → a ≡ b → a ≡ b
  | .yes q, _ => q
  | .no refute, p => (refute p).elim

/-- The identity proof of a decision is the same for each given proof. -/
def pathSame {a b : α} : (d : Dec (a ≡ b)) → (p q : a ≡ b) → path d p ≡ path d q
  | .yes _, _, _ => .refl
  | .no refute, p, _ => (refute p).elim

/-- An identity proof is the composite of the two identity proofs of a decision. -/
def pathSplit (dec : (x y : α) → Dec (x ≡ y)) {a b : α} (p : a ≡ b) :
    p ≡ (path (dec a a) .refl).symm.trans (path (dec a b) p) :=
  Identity.ind
    (fun (b : α) (p : a ≡ b) => p ≡ (path (dec a a) .refl).symm.trans (path (dec a b) p))
    (Identity.symmTrans (path (dec a a) .refl)).symm p

/-- Each identity type of a type with a decision of identity is a proposition. -/
def unique (dec : (x y : α) → Dec (x ≡ y)) {a b : α} : IsProp (a ≡ b) := fun p q =>
  (pathSplit dec p).trans
    ((Identity.cong (fun r => (path (dec a a) .refl).symm.trans r)
        (pathSame (dec a b) p q)).trans
      (pathSplit dec q).symm)

/-- The decision of the identity of an element with itself is the reflexivity. -/
def yesRefl (dec : (x y : α) → Dec (x ≡ y)) (x : α) : dec x x ≡ .yes .refl :=
  let self : (d : Dec (x ≡ x)) → d ≡ .yes .refl
    | .yes p => Identity.cong Dec.yes (unique dec p .refl)
    | .no refute => (refute .refl).elim
  self (dec x x)

/-- The transport of a value of a family along a decision of identity: the transported value
when the decision has an identity proof, and no value when it has none. -/
def transport? {a b : α} (P : α → Type v) (x : P a) : Dec (a ≡ b) → Option (P b)
  | .yes p => some (Identity.transport P p x)
  | .no _ => none

/-- The decision of the identity of two dependent pairs, from a decision for the first
components and a decision for the second components over each first component. -/
def sigma {P : α → Type v} (base : (a b : α) → Dec (a ≡ b))
    (fiber : (a : α) → (x y : P a) → Dec (x ≡ y)) (x y : Sigma P) : Dec (x ≡ y) :=
  match base x.1 y.1 with
  | .no refute => .no fun p => refute (Identity.cong Sigma.fst p)
  | .yes p =>
      (fiber y.1 (Identity.transport P p x.2) y.2).map (Identity.sigma p) fun q =>
        (Identity.cong (fun path => Identity.transport P path x.2)
          (unique base p (Identity.cong Sigma.fst q))).trans (Identity.sigmaSnd q)

end Dec

/-- Decidable internal identity. -/
class DecEq (α : Type u) where
  decEq : (a b : α) → Dec (a ≡ b)

def decideEq {α : Type u} [DecEq α] (a b : α) : Dec (a ≡ b) := DecEq.decEq a b

/-! Instances by structural recursion. Each refutation transports an inhabitant
of `Unit` into `Empty` along the offered identity. The `Nat` instance is unary:
its cost is linear in the smaller argument. -/

namespace DecEq

variable {α : Type u} {β : Type v}

instance : DecEq Unit where
  decEq _ _ := .yes .refl

instance : DecEq Bool where
  decEq
    | false, false => .yes .refl
    | true, true => .yes .refl
    | false, true => .no (fun p => Identity.transport (fun b => bif b then Empty else Unit) p ())
    | true, false => .no (fun p => Identity.transport (fun b => bif b then Unit else Empty) p ())

def nat : (a b : Nat) → Dec (a ≡ b)
  | 0, 0 => .yes .refl
  | 0, _ + 1 => .no (fun p => Identity.transport (Nat.rec Unit fun _ _ => Empty) p ())
  | _ + 1, 0 => .no (fun p => Identity.transport (Nat.rec Empty fun _ _ => Unit) p ())
  | a + 1, b + 1 => (nat a b).map (Identity.cong Nat.succ) (Identity.cong Nat.pred)

instance : DecEq Nat := ⟨nat⟩

instance : DecEq Int where
  decEq x y := by
    cases x <;> cases y
    all_goals first
      | exact (decideEq _ _).map (Identity.cong _) (fun p => by cases p; exact .refl)
      | exact .no fun p => by cases p

/-- Equal values give equal elements of `Fin n`; the bound is a proposition. -/
def finExt {n : Nat} : {a b : Fin n} → a.val ≡ b.val → a ≡ b
  | ⟨x, hx⟩, ⟨_, hy⟩, p =>
    Identity.ind (fun y _ => (hy : y < n) → (⟨x, hx⟩ : Fin n) ≡ ⟨y, hy⟩) (fun _ => .refl) p hy

instance {n : Nat} : DecEq (Fin n) where
  decEq a b := (nat a.val b.val).map finExt (Identity.cong Fin.val)

instance [DecEq α] : DecEq (Option α) where
  decEq
    | none, none => .yes .refl
    | some a, some b => (decideEq a b).map (Identity.cong some) Identity.someInject
    | none, some _ => .no (fun p => Identity.transport
        (fun o => match o with | none => Unit | some _ => Empty) p ())
    | some _, none => .no (fun p => Identity.transport
        (fun o => match o with | none => Empty | some _ => Unit) p ())

instance [DecEq α] [DecEq β] : DecEq (Sum α β) where
  decEq
    | .inl a, .inl b => (decideEq a b).map (Identity.cong Sum.inl) Identity.inlInject
    | .inr a, .inr b => (decideEq a b).map (Identity.cong Sum.inr) Identity.inrInject
    | .inl _, .inr _ => .no (fun p => Identity.transport
        (fun s => match s with | .inl _ => Unit | .inr _ => Empty) p ())
    | .inr _, .inl _ => .no (fun p => Identity.transport
        (fun s => match s with | .inl _ => Empty | .inr _ => Unit) p ())

instance [DecEq α] [DecEq β] : DecEq (α × β) where
  decEq
    | (a, x), (b, y) => ((decideEq a b).product (decideEq x y)).map
        (fun p => Identity.pair p.1 p.2)
        (fun p => (Identity.cong Prod.fst p, Identity.cong Prod.snd p))

def list [DecEq α] : (xs ys : List α) → Dec (xs ≡ ys)
  | [], [] => .yes .refl
  | [], _ :: _ => .no (fun p => Identity.transport
      (fun l => match l with | [] => Unit | _ :: _ => Empty) p ())
  | _ :: _, [] => .no (fun p => Identity.transport
      (fun l => match l with | [] => Empty | _ :: _ => Unit) p ())
  | x :: xs, y :: ys => ((decideEq x y).product (list xs ys)).map
      (fun p => Identity.cong₂ List.cons p.1 p.2)
      (fun p => (Identity.cong (fun l => l.headD x) p, Identity.cong List.tail p))

instance [DecEq α] : DecEq (List α) := ⟨list⟩

end DecEq

end Prelude
