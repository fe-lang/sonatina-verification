import Init

/-! Computational Type-valued identity and its eliminators. -/

set_option autoImplicit false
set_option genInjectivity false

universe u v w

namespace Prelude

/-- The identity type of two elements of `α`. -/
inductive Identity {α : Type u} (a : α) : α → Type u where
  | refl : Identity a a

scoped infix:50 " ≡ " => Identity

namespace Identity

variable {α : Type u} {β : Type v} {γ : Type w} {a b c d : α}

/-- Based path induction. Direct elimination avoids generated transports of the indices. -/
def ind {a : α} (motive : (b : α) → a ≡ b → Sort v)
    (base : motive a .refl) {b : α} (p : a ≡ b) : motive b p :=
  Identity.casesOn (motive := motive) p base

/-- An identity witness implies Lean equality. -/
theorem toEq (p : a ≡ b) : a = b :=
  ind (fun b _ => a = b) rfl p

def symm (p : a ≡ b) : b ≡ a :=
  ind (fun b _ => b ≡ a) .refl p

/-- Composition in traversal order: first `p`, then `q`. -/
def trans (p : a ≡ b) (q : b ≡ c) : a ≡ c :=
  ind (fun b _ => b ≡ c → a ≡ c) (fun q => q) p q

instance : Trans (@Identity α) (@Identity α) (@Identity α) := ⟨trans⟩

def cong (f : α → β) (p : a ≡ b) : f a ≡ f b :=
  ind (fun b _ => f a ≡ f b) .refl p

def cong₂ (f : α → β → γ) {x y : β} (p : a ≡ b) (q : x ≡ y) :
    f a x ≡ f b y :=
  match p, q with
  | .refl, .refl => .refl

/-- Transport also accepts Prop-valued families at the Lean interface. -/
def transport (P : α → Sort v) (p : a ≡ b) (x : P a) : P b :=
  ind (fun b _ => P b) x p

def cast {A B : Type u} (p : A ≡ B) (x : A) : B :=
  transport (fun X => X) p x

def depCong {P : α → Type v} (f : (x : α) → P x) (p : a ≡ b) :
    transport P p (f a) ≡ f b :=
  match p with
  | .refl => .refl

def transRefl (p : a ≡ b) : p.trans .refl ≡ p :=
  match p with
  | .refl => .refl

def reflTrans (p : a ≡ b) : Identity.refl.trans p ≡ p := .refl

def transAssoc (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) :
    (p.trans q).trans r ≡ p.trans (q.trans r) := by
  cases p
  exact .refl

def symmSymm (p : a ≡ b) : p.symm.symm ≡ p :=
  match p with
  | .refl => .refl

def symmTrans (p : a ≡ b) : p.symm.trans p ≡ .refl :=
  match p with
  | .refl => .refl

def transSymm (p : a ≡ b) : p.trans p.symm ≡ .refl :=
  match p with
  | .refl => .refl

def congId (p : a ≡ b) : cong id p ≡ p :=
  match p with
  | .refl => .refl

def congComp (f : α → β) (g : β → γ) (p : a ≡ b) :
    cong (g ∘ f) p ≡ cong g (cong f p) :=
  match p with
  | .refl => .refl

def congTrans (f : α → β) (p : a ≡ b) (q : b ≡ c) :
    cong f (p.trans q) ≡ (cong f p).trans (cong f q) := by
  cases p
  exact .refl

def transportTrans (P : α → Type v) (p : a ≡ b) (q : b ≡ c) (x : P a) :
    transport P (p.trans q) x ≡ transport P q (transport P p x) :=
  ind (fun b p => (q : b ≡ c) →
    transport P (p.trans q) x ≡ transport P q (transport P p x))
    (fun _ => .refl) p q

def transportSymm (P : α → Type v) (p : a ≡ b) (x : P a) :
    transport P p.symm (transport P p x) ≡ x :=
  ind (fun _ p => transport P p.symm (transport P p x) ≡ x) .refl p

/-- A transport in a constant family returns the value. -/
def transportConst (p : a ≡ b) (x : β) : transport (fun _ => β) p x ≡ x :=
  ind (fun _ p => transport (fun _ => β) p x ≡ x) .refl p

/-- Dependent functions commute with transport in their argument family. -/
def transportMap {P : α → Type v} {Q : α → Type w}
    (f : (x : α) → P x → Q x) (p : a ≡ b) (x : P a) :
    transport Q p (f a x) ≡ f b (transport P p x) :=
  match p with
  | .refl => .refl

def pair {x y : β} (p : a ≡ b) (q : x ≡ y) : (a, x) ≡ (b, y) :=
  cong₂ Prod.mk p q

def sigma {P : α → Type v} {x : P a} {y : P b}
    (p : a ≡ b) (q : transport P p x ≡ y) :
    (⟨a, x⟩ : Sigma P) ≡ ⟨b, y⟩ :=
  match p, q with
  | .refl, .refl => .refl

def sigmaSnd {P : α → Type v} {x y : Sigma P} (p : x ≡ y) :
    transport P (cong Sigma.fst p) x.2 ≡ y.2 :=
  match p with
  | .refl => .refl

def congFun {P : α → Type v} {f g : (x : α) → P x} (p : f ≡ g) (x : α) :
    f x ≡ g x := cong (fun h => h x) p

/-- Constructor injectivity obtained by applying a total projection to the path. -/
def someInject {a b : α} (p : some a ≡ some b) : a ≡ b :=
  cong (fun value => value.getD a) p

def inlInject {a b : α} (p : (Sum.inl a : Sum α β) ≡ .inl b) : a ≡ b :=
  cong (Sum.elim id (fun _ => a)) p

def inrInject {a b : β} (p : (Sum.inr a : Sum α β) ≡ .inr b) : a ≡ b :=
  cong (Sum.elim (fun _ => a) id) p

/-- Different constructors have no identity: transport `Unit` into `Empty`. -/
def inlNotInr {x : α} {y : β} (p : (Sum.inl x : Sum α β) ≡ .inr y) : Empty :=
  transport (fun s => match s with | .inl _ => Unit | .inr _ => Empty) p ()

def inrNotInl {x : β} {y : α} (p : (Sum.inr x : Sum α β) ≡ .inl y) : Empty :=
  transport (fun s => match s with | .inl _ => Empty | .inr _ => Unit) p ()

def noneNotSome {x : α} (p : (none : Option α) ≡ some x) : Empty :=
  transport (fun o => match o with | none => Unit | some _ => Empty) p ()

/-- The value of an option under a function, when the result has a value. -/
def ofMapSome {f : α → β} {y : β} : (o : Option α) → o.map f ≡ some y →
    (x : α) × ((o ≡ some x) × (f x ≡ y))
  | none, p => (noneNotSome p).elim
  | some x, p => ⟨x, .refl, someInject p⟩

/-- Transport along `p.symm` and then along `p`. -/
def symmTransport (P : α → Type v) (p : a ≡ b) (y : P b) :
    transport P p (transport P p.symm y) ≡ y :=
  ind (fun _ p => (y : P _) → transport P p (transport P p.symm y) ≡ y) (fun _ => .refl) p y

/-- Two identities from one element to `inl` values: an identity of the values that carries
the first identity to the second. -/
abbrev InlFiber (s : Sum α β) {x y : α} (p : s ≡ .inl x) (q : s ≡ .inl y) : Type (max u v) :=
  (e : x ≡ y) × (transport (fun z => s ≡ .inl z) e p ≡ q)

abbrev InrFiber (s : Sum α β) {x y : β} (p : s ≡ .inr x) (q : s ≡ .inr y) : Type (max u v) :=
  (e : x ≡ y) × (transport (fun z => s ≡ .inr z) e p ≡ q)

def inlCode {x : α} : (t : Sum α β) → (Sum.inl x : Sum α β) ≡ t → Type (max u v)
  | .inl _, q => InlFiber (.inl x) .refl q
  | .inr _, _ => PUnit

def inlEncode {x : α} : (t : Sum α β) → (q : (Sum.inl x : Sum α β) ≡ t) → inlCode t q
  | _, .refl => (⟨.refl, .refl⟩ : InlFiber (β := β) (.inl x) .refl .refl)

def inrCode {x : β} : (t : Sum α β) → (Sum.inr x : Sum α β) ≡ t → Type (max u v)
  | .inl _, _ => PUnit
  | .inr _, q => InrFiber (.inr x) .refl q

def inrEncode {x : β} : (t : Sum α β) → (q : (Sum.inr x : Sum α β) ≡ t) → inrCode t q
  | _, .refl => (⟨.refl, .refl⟩ : InrFiber (α := α) (.inr x) .refl .refl)

/-- `inl` has at most one value and one identity over each element of the sum. -/
def inlFiber : {s : Sum α β} → {x y : α} → (p : s ≡ .inl x) → (q : s ≡ .inl y) →
    InlFiber s p q
  | _, _, y, .refl, q => inlEncode (.inl y) q

/-- `inr` has at most one value and one identity over each element of the sum. -/
def inrFiber : {s : Sum α β} → {x y : β} → (p : s ≡ .inr x) → (q : s ≡ .inr y) →
    InrFiber s p q
  | _, _, y, .refl, q => inrEncode (.inr y) q

end Identity

/-- Maps in the two directions, with the round-trip identity at each element. -/
structure Iso (α : Type u) (β : Type v) where
  to : α → β
  inv : β → α
  invTo : (x : α) → inv (to x) ≡ x
  toInv : (y : β) → to (inv y) ≡ y

namespace Iso

variable {α : Type u} {β : Type v} {γ : Type w}

protected def refl (α : Type u) : Iso α α :=
  ⟨fun x => x, fun x => x, fun _ => .refl, fun _ => .refl⟩

def symm (e : Iso α β) : Iso β α := ⟨e.inv, e.to, e.toInv, e.invTo⟩

def trans (e : Iso α β) (f : Iso β γ) : Iso α γ where
  to x := f.to (e.to x)
  inv z := e.inv (f.inv z)
  invTo x := (Identity.cong e.inv (f.invTo (e.to x))).trans (e.invTo x)
  toInv z := (Identity.cong f.to (e.toInv (f.inv z))).trans (f.toInv z)

/-- A family on `α`, as a family on `β`. -/
abbrev Moved (e : Iso α β) (Q : α → Type w) : β → Type w := fun y => Q (e.inv y)

/-- Evidence at `x` moves to evidence at `e.to x` along the round-trip identity. -/
def across (e : Iso α β) (Q : α → Type w) (x : α) (evidence : Q x) : e.Moved Q (e.to x) :=
  Identity.transport Q (e.invTo x).symm evidence

def back (e : Iso α β) (Q : α → Type w) (x : α) (evidence : e.Moved Q (e.to x)) : Q x :=
  Identity.transport Q (e.invTo x) evidence

def backAcross (e : Iso α β) (Q : α → Type w) (x : α) (evidence : Q x) :
    e.back Q x (e.across Q x evidence) ≡ evidence :=
  Identity.symmTransport Q (e.invTo x) evidence

def acrossBack (e : Iso α β) (Q : α → Type w) (x : α) (evidence : e.Moved Q (e.to x)) :
    e.across Q x (e.back Q x evidence) ≡ evidence :=
  Identity.transportSymm Q (e.invTo x) evidence

end Iso

/-- Pointwise identity of dependent functions. -/
abbrev Homotopy {α : Type u} {P : α → Type v} (f g : (x : α) → P x) :=
  (x : α) → f x ≡ g x

namespace Homotopy

variable {α : Type u} {P : α → Type v} {f g h : (x : α) → P x}

protected def refl (f : (x : α) → P x) : Homotopy f f := fun _ => .refl

def symm (p : Homotopy f g) : Homotopy g f := fun x => (p x).symm

/-- Composition in traversal order: first `p`, then `q`. -/
def trans (p : Homotopy f g) (q : Homotopy g h) : Homotopy f h := fun x => (p x).trans (q x)

end Homotopy

end Prelude
