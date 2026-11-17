import Init

/-! Computational Type-valued identity and its eliminators.

Each function eliminates an identity by `ind` or `indEnd`, with an explicit motive. Its term
has no eliminator of a `Prop` equality, so its reduction compares no two values. -/

set_option autoImplicit false
set_option genInjectivity false

universe u v w z

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

/-- Path induction with the second element fixed. -/
def indEnd {b : α} (motive : (a : α) → a ≡ b → Sort v)
    (base : motive b .refl) {a : α} (p : a ≡ b) : motive a p :=
  ind (fun b p => (motive : (a : α) → a ≡ b → Sort v) → motive b .refl → motive a p)
    (fun _ base => base) p motive base

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
  ind (fun b _ => f a x ≡ f b y) (cong (f a) q) p

/-- Transport also accepts Prop-valued families at the Lean interface. -/
def transport (P : α → Sort v) (p : a ≡ b) (x : P a) : P b :=
  ind (fun b _ => P b) x p

def cast {A B : Type u} (p : A ≡ B) (x : A) : B :=
  transport (fun X => X) p x

def depCong {P : α → Type v} (f : (x : α) → P x) (p : a ≡ b) :
    transport P p (f a) ≡ f b :=
  ind (fun b p => transport P p (f a) ≡ f b) .refl p

def transRefl (p : a ≡ b) : p.trans .refl ≡ p :=
  ind (fun _ p => p.trans .refl ≡ p) .refl p

def reflTrans (p : a ≡ b) : Identity.refl.trans p ≡ p := .refl

def transAssoc (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) :
    (p.trans q).trans r ≡ p.trans (q.trans r) :=
  ind (fun b p => (q : b ≡ c) → (p.trans q).trans r ≡ p.trans (q.trans r)) (fun _ => .refl) p q

def symmSymm (p : a ≡ b) : p.symm.symm ≡ p :=
  ind (fun _ p => p.symm.symm ≡ p) .refl p

def symmTrans (p : a ≡ b) : p.symm.trans p ≡ .refl :=
  ind (fun _ p => p.symm.trans p ≡ .refl) .refl p

def transSymm (p : a ≡ b) : p.trans p.symm ≡ .refl :=
  ind (fun _ p => p.trans p.symm ≡ .refl) .refl p

def congId (p : a ≡ b) : cong id p ≡ p :=
  ind (fun _ p => cong id p ≡ p) .refl p

def congComp (f : α → β) (g : β → γ) (p : a ≡ b) :
    cong (g ∘ f) p ≡ cong g (cong f p) :=
  ind (fun _ p => cong (g ∘ f) p ≡ cong g (cong f p)) .refl p

def congTrans (f : α → β) (p : a ≡ b) (q : b ≡ c) :
    cong f (p.trans q) ≡ (cong f p).trans (cong f q) :=
  ind (fun b p => (q : b ≡ c) → cong f (p.trans q) ≡ (cong f p).trans (cong f q))
    (fun _ => .refl) p q

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
  ind (fun b p => transport Q p (f a x) ≡ f b (transport P p x)) .refl p

def pair {x y : β} (p : a ≡ b) (q : x ≡ y) : (a, x) ≡ (b, y) :=
  cong₂ Prod.mk p q

def sigma {P : α → Type v} {x : P a} {y : P b}
    (p : a ≡ b) (q : transport P p x ≡ y) :
    (⟨a, x⟩ : Sigma P) ≡ ⟨b, y⟩ :=
  ind (fun b p => (y : P b) → transport P p x ≡ y → (⟨a, x⟩ : Sigma P) ≡ ⟨b, y⟩)
    (fun _ q => cong (Sigma.mk a) q) p y q

def sigmaSnd {P : α → Type v} {x y : Sigma P} (p : x ≡ y) :
    transport P (cong Sigma.fst p) x.2 ≡ y.2 :=
  ind (fun y p => transport P (cong Sigma.fst p) x.2 ≡ y.2) .refl p

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

/-- The map of an inverse identity is the inverse of the map. -/
def congSymm (f : α → β) (p : a ≡ b) : cong f p.symm ≡ (cong f p).symm :=
  ind (fun _ p => cong f p.symm ≡ (cong f p).symm) .refl p

/-- An identity cancels its inverse on the left of a composite. -/
def symmTransTrans (t : a ≡ b) (p : b ≡ c) : t.symm.trans (t.trans p) ≡ p :=
  ind (fun _ t => (p : _ ≡ c) → t.symm.trans (t.trans p) ≡ p) (fun _ => .refl) t p

/-- An identity cancels on the right of a composite. -/
def cancelRight (t : b ≡ c) {p q : a ≡ b} (h : p.trans t ≡ q.trans t) : p ≡ q :=
  ind (fun _ t => p.trans t ≡ q.trans t → p ≡ q)
    (fun h => ((transRefl p).symm.trans h).trans (transRefl q)) t h

/-- A pointwise identity from a function to the identity function is natural. -/
def natural {h : α → α} (H : (x : α) → h x ≡ x) (p : a ≡ b) :
    (H a).trans p ≡ (cong h p).trans (H b) :=
  ind (fun b p => (H a).trans p ≡ (cong h p).trans (H b)) (transRefl (H a)) p

/-- A pointwise identity from a function to the identity function, at a value of the
function, is the map of that identity. -/
def naturalAt {h : α → α} (H : (x : α) → h x ≡ x) (x : α) : H (h x) ≡ cong h (H x) :=
  cancelRight (H x) (natural H (H x))

/-- Two identities from one element to `inl` values: an identity of the values that carries
the first identity to the second. -/
abbrev InlFiber (s : Sum α β) {x y : α} (p : s ≡ .inl x) (q : s ≡ .inl y) : Type (max u v) :=
  (e : x ≡ y) × (transport (fun z => s ≡ .inl z) e p ≡ q)

abbrev InrFiber (s : Sum α β) {x y : β} (p : s ≡ .inr x) (q : s ≡ .inr y) : Type (max u v) :=
  (e : x ≡ y) × (transport (fun z => s ≡ .inr z) e p ≡ q)

def inlCode {x : α} : (t : Sum α β) → (Sum.inl x : Sum α β) ≡ t → Type (max u v)
  | .inl _, q => InlFiber (.inl x) .refl q
  | .inr _, _ => PUnit

def inlEncode {x : α} (t : Sum α β) (q : (Sum.inl x : Sum α β) ≡ t) : inlCode t q :=
  ind (fun t q => inlCode t q) (⟨.refl, .refl⟩ : InlFiber (β := β) (.inl x) .refl .refl) q

def inrCode {x : β} : (t : Sum α β) → (Sum.inr x : Sum α β) ≡ t → Type (max u v)
  | .inl _, _ => PUnit
  | .inr _, q => InrFiber (.inr x) .refl q

def inrEncode {x : β} (t : Sum α β) (q : (Sum.inr x : Sum α β) ≡ t) : inrCode t q :=
  ind (fun t q => inrCode t q) (⟨.refl, .refl⟩ : InrFiber (α := α) (.inr x) .refl .refl) q

/-- `inl` has at most one value and one identity over each element of the sum. -/
def inlFiber {s : Sum α β} {x y : α} (p : s ≡ .inl x) (q : s ≡ .inl y) : InlFiber s p q :=
  indEnd (b := (Sum.inl x : Sum α β))
    (fun (s : Sum α β) (p : s ≡ .inl x) => (q : s ≡ .inl y) → InlFiber s p q)
    (fun (q : (Sum.inl x : Sum α β) ≡ .inl y) => inlEncode (.inl y) q) p q

/-- `inr` has at most one value and one identity over each element of the sum. -/
def inrFiber {s : Sum α β} {x y : β} (p : s ≡ .inr x) (q : s ≡ .inr y) : InrFiber s p q :=
  indEnd (b := (Sum.inr x : Sum α β))
    (fun (s : Sum α β) (p : s ≡ .inr x) => (q : s ≡ .inr y) → InrFiber s p q)
    (fun (q : (Sum.inr x : Sum α β) ≡ .inr y) => inrEncode (.inr y) q) p q

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

/-- The first round trip of an isomorphism, in the form that the second round trip
determines. -/
def invToOf (e : Iso α β) (x : α) : e.inv (e.to x) ≡ x :=
  (e.invTo (e.inv (e.to x))).symm.trans
    ((Identity.cong e.inv (e.toInv (e.to x))).trans (e.invTo x))

/-- The two round trips agree: the map of that first round trip is the second round trip at
the value of the map. -/
def coherence (e : Iso α β) (x : α) : Identity.cong e.to (e.invToOf x) ≡ e.toInv (e.to x) :=
  let p : e.to (e.inv (e.to x)) ≡ e.to x := Identity.cong e.to (e.invTo x)
  let first : e.to (e.inv (e.to (e.inv (e.to x)))) ≡ e.to (e.inv (e.to x)) :=
    Identity.cong e.to (e.invTo (e.inv (e.to x)))
  let inner : e.invTo (e.inv (e.to x)) ≡ Identity.cong (e.inv ∘ e.to) (e.invTo x) :=
    Identity.naturalAt (h := e.inv ∘ e.to) e.invTo x
  let moved : first ≡ Identity.cong (e.to ∘ e.inv) p :=
    (Identity.cong (Identity.cong e.to) inner).trans
      ((Identity.congComp (e.inv ∘ e.to) e.to (e.invTo x)).symm.trans
        (Identity.congComp e.to (e.to ∘ e.inv) (e.invTo x)))
  let square : first.trans (e.toInv (e.to x)) ≡ (e.toInv (e.to (e.inv (e.to x)))).trans p :=
    (Identity.cong (fun q => q.trans (e.toInv (e.to x))) moved).trans
      (Identity.natural (h := e.to ∘ e.inv) e.toInv p).symm
  let middle : Identity.cong e.to (Identity.cong e.inv (e.toInv (e.to x))) ≡
      e.toInv (e.to (e.inv (e.to x))) :=
    (Identity.congComp e.inv e.to (e.toInv (e.to x))).symm.trans
      (Identity.naturalAt (h := e.to ∘ e.inv) e.toInv (e.to x)).symm
  let parts : Identity.cong e.to (e.invToOf x) ≡
      first.symm.trans ((e.toInv (e.to (e.inv (e.to x)))).trans p) :=
    (Identity.congTrans e.to (e.invTo (e.inv (e.to x))).symm
        ((Identity.cong e.inv (e.toInv (e.to x))).trans (e.invTo x))).trans
      (Identity.cong₂ Identity.trans (Identity.congSymm e.to (e.invTo (e.inv (e.to x))))
        ((Identity.congTrans e.to (Identity.cong e.inv (e.toInv (e.to x))) (e.invTo x)).trans
          (Identity.cong (fun q => q.trans p) middle)))
  (parts.trans (Identity.cong (fun q => first.symm.trans q) square.symm)).trans
    (Identity.symmTransTrans first (e.toInv (e.to x)))

/-- An isomorphism of the fibres at each element gives an isomorphism of the sums. -/
def sigmaFiber {B : Type u} {C : B → Type v} {C' : B → Type w}
    (φ : (b : B) → Iso (C b) (C' b)) : Iso ((b : B) × C b) ((b : B) × C' b) where
  to x := ⟨x.1, (φ x.1).to x.2⟩
  inv y := ⟨y.1, (φ y.1).inv y.2⟩
  invTo x := Identity.cong (Sigma.mk x.1) ((φ x.1).invTo x.2)
  toInv y := Identity.cong (Sigma.mk y.1) ((φ y.1).toInv y.2)

/-- An element of the fibre over the value of an isomorphism, moved back along the map of an
identity. -/
def sigmaBaseBack {B' : Type u} {B : Type v} (e : Iso B' B) (C : B → Type w) {b b' : B'}
    (p : b ≡ b') (c : C (e.to b')) :
    (⟨b, Identity.transport C (Identity.cong e.to p).symm c⟩ : (b' : B') × C (e.to b')) ≡
      ⟨b', c⟩ :=
  Identity.indEnd
    (fun b p =>
      (⟨b, Identity.transport C (Identity.cong e.to p).symm c⟩ : (b' : B') × C (e.to b')) ≡
        ⟨b', c⟩)
    .refl p

/-- An isomorphism of the bases gives an isomorphism of the sums of a family on the second
base. The two maps and the second round trip use the second round trip of the bases. The
first round trip uses the agreement of the two round trips of the bases. -/
def sigmaBase {B' : Type u} {B : Type v} (e : Iso B' B) (C : B → Type w) :
    Iso ((b' : B') × C (e.to b')) ((b : B) × C b) where
  to x := ⟨e.to x.1, x.2⟩
  inv y := ⟨e.inv y.1, Identity.transport C (e.toInv y.1).symm y.2⟩
  invTo x :=
    Identity.transport
      (fun q =>
        (⟨e.inv (e.to x.1), Identity.transport C q.symm x.2⟩ : (b' : B') × C (e.to b')) ≡
          ⟨x.1, x.2⟩)
      (e.coherence x.1) (sigmaBaseBack e C (e.invToOf x.1) x.2)
  toInv y := Identity.sigma (e.toInv y.1) (Identity.symmTransport C (e.toInv y.1) y.2)

/-- An isomorphism of the bases, and an isomorphism of the fibres over it, give an isomorphism
of the sums. -/
def sigma {B' : Type u} {B : Type v} {C' : B' → Type w} {C : B → Type z} (e : Iso B' B)
    (φ : (b' : B') → Iso (C' b') (C (e.to b'))) : Iso ((b' : B') × C' b') ((b : B) × C b) :=
  (sigmaFiber φ).trans (sigmaBase e C)

end Iso

/-- A family on the identities from one element is its value at the reflexivity. -/
def Identity.contract {α : Type u} {x₀ : α} (H : (m : α) → x₀ ≡ m → Type w) :
    Iso ((m : α) × (e : x₀ ≡ m) × H m e) (H x₀ .refl) where
  to t := Identity.ind (fun m e => H m e → H x₀ .refl) (fun h => h) t.2.1 t.2.2
  inv h := ⟨x₀, .refl, h⟩
  invTo t :=
    Identity.ind
      (fun m e => (h : H m e) →
        (⟨x₀, .refl, Identity.ind (fun m e => H m e → H x₀ .refl) (fun h => h) e h⟩ :
          (m : α) × (e : x₀ ≡ m) × H m e) ≡ ⟨m, e, h⟩)
      (fun _ => .refl) t.2.1 t.2.2
  toInv _ := .refl

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
