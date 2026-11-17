import Prelude.Identity
import Prelude.Decision

/-! Type-valued positions and dependent environments over ordinary Lean lists.

The functions on a position and on an environment use `casesOn` with an explicit motive. A
generated matcher on these families eliminates `Prop` equalities of the list and of the value,
and the elaborator then compares the values again at each step. The decisions of the identity of
two positions and of two environments use a generated matcher: the analysis of two values at
one list needs the identity of the two lists. -/

set_option autoImplicit false
set_option genInjectivity false

universe u v w z

namespace Prelude

/-- A position occupied by `a`; repeated occurrences have distinct witnesses. -/
inductive Elem {α : Type u} (a : α) : List α → Type u where
  | here {xs : List α} : Elem a (a :: xs)
  | there {b : α} {xs : List α} : Elem a xs → Elem a (b :: xs)

namespace Elem

variable {α : Type u} {β : Type v} {a : α}

def toFin {xs : List α} (i : Elem a xs) : Fin xs.length :=
  Elem.casesOn (motive := fun xs _ => Fin xs.length) i ⟨0, Nat.zero_lt_succ _⟩
    (fun j => (toFin j).succ)

def map (f : α → β) {xs : List α} (i : Elem a xs) : Elem (f a) (xs.map f) :=
  Elem.casesOn (motive := fun xs _ => Elem (f a) (xs.map f)) i .here (fun j => .there (map f j))

theorem toMem {xs : List α} (i : Elem a xs) : a ∈ xs := by
  induction i with
  | here => exact List.mem_cons_self
  | there _ ih => exact List.mem_cons_of_mem _ ih

/-- A position of the first part of a concatenation. -/
def left {xs ys : List α} (i : Elem a xs) : Elem a (xs ++ ys) :=
  Elem.casesOn (motive := fun xs _ => Elem a (xs ++ ys)) i .here (fun j => .there j.left)

/-- A position of the second part of a concatenation. -/
def right : (xs : List α) → {ys : List α} → Elem a ys → Elem a (xs ++ ys)
  | [], _, i => i
  | _ :: xs, _, i => .there (right xs i)

/-- The type of the case analysis of a position, as a function of its list. A position of a
nonempty list gives a value of each motive on the positions of that list that has a value at
the first position and at each position of the tail. -/
def ConsCases (a : α) (zs : List α) : Elem a zs → Type (max u (w + 1)) :=
  List.casesOn (motive := fun zs => Elem a zs → Type (max u (w + 1))) zs (fun _ => PUnit)
    (fun b xs i => (motive : (c : α) → Elem c (b :: xs) → Type w) → motive b .here →
      ((c : α) → (j : Elem c xs) → motive c (.there j)) → motive a i)

def consCasesOn {zs : List α} (i : Elem a zs) : ConsCases.{u, w} a zs i :=
  Elem.casesOn (motive := fun zs i => ConsCases.{u, w} a zs i) i
    (fun _ here _ => here) (fun j _ _ there => there a j)

/-- The case analysis of a position of a nonempty list. The motive is a function of the
element of the position, so the analysis eliminates no equality of elements. -/
def consCases {b : α} {xs : List α} {motive : (c : α) → Elem c (b :: xs) → Type w}
    (i : Elem a (b :: xs)) (here : motive b .here)
    (there : (c : α) → (j : Elem c xs) → motive c (.there j)) : motive a i :=
  consCasesOn.{u, w} i motive here there

/-- A position of a concatenation is a position of the first part or a position of the second
part. -/
def split : (xs : List α) → {ys : List α} → {a : α} → (i : Elem a (xs ++ ys)) →
    ((j : Elem a xs) × (i ≡ j.left)) ⊕ ((j : Elem a ys) × (i ≡ j.right xs))
  | [], _, _, i => .inr ⟨i, .refl⟩
  | b :: xs, ys, _, i =>
      consCases
        (motive := fun c (i : Elem c (b :: (xs ++ ys))) =>
          ((j : Elem c (b :: xs)) × (i ≡ j.left)) ⊕ ((j : Elem c ys) × (i ≡ j.right (b :: xs))))
        i (.inl ⟨.here, .refl⟩)
        (fun _ j =>
          match split xs j with
          | .inl found => .inl ⟨.there found.1, Identity.cong Elem.there found.2⟩
          | .inr found => .inr ⟨found.1, Identity.cong Elem.there found.2⟩)

/-- A position of a nonempty list is the first position, with the identity of the two elements,
or a position of the tail. -/
def uncons {b : α} {xs : List α} (i : Elem a (b :: xs)) : (a ≡ b) ⊕ Elem a xs :=
  consCases (motive := fun c (_ : Elem c (b :: xs)) => (c ≡ b) ⊕ Elem c xs) i (.inl .refl)
    (fun _ j => .inr j)

/-- A value of each type from a position of the empty list. -/
def ofNil {β : Type w} (i : Elem a ([] : List α)) : β :=
  Elem.casesOn
    (motive := fun zs _ => List.casesOn (motive := fun _ => Type w) zs β (fun _ _ => PUnit))
    i PUnit.unit (fun _ => PUnit.unit)

/-- A position of an element in a list, or the evidence that the list has no such position. -/
def find [DecEq α] (a : α) : (xs : List α) → Dec (Elem a xs)
  | [] => .no (fun i => ofNil i)
  | b :: xs =>
      match decideEq a b with
      | .yes same => .yes (Identity.transport (fun c => Elem a (c :: xs)) same .here)
      | .no differ =>
          match find a xs with
          | .yes i => .yes (.there i)
          | .no absent =>
              .no (fun i =>
                match uncons i with
                | .inl same => differ same
                | .inr j => absent j)

/-- The type with a value at the first position only. -/
def IsHere {b : α} {xs : List α} (i : Elem a (b :: xs)) : Type :=
  consCases (motive := fun _ _ => Type) i Unit (fun _ _ => Empty)

/-- The position of the tail, for each position after the first position. -/
def back {b : α} {xs : List α} (i : Elem a (b :: xs)) : Option (Elem a xs) :=
  consCases (motive := fun c _ => Option (Elem c xs)) i none (fun _ j => some j)

/-- The decision of the identity of two positions of one element. -/
def decide : {xs : List α} → (i j : Elem a xs) → Dec (i ≡ j)
  | _, .here, .here => .yes .refl
  | _, .here, .there _ => .no (fun p => Identity.transport IsHere p ())
  | _, .there _, .here => .no (fun p => Identity.transport IsHere p.symm ())
  | _, .there i, .there j =>
      (decide i j).map (Identity.cong Elem.there)
        (fun p => Identity.someInject (Identity.cong back p))

/-- No element of a list has two positions. -/
def Distinct (xs : List α) : Type u := (x : α) → (i j : Elem x xs) → i ≡ j

/-- The tail of a list with no element at two positions has no element at two positions. -/
def Distinct.tail {b : α} {xs : List α} (d : Distinct (b :: xs)) : Distinct xs :=
  fun x i j => Identity.someInject (Identity.cong back (d x (.there i) (.there j)))

/-- The first element of a list with no element at two positions has no position in the
tail. -/
def Distinct.fresh {b : α} {xs : List α} (d : Distinct (b :: xs)) (i : Elem b xs) : Empty :=
  Identity.transport IsHere (d b .here (.there i)) ()

/-- A list with one more first element has no element at two positions, when its tail has none
and the first element has no position in the tail. -/
def Distinct.cons {b : α} {xs : List α} (tail : Distinct xs) (fresh : Elem b xs → Empty) :
    Distinct (b :: xs) :=
  fun x i j =>
    match x, i, j with
    | _, .here, .here => .refl
    | _, .here, .there j => (fresh j).elim
    | _, .there i, .here => (fresh i).elim
    | _, .there i, .there j => Identity.cong Elem.there (tail _ i j)

end Elem

/-- One value of `P a` for each element `a` of a list. -/
inductive All {α : Type u} (P : α → Type v) : List α → Type (max u v) where
  | nil : All P []
  | cons {a : α} {xs : List α} : P a → All P xs → All P (a :: xs)

namespace All

variable {α : Type u} {P : α → Type v} {Q : α → Type w} {R : α → Type z}

/-- The type of the case analysis of an environment, as a function of its list. An
environment of a nonempty list gives a value of each motive that has a value at each
`.cons x rest`. -/
def ConsCases (P : α → Type v) (xs : List α) : All P xs → Type (max u v (w + 1)) :=
  List.casesOn (motive := fun xs => All P xs → Type (max u v (w + 1))) xs (fun _ => PUnit)
    (fun a xs env => (motive : All P (a :: xs) → Type w) →
      ((x : P a) → (rest : All P xs) → motive (.cons x rest)) → motive env)

def consCasesOn {xs : List α} (env : All P xs) : ConsCases.{u, v, w} P xs env :=
  All.casesOn (motive := fun xs env => ConsCases.{u, v, w} P xs env) env PUnit.unit
    (fun x rest _ cons => cons x rest)

/-- The case analysis of an environment of a nonempty list. The type of the analysis is a
function of the list, so the analysis eliminates no equality of lists. -/
def consCases {a : α} {xs : List α} {motive : All P (a :: xs) → Type w}
    (env : All P (a :: xs)) (cons : (x : P a) → (rest : All P xs) → motive (.cons x rest)) :
    motive env :=
  consCasesOn.{u, v, w} env motive cons

/-- The first value of an environment of a nonempty list. -/
def head {a : α} {xs : List α} (env : All P (a :: xs)) : P a :=
  consCases (motive := fun _ => P a) env (fun x _ => x)

/-- The other values of an environment of a nonempty list. -/
def tail {a : α} {xs : List α} (env : All P (a :: xs)) : All P xs :=
  consCases (motive := fun _ => All P xs) env (fun _ rest => rest)

def lookup {a : α} {xs : List α} (env : All P xs) (i : Elem a xs) : P a :=
  Elem.casesOn (motive := fun xs _ => All P xs → P a) i (fun env => env.head)
    (fun j env => env.tail.lookup j) env

def map (f : (a : α) → P a → Q a) {xs : List α} (env : All P xs) : All Q xs :=
  All.casesOn (motive := fun xs _ => All Q xs) env .nil
    (fun x rest => .cons (f _ x) (rest.map f))

def append {xs ys : List α} (x : All P xs) (y : All P ys) : All P (xs ++ ys) :=
  All.casesOn (motive := fun xs _ => All P (xs ++ ys)) x y
    (fun v rest => .cons v (rest.append y))

/-- An environment of the empty list is the empty environment. -/
def nilEta (env : All P ([] : List α)) : env ≡ .nil :=
  All.casesOn
    (motive := fun xs env =>
      List.casesOn (motive := fun xs => All P xs → Type (max u v)) xs (fun env => env ≡ All.nil)
        (fun _ _ _ => PUnit) env)
    env .refl (fun _ _ => PUnit.unit)

/-- The concatenation of an environment of one value and an environment. -/
def appendOne {a : α} {xs : List α} (x : All P [a]) (env : All P xs) :
    (x.append env : All P (a :: xs)) ≡ .cons x.head env :=
  consCases
    (motive := fun (x : All P [a]) => (x.append env : All P (a :: xs)) ≡ .cons x.head env) x
    (fun v rest =>
      Identity.cong (fun (r : All P []) => (All.cons v (r.append env) : All P (a :: xs)))
        (nilEta rest))

/-- The environment with a new value at one position. -/
def set {a : α} {xs : List α} (env : All P xs) (i : Elem a xs) (x : P a) : All P xs :=
  Elem.casesOn (motive := fun xs _ => All P xs → All P xs) i (fun env => .cons x env.tail)
    (fun j env => .cons env.head (env.tail.set j x)) env

def tabulate : (xs : List α) → ((a : α) → Elem a xs → P a) → All P xs
  | [], _ => .nil
  | a :: xs, f => .cons (f a .here) (tabulate xs (fun b i => f b (.there i)))

def lookupTabulate {a : α} {xs : List α} (f : (a : α) → Elem a xs → P a) (i : Elem a xs) :
    (tabulate xs f).lookup i ≡ f a i :=
  Elem.casesOn
    (motive := fun xs i => (f : (b : α) → Elem b xs → P b) → (tabulate xs f).lookup i ≡ f a i)
    i (fun _ => .refl) (fun j f => lookupTabulate (fun b k => f b (.there k)) j) f

/-- The value of a map at a position. -/
def lookupMap (f : (a : α) → P a → Q a) {a : α} {xs : List α} (x : All P xs)
    (i : Elem a xs) : (x.map f).lookup i ≡ f a (x.lookup i) :=
  Elem.casesOn
    (motive := fun xs i => (x : All P xs) → (x.map f).lookup i ≡ f a (x.lookup i)) i
    (fun x =>
      consCases (motive := fun x => (x.map f).lookup Elem.here ≡ f a (x.lookup .here)) x
        (fun _ _ => .refl))
    (fun j x =>
      consCases (motive := fun x => (x.map f).lookup (Elem.there j) ≡ f a (x.lookup (.there j)))
        x (fun _ rest => lookupMap f rest j))
    x

/-- The value at a position of the first part of a concatenation. -/
def lookupLeft {a : α} {xs ys : List α} (x : All P xs) (y : All P ys) (i : Elem a xs) :
    (x.append y).lookup i.left ≡ x.lookup i :=
  Elem.casesOn
    (motive := fun xs i => (x : All P xs) → (x.append y).lookup i.left ≡ x.lookup i) i
    (fun x =>
      consCases (motive := fun x => (x.append y).lookup Elem.here ≡ x.lookup .here) x
        (fun _ _ => .refl))
    (fun j x =>
      consCases
        (motive := fun x => (x.append y).lookup (Elem.there j.left) ≡ x.lookup (.there j))
        x (fun _ rest => lookupLeft rest y j))
    x

/-- The value at a position of the second part of a concatenation. -/
def lookupRight {xs ys : List α} (x : All P xs) (y : All P ys) {a : α} (i : Elem a ys) :
    (x.append y).lookup (i.right xs) ≡ y.lookup i :=
  All.casesOn (motive := fun xs x => (x.append y).lookup (i.right xs) ≡ y.lookup i) x .refl
    (fun _ rest => lookupRight rest y i)

/-- Two functions that agree at each value give the same map. -/
def mapCongr {f g : (a : α) → P a → Q a} (same : (a : α) → (x : P a) → f a x ≡ g a x)
    {xs : List α} (x : All P xs) : x.map f ≡ x.map g :=
  All.casesOn (motive := fun _ x => x.map f ≡ x.map g) x .refl
    (fun v rest => Identity.cong₂ All.cons (same _ v) (mapCongr same rest))

def mapMap (f : (a : α) → P a → Q a) (g : (a : α) → Q a → R a) {xs : List α}
    (x : All P xs) : (x.map f).map g ≡ x.map (fun a p => g a (f a p)) :=
  All.casesOn (motive := fun _ x => (x.map f).map g ≡ x.map (fun a p => g a (f a p))) x .refl
    (fun _ rest => Identity.cong (All.cons _) (mapMap f g rest))

/-- The map by the function that returns each value. -/
def mapId {xs : List α} (x : All P xs) : x.map (fun _ v => v) ≡ x :=
  All.casesOn (motive := fun _ x => x.map (fun _ v => v) ≡ x) x .refl
    (fun _ rest => Identity.cong (All.cons _) (mapId rest))

/-- The map of a table. -/
def mapTabulate (g : (a : α) → P a → Q a) :
    (xs : List α) → (f : (a : α) → Elem a xs → P a) →
      (tabulate xs f).map g ≡ tabulate xs (fun a i => g a (f a i))
  | [], _ => .refl
  | _ :: xs, f => Identity.cong (All.cons _) (mapTabulate g xs (fun b i => f b (.there i)))

/-- The table of a concatenation has the table of each part. -/
def tabulateAppend : (xs : List α) → {ys : List α} → (f : (a : α) → Elem a (xs ++ ys) → P a) →
    tabulate (xs ++ ys) f ≡
      (tabulate xs (fun a i => f a i.left)).append (tabulate ys (fun a i => f a (i.right xs)))
  | [], _, _ => .refl
  | _ :: xs, _, f => Identity.cong (All.cons _) (tabulateAppend xs (fun b i => f b (.there i)))

def mapAppend (f : (a : α) → P a → Q a) {xs ys : List α} (x : All P xs) (y : All P ys) :
    (x.append y).map f ≡ (x.map f).append (y.map f) :=
  All.casesOn (motive := fun _ x => (x.append y).map f ≡ (x.map f).append (y.map f)) x .refl
    (fun _ rest => Identity.cong (All.cons _) (mapAppend f rest y))

/-- The values at a list of positions. A position can occur more than once, and a position
can be absent. -/
def select {xs ys : List α} (env : All P xs) (positions : All (fun a => Elem a xs) ys) :
    All P ys :=
  positions.map (fun _ i => env.lookup i)

/-- The selection at a concatenation of two lists of positions. -/
def selectAppend {xs ys zs : List α} (env : All P xs) (first : All (fun a => Elem a xs) ys)
    (second : All (fun a => Elem a xs) zs) :
    env.select (first.append second) ≡ (env.select first).append (env.select second) :=
  mapAppend _ first second

/-- The selection at selected positions is the selection of the selection. -/
def selectSelect {xs ys zs : List α} (env : All P xs) (first : All (fun a => Elem a xs) ys)
    (second : All (fun a => Elem a ys) zs) :
    env.select (first.select second) ≡ (env.select first).select second :=
  (mapMap _ _ second).trans
    (mapCongr (fun _ i => (lookupMap (fun _ j => env.lookup j) first i).symm) second)

/-- A table of positions selects `y` when the value at each of its positions is the value of
`y`. -/
def selectTabulate {xs : List α} (env : All P xs) {ys : List α} (y : All P ys)
    (f : (a : α) → Elem a ys → Elem a xs)
    (same : (a : α) → (i : Elem a ys) → env.lookup (f a i) ≡ y.lookup i) :
    env.select (tabulate ys f) ≡ y :=
  All.casesOn
    (motive := fun ys y => (f : (a : α) → Elem a ys → Elem a xs) →
      ((a : α) → (i : Elem a ys) → env.lookup (f a i) ≡ y.lookup i) →
      env.select (tabulate ys f) ≡ y)
    y (fun _ _ => .refl)
    (fun _ rest f same =>
      Identity.cong₂ All.cons (same _ .here)
        (selectTabulate env rest (fun b i => f b (.there i)) (fun b i => same b (.there i))))
    f same

/-- The values at the image of a list, from a function of the values over the function of the
elements. -/
def image {β : Type u} {T : β → Type v} (f : α → β) (g : (a : α) → P a → T (f a))
    {xs : List α} (x : All P xs) : All T (xs.map f) :=
  All.casesOn (motive := fun xs _ => All T (xs.map f)) x .nil
    (fun y rest => .cons (g _ y) (image f g rest))

/-- The decision of the identity of two environments, from the decision at each element. -/
def decide (dec : (a : α) → (x y : P a) → Dec (x ≡ y)) :
    {xs : List α} → (x y : All P xs) → Dec (x ≡ y)
  | _, .nil, .nil => .yes .refl
  | _, .cons x xs, .cons y ys =>
      ((dec _ x y).product (decide dec xs ys)).map
        (fun p => Identity.cong₂ All.cons p.1 p.2)
        (fun p => (Identity.cong head p, Identity.cong tail p))

end All

end Prelude
