import Prelude.Identity

/-!
# Relations in `Type`

Type-valued relations: execution paths, accessibility, computations, and loops.

`Steps R a b` is a path of steps of a relation. `Accessible R x` is accessibility with its
evidence in `Type`. `Rel A B` is a computation from `A` to `B`: an element of `F a b` is a run
from the input `a` with the result `b`. `Loop F` is the loop of a body `F : Rel A (B ⊕ A)`: the
family of its finite runs. The loop has its initial property, the agreement with paths, the
fixpoint law, the unrolling, and the maps of strength, naturality, uniformity, and the
codiagonal. The loop of a function body has its domain evidence and its function with fuel.
-/

set_option autoImplicit false
set_option genInjectivity false

universe u v w z r r'

namespace Prelude

/-- Reflexive transitive closure retaining every step witness. Two paths with the same ends can
have different lengths and different steps. -/
inductive Steps {α : Type u} (R : α → α → Type v) : α → α → Type (max u v) where
  /-- The path with no step. -/
  | refl {a : α} : Steps R a a
  /-- One step, and then a path. -/
  | cons {a b c : α} : R a b → Steps R b c → Steps R a c

namespace Steps

variable {α : Type u} {R : α → α → Type v} {a b c d : α}

/-- The path of one step. -/
def single (step : R a b) : Steps R a b := .cons step .refl

/-- Composition in traversal order: first `p`, then `q`. -/
def append {a b c : α} (p : Steps R a b) (q : Steps R b c) : Steps R a c :=
  match p with
  | .refl => q
  | .cons step rest => .cons step (rest.append q)

/-- The number of steps. -/
def length {a b : α} (p : Steps R a b) : Nat :=
  match p with
  | .refl => 0
  | .cons _ rest => rest.length + 1

/-- The path of the images of the steps, for a function of the elements and a map of the
steps. -/
def map {β : Type w} {S : β → β → Type z} {a b : α} (f : α → β)
    (onStep : {x y : α} → R x y → S (f x) (f y)) (p : Steps R a b) :
    Steps S (f a) (f b) :=
  match p with
  | .refl => .refl
  | .cons step rest => .cons (onStep step) (rest.map f onStep)

def appendRefl {a b : α} (p : Steps R a b) : p.append .refl ≡ p :=
  match p with
  | .refl => .refl
  | .cons step rest => Identity.cong (Steps.cons step) rest.appendRefl

def appendAssoc {a b : α} (p : Steps R a b) :
    {c d : α} → (q : Steps R b c) → (r : Steps R c d) →
    (p.append q).append r ≡ p.append (q.append r) :=
  match p with
  | .refl => fun _ _ => .refl
  | .cons step rest => fun q r => Identity.cong (Steps.cons step) (rest.appendAssoc q r)

/-- Forget the trace into any reflexive, transitive Prop-valued relation. -/
theorem foldProp {S : α → α → Prop} (refl : ∀ x, S x x)
    (trans : ∀ {x y z}, S x y → S y z → S x z)
    (step : ∀ {x y}, R x y → S x y) (p : Steps R a b) : S a b := by
  induction p with
  | refl => exact refl _
  | cons h _ ih => exact trans (step h) ih

end Steps

/-- Accessibility with predecessor evidence in `Type`. -/
inductive Accessible {α : Type u} (R : α → α → Type v) : α → Type (max u v) where
  | intro {x : α} : ((y : α) → R y x → Accessible R y) → Accessible R x

namespace Accessible

variable {α : Type u} {R : α → α → Type v}

def inv {x y : α} (acc : Accessible R x) (step : R y x) : Accessible R y :=
  match acc with
  | .intro next => next y step

/-- Recursion on a supplied accessibility witness. -/
def fold {P : α → Sort w}
    (step : (x : α) → ((y : α) → R y x → P y) → P x)
    (x : α) (acc : Accessible R x) : P x :=
  match acc with
  | .intro next => step x (fun y r => fold step y (next y r))

end Accessible

/-- A relation is well-founded when each element is accessible. -/
abbrev TypeWellFounded {α : Type u} (R : α → α → Type v) :=
  (x : α) → Accessible R x

/-! ### Computations -/

/-- A computation from `A` to `B` is a Type-valued relation. An element of `F a b` is a run
from the input `a` with the result `b`. The inputs, the results, and the runs have independent
universe levels. -/
abbrev Rel (A : Type u) (B : Type v) : Type (max u v (r + 1)) := A → B → Type r

namespace Rel

variable {A : Type u} {B : Type v} {C : Type w}

/-- The graph of a function. -/
abbrev graph (f : A → B) : Rel A B := fun a b => f a ≡ b

protected abbrev id : Rel A A := fun a a' => a ≡ a'

/-- Composition in traversal order: first `F`, then `G`. -/
abbrev seq (F : Rel.{u, v, r} A B) (G : Rel.{v, w, r'} B C) : Rel A C :=
  fun a c => (b : B) × (F a b × G b c)

/-- The copairing of two computations: the map out of the control sum. Each case lifts its
runs to the common level of the two computations. -/
def copair (G : Rel.{v, w, r} B C) (H : Rel.{u, w, r'} A C) : Rel (B ⊕ A) C
  | .inl b => fun c => ULift.{r'} (G b c)
  | .inr a => fun c => ULift.{r} (H a c)

/-- Two computations agree when their run families are equivalent. -/
abbrev Agreement (F : Rel.{u, v, r} A B) (G : Rel.{u, v, r'} A B) : Type (max u v r r') :=
  (a : A) → (b : B) → Iso (F a b) (G a b)

/-- The runs of a computation at a higher level. -/
abbrev lift (F : Rel.{u, v, r} A B) : Rel.{u, v, max r r'} A B := fun a b => ULift.{r'} (F a b)

/-- A run of the graph of a function and then a computation is the run that its run of the
computation gives. -/
def graphSeqInvTo (f : A → B) (G : Rel.{v, w, r} B C) {a : A} {c : C}
    (x : seq (lift.{u, v, v, r'} (graph f)) G a c) :
    (⟨f a, ⟨.refl⟩, Identity.transport (fun b => G b c) x.2.1.down.symm x.2.2⟩ :
      seq (lift.{u, v, v, r'} (graph f)) G a c) ≡ x :=
  Identity.ind
    (fun (b : B) (e : f a ≡ b) => (g : G b c) →
      (⟨f a, ⟨.refl⟩, Identity.transport (fun b => G b c) e.symm g⟩ :
        seq (lift.{u, v, v, r'} (graph f)) G a c) ≡ ⟨b, ⟨e⟩, g⟩)
    (fun _ => .refl) x.2.1.down x.2.2

/-- The graph of a function and then a computation agrees with the computation at the value of
the function. The runs of the graph can be at a higher level. -/
def graphSeq (f : A → B) (G : Rel.{v, w, r} B C) :
    Agreement (seq (lift.{u, v, v, r'} (graph f)) G) (fun a c => G (f a) c) := fun a c =>
  { to := fun x => Identity.transport (fun b => G b c) x.2.1.down.symm x.2.2
    inv := fun g => ⟨f a, ⟨.refl⟩, g⟩
    invTo := graphSeqInvTo f G
    toInv := fun _ => .refl }

/-- The continue case of a loop body, as a relation on the inputs. -/
abbrev continues (F : Rel.{u, max v u, r} A (B ⊕ A)) : A → A → Type r := fun a a' => F a (.inr a')

/-- `F ; [inl, F]`, the body run twice, with the exit case in normal form: the first run
exits, or the first run continues and the second run selects the case. -/
def twice (F : Rel.{u, max v u, r} A (B ⊕ A)) : Rel A (B ⊕ A) :=
  fun a s =>
    Sum.{r, max u r}
      (match s with
        | .inl b => F a (.inl b)
        | .inr _ => PEmpty.{r + 1})
      ((a' : A) × (F a (.inr a') × F a' s))

/-- `K + id`: a computation on the exit case of a body, and the identity on the continue
case. Each case lifts its runs to the common level of `K` and the identity. -/
def onExit (K : Rel.{v, w, r} B C) : Rel.{max v u, max w u, max u r} (B ⊕ A) (C ⊕ A)
  | .inl b, .inl c => ULift.{u} (K b c)
  | .inr a, .inr a' => ULift.{r} (a ≡ a')
  | .inl _, .inr _ => PEmpty
  | .inr _, .inl _ => PEmpty

/-- `C × F`: the body beside a context that it does not change. -/
def withContext (F : Rel A (B ⊕ A)) : Rel (C × A) ((C × B) ⊕ (C × A)) :=
  fun x s => match s with
    | .inl y => (x.1 ≡ y.1) × F x.2 (.inl y.2)
    | .inr x' => (x.1 ≡ x'.1) × F x.2 (.inr x'.2)

/-- `G ; [id, inr]`: a body with two continue cases, as a body with one continue case. -/
abbrev merged (G : Rel A ((B ⊕ A) ⊕ A)) : Rel A (B ⊕ A) :=
  fun a s => (t : (B ⊕ A) ⊕ A) × (G a t × (Sum.elim id Sum.inr t ≡ s))

end Rel

/-! ### Loops -/

/-- The loop of a body `F : A → B + A` is the family of its finite runs. A run exits with a
result, or it continues to a next input and the rest runs from that input. A run contains
inputs, a result, and runs of the body, so its level is the maximum of the three levels. -/
inductive Loop {A : Type u} {B : Type v} (F : Rel.{u, max v u, r} A (B ⊕ A)) :
    A → B → Type (max u v r) where
  /-- An exit run of the body. -/
  | exit {a : A} {b : B} : F a (.inl b) → Loop F a b
  /-- A continue run of the body, and the run from the next input. -/
  | next {a a' : A} {b : B} : F a (.inr a') → Loop F a' b → Loop F a b

namespace Loop

variable {A : Type u} {B : Type v} {C : Type w}

/-- The number of runs of the body. -/
def length {F : Rel A (B ⊕ A)} : {a : A} → {b : B} → Loop F a b → Nat
  | _, _, .exit _ => 1
  | _, _, .next _ r => r.length + 1

/-! #### The initial property -/

/-- The map from the loop to a family that the exit rule and the continue rule close. -/
def elim {F : Rel A (B ⊕ A)} {R : A → B → Type w}
    (base : (a : A) → (b : B) → F a (.inl b) → R a b)
    (step : (a a' : A) → (b : B) → F a (.inr a') → R a' b → R a b) :
    {a : A} → {b : B} → Loop F a b → R a b
  | _, _, .exit p => base _ _ p
  | _, _, .next p r => step _ _ _ p (elim base step r)

/-- A map that commutes with the two rules is `elim`, at each run. -/
def elimUnique {F : Rel A (B ⊕ A)} {R : A → B → Type w}
    (base : (a : A) → (b : B) → F a (.inl b) → R a b)
    (step : (a a' : A) → (b : B) → F a (.inr a') → R a' b → R a b)
    (h : {a : A} → {b : B} → Loop F a b → R a b)
    (onExit : (a : A) → (b : B) → (p : F a (.inl b)) → h (.exit p) ≡ base a b p)
    (onNext : (a a' : A) → (b : B) → (p : F a (.inr a')) → (r : Loop F a' b) →
      h (.next p r) ≡ step a a' b p (h r)) :
    {a : A} → {b : B} → (r : Loop F a b) → h r ≡ elim base step r
  | _, _, .exit p => onExit _ _ p
  | _, _, .next p r =>
    (onNext _ _ _ p r).trans
      (Identity.cong (step _ _ _ p) (elimUnique base step h onExit onNext r))

/-! #### Agreement of bodies -/

/-- A map of the bodies gives a map of the loops. -/
def map {F : Rel.{u, max v u, r} A (B ⊕ A)} {G : Rel.{u, max v u, r'} A (B ⊕ A)}
    (f : (a : A) → (s : B ⊕ A) → F a s → G a s) : {a : A} → {b : B} → Loop F a b → Loop G a b :=
  elim (fun _ b p => .exit (f _ (.inl b) p)) (fun _ a' _ p l => .next (f _ (.inr a') p) l)

/-- Two maps of the bodies whose composite is the identity at each run give maps of the loops
whose composite is the identity at each run. -/
def mapMap {F : Rel.{u, max v u, r} A (B ⊕ A)} {G : Rel.{u, max v u, r'} A (B ⊕ A)}
    (f : (a : A) → (s : B ⊕ A) → F a s → G a s) (g : (a : A) → (s : B ⊕ A) → G a s → F a s)
    (gf : (a : A) → (s : B ⊕ A) → (p : F a s) → g a s (f a s p) ≡ p) :
    {a : A} → {b : B} → (l : Loop F a b) → map g (map f l) ≡ l
  | _, _, .exit p => Identity.cong Loop.exit (gf _ _ p)
  | _, _, .next p l => Identity.cong₂ Loop.next (gf _ _ p) (mapMap f g gf l)

/-- Bodies that agree have loops that agree. -/
def agreement {F : Rel.{u, max v u, r} A (B ⊕ A)} {G : Rel.{u, max v u, r'} A (B ⊕ A)}
    (e : Rel.Agreement F G) : Rel.Agreement (Loop F) (Loop G) := fun _ _ =>
  { to := map fun a s => (e a s).to
    inv := map fun a s => (e a s).inv
    invTo := mapMap (fun a s => (e a s).to) (fun a s => (e a s).inv) fun a s => (e a s).invTo
    toInv := mapMap (fun a s => (e a s).inv) (fun a s => (e a s).to) fun a s => (e a s).toInv }

/-! #### Runs as paths -/

/-- A path of continue steps and one exit step. -/
abbrev Path (F : Rel A (B ⊕ A)) : Rel A B :=
  fun a b => (a' : A) × (Steps F.continues a a' × F a' (.inl b))

def toPath {F : Rel A (B ⊕ A)} : {a : A} → {b : B} → Loop F a b → Path F a b
  | a, _, .exit p => ⟨a, .refl, p⟩
  | _, _, .next p r => ⟨(toPath r).1, .cons p (toPath r).2.1, (toPath r).2.2⟩

def ofSteps {F : Rel A (B ⊕ A)} {b : B} :
    {a a' : A} → Steps F.continues a a' → F a' (.inl b) → Loop F a b
  | _, _, .refl, e => .exit e
  | _, _, .cons p rest, e => .next p (ofSteps rest e)

def ofStepsToPath {F : Rel A (B ⊕ A)} : {a : A} → {b : B} → (r : Loop F a b) →
    ofSteps (toPath r).2.1 (toPath r).2.2 ≡ r
  | _, _, .exit _ => .refl
  | _, _, .next p r => Identity.cong (Loop.next p) (ofStepsToPath r)

def toPathOfSteps {F : Rel A (B ⊕ A)} {b : B} :
    {a a' : A} → (steps : Steps F.continues a a') → (e : F a' (.inl b)) →
    toPath (ofSteps steps e) ≡ (⟨a', steps, e⟩ : Path F a b)
  | _, _, .refl, _ => .refl
  | _, _, .cons p rest, e =>
    Identity.cong (fun q : Path F _ b => (⟨q.1, .cons p q.2.1, q.2.2⟩ : Path F _ b))
      (toPathOfSteps rest e)

/-- The loop agrees with the paths of continue steps that end with an exit step. -/
def path (F : Rel A (B ⊕ A)) : Rel.Agreement (Loop F) (Path F) := fun _ _ =>
  { to := toPath
    inv := fun q => ofSteps q.2.1 q.2.2
    invTo := ofStepsToPath
    toInv := fun q => toPathOfSteps q.2.1 q.2.2 }

/-! #### Fixpoint -/

/-- `F ; [id, Loop F]`: one run of the body, and the loop in the continue case. -/
abbrev Unfolded (F : Rel A (B ⊕ A)) : Rel A B := Rel.seq F (Rel.copair Rel.id (Loop F))

def unfold {F : Rel A (B ⊕ A)} : {a : A} → {b : B} → Loop F a b → Unfolded F a b
  | _, b, .exit p => ⟨.inl b, p, ⟨(Identity.refl : b ≡ b)⟩⟩
  | _, _, .next p r => ⟨.inr _, p, ⟨r⟩⟩

def fold {F : Rel A (B ⊕ A)} {a : A} {b : B} :
    (s : B ⊕ A) → F a s → Rel.copair Rel.id (Loop F) s b → Loop F a b
  | .inl _, p, q => .exit (Identity.transport (fun v => F a (.inl v)) q.down p)
  | .inr _, p, r => .next p r.down

def foldUnfold {F : Rel A (B ⊕ A)} : {a : A} → {b : B} → (r : Loop F a b) →
    fold (unfold r).1 (unfold r).2.1 (unfold r).2.2 ≡ r
  | _, _, .exit _ => .refl
  | _, _, .next _ _ => .refl

def unfoldFoldExit {F : Rel A (B ⊕ A)} {a : A} {b' b : B} (p : F a (.inl b')) (q : b' ≡ b) :
    unfold (fold (F := F) (.inl b') p ⟨q⟩) ≡ (⟨.inl b', p, ⟨q⟩⟩ : Unfolded F a b) :=
  Identity.ind
    (fun b q => unfold (fold (F := F) (.inl b') p ⟨q⟩) ≡ (⟨.inl b', p, ⟨q⟩⟩ : Unfolded F a b))
    .refl q

def unfoldFold {F : Rel A (B ⊕ A)} {a : A} {b : B} :
    (s : B ⊕ A) → (p : F a s) → (q : Rel.copair Rel.id (Loop F) s b) →
    unfold (fold s p q) ≡ (⟨s, p, q⟩ : Unfolded F a b)
  | .inl _, p, q => unfoldFoldExit p q.down
  | .inr _, _, _ => .refl

/-- The fixpoint law: `Loop F` agrees with `F ; [id, Loop F]`. -/
def fixpoint (F : Rel A (B ⊕ A)) : Rel.Agreement (Loop F) (Unfolded F) := fun _ _ =>
  { to := unfold
    inv := fun x => fold x.1 x.2.1 x.2.2
    invTo := foldUnfold
    toInv := fun x => unfoldFold x.1 x.2.1 x.2.2 }

/-! #### Unrolling -/

def unroll {F : Rel A (B ⊕ A)} : {a : A} → {b : B} → Loop F a b → Loop F.twice a b
  | _, _, .exit p => .exit (.inl p)
  | _, _, .next (a' := a') p (.exit p') => .exit (.inr ⟨a', p, p'⟩)
  | _, _, .next (a' := a') p (.next p' r) => .next (.inr ⟨a', p, p'⟩) (unroll r)

def rerollExit {F : Rel A (B ⊕ A)} {a : A} {b : B} : F.twice a (.inl b) → Loop F a b
  | .inl p => .exit p
  | .inr ⟨_, p, p'⟩ => .next p (.exit p')

def rerollNext {F : Rel A (B ⊕ A)} {a a₂ : A} {b : B} (rest : Loop F a₂ b) :
    F.twice a (.inr a₂) → Loop F a b
  | .inl e => (e : PEmpty).elim
  | .inr ⟨_, p, p'⟩ => .next p (.next p' rest)

def reroll {F : Rel A (B ⊕ A)} : {a : A} → {b : B} → Loop F.twice a b → Loop F a b
  | _, _, .exit x => rerollExit x
  | _, _, .next x r => rerollNext (reroll r) x

def rerollUnroll {F : Rel A (B ⊕ A)} : {a : A} → {b : B} → (r : Loop F a b) →
    reroll (unroll r) ≡ r
  | _, _, .exit _ => .refl
  | _, _, .next _ (.exit _) => .refl
  | _, _, .next p (.next p' r) =>
    Identity.cong (fun x => Loop.next p (Loop.next p' x)) (rerollUnroll r)

def unrollRerollExit {F : Rel A (B ⊕ A)} {a : A} {b : B} :
    (x : F.twice a (.inl b)) → unroll (rerollExit x) ≡ Loop.exit x
  | .inl _ => .refl
  | .inr ⟨_, _, _⟩ => .refl

def unrollRerollNext {F : Rel A (B ⊕ A)} {a a₂ : A} {b : B}
    (rest : Loop F a₂ b) (q : Loop F.twice a₂ b) (ih : unroll rest ≡ q) :
    (x : F.twice a (.inr a₂)) → unroll (rerollNext rest x) ≡ Loop.next x q
  | .inl e => (e : PEmpty).elim
  | .inr ⟨a', p, p'⟩ =>
    Identity.cong (fun y => Loop.next (F := F.twice) (.inr ⟨a', p, p'⟩) y) ih

def unrollReroll {F : Rel A (B ⊕ A)} : {a : A} → {b : B} → (q : Loop F.twice a b) →
    unroll (reroll q) ≡ q
  | _, _, .exit x => unrollRerollExit x
  | _, _, .next x r => unrollRerollNext (reroll r) r (unrollReroll r) x

/-- Unrolling: the loop of a body agrees with the loop of the body run twice. A run of
length `n` corresponds to a run of length `⌈n / 2⌉`. -/
def unrolling (F : Rel A (B ⊕ A)) : Rel.Agreement (Loop F) (Loop F.twice) := fun _ _ =>
  ⟨unroll, reroll, rerollUnroll, unrollReroll⟩

/-! #### Strength -/

/-- A run of the loop of a body beside a context is a run of the loop of the body, with the
identity of the context at the input and at the result. -/
def strengthTo {F : Rel A (B ⊕ A)} :
    {x : C × A} → {y : C × B} → Loop (Rel.withContext F) x y → (x.1 ≡ y.1) × Loop F x.2 y.2
  | x, y, .exit p =>
    let q : (x.1 ≡ y.1) × F x.2 (.inl y.2) := p
    ⟨q.1, .exit q.2⟩
  | x, _, .next (a' := x') p r =>
    let q : (x.1 ≡ x'.1) × F x.2 (.inr x'.2) := p
    ⟨q.1.trans (strengthTo r).1, .next q.2 (strengthTo r).2⟩

/-- A run of the loop of a body is a run of the loop of the body beside each context. -/
def strengthFrom {F : Rel A (B ⊕ A)} (c : C) :
    {a : A} → {b : B} → Loop F a b → Loop (Rel.withContext F) (c, a) (c, b)
  | a, b, .exit p =>
    .exit (show (c ≡ c) × F a (.inl b) from ⟨.refl, p⟩)
  | a, _, .next (a' := a') p r =>
    .next (a' := (c, a')) (show (c ≡ c) × F a (.inr a') from ⟨.refl, p⟩) (strengthFrom c r)

/-- A run beside a context gives the same run after the two strength maps. -/
def strengthToFrom {F : Rel A (B ⊕ A)} (c : C) : {a : A} → {b : B} → (r : Loop F a b) →
    strengthTo (strengthFrom c r) ≡ ((⟨.refl, r⟩ : (c ≡ c) × Loop F a b))
  | _, _, .exit _ => .refl
  | _, b, .next (a' := a') p r =>
    Identity.cong
      (fun z : (c ≡ c) × Loop F a' b =>
        ((⟨Identity.refl.trans z.1, Loop.next p z.2⟩ : (c ≡ c) × Loop F _ b)))
      (strengthToFrom c r)

/-! #### Naturality -/

def naturalExit {F : Rel A (B ⊕ A)} {K : Rel B C} {a : A} {c : C} :
    (s : B ⊕ A) → F a s → Rel.onExit (A := A) K s (.inl c) → (b : B) × (Loop F a b × K b c)
  | .inl b, p, k => ⟨b, .exit p, k.down⟩
  | .inr _, _, k => (k : PEmpty).elim

def naturalNext {F : Rel A (B ⊕ A)} {K : Rel B C} {a a' : A} {c : C}
    (rest : (b : B) × (Loop F a' b × K b c)) :
    (s : B ⊕ A) → F a s → Rel.onExit (A := A) K s (.inr a') → (b : B) × (Loop F a b × K b c)
  | .inl _, _, k => (k : PEmpty).elim
  | .inr _, p, k =>
    ⟨rest.1, .next (Identity.transport (fun v => F a (.inr v)) k.down p) rest.2.1, rest.2.2⟩

/-- A run of the loop of `F ; (K + id)` is a run of the loop of `F` and then a run of `K`. -/
def naturalTo {F : Rel A (B ⊕ A)} {K : Rel B C} :
    {a : A} → {c : C} → Loop (Rel.seq F (Rel.onExit K)) a c → Rel.seq (Loop F) K a c
  | _, _, .exit p => naturalExit p.1 p.2.1 p.2.2
  | _, _, .next p r => naturalNext (naturalTo r) p.1 p.2.1 p.2.2

/-- A run of the loop of `F` and then a run of `K` is a run of the loop of `F ; (K + id)`. -/
def naturalFrom {F : Rel A (B ⊕ A)} {K : Rel B C} {c : C} :
    {a : A} → {b : B} → Loop F a b → K b c → Loop (Rel.seq F (Rel.onExit K)) a c
  | _, b, .exit p, k => .exit ⟨.inl b, p, ⟨k⟩⟩
  | _, _, .next (a' := a') p r, k =>
    .next ⟨.inr a', p, ⟨(Identity.refl : a' ≡ a')⟩⟩ (naturalFrom r k)

/-! #### Uniformity for a pure map -/

/-- A body `G` on `C` that a function `h : C → A` carries to the body `F`: each run of the
loop of `G` from `z` is a run of the loop of `F` from `h z`. -/
def uniformTo (h : C → A) {F : Rel A (B ⊕ A)} {G : Rel C (B ⊕ C)}
    (forward : (z : C) → (s : B ⊕ C) → G z s → F (h z) (Sum.map id h s)) :
    {z : C} → {b : B} → Loop G z b → Loop F (h z) b
  | _, _, .exit p => .exit (forward _ _ p)
  | _, _, .next p r => .next (forward _ _ p) (uniformTo h forward r)

def uniformExit (h : C → A) {G : Rel C (B ⊕ C)} {z : C} {b : B} :
    (s : B ⊕ C) → G z s → Sum.map id h s ≡ .inl b → Loop G z b
  | .inl _, g, e => .exit (Identity.transport (fun v => G z (.inl v)) (Identity.inlInject e) g)
  | .inr _, _, e => (Identity.inrNotInl e).elim

def uniformNext (h : C → A) {G : Rel C (B ⊕ C)} {z : C} {b : B} {a' : A}
    (rest : (z' : C) → a' ≡ h z' → Loop G z' b) :
    (s : B ⊕ C) → G z s → Sum.map id h s ≡ .inr a' → Loop G z b
  | .inl _, _, e => (Identity.inlNotInr e).elim
  | .inr z', g, e => .next g (rest z' (Identity.inrInject e).symm)

/-- The converse map. Each run of the body `F` from `h z` has a run of the body `G` from `z`
whose case goes to its case under `h`. Then each run of the loop of `F` from `h z` is a run of
the loop of `G` from `z`. -/
def uniformFrom (h : C → A) {F : Rel A (B ⊕ A)} {G : Rel C (B ⊕ C)}
    (backward : (z : C) → (t : B ⊕ A) → F (h z) t →
      (s : B ⊕ C) × (G z s × (Sum.map id h s ≡ t))) :
    {a : A} → {b : B} → Loop F a b → (z : C) → a ≡ h z → Loop G z b
  | _, b, .exit p, z, e =>
    let r := backward z (.inl b) (Identity.transport (fun v => F v (.inl b)) e p)
    uniformExit h r.1 r.2.1 r.2.2
  | _, _, .next (a' := a') p l, z, e =>
    let r := backward z (.inr a') (Identity.transport (fun v => F v (.inr a')) e p)
    uniformNext h (fun z' e' => uniformFrom h backward l z' e') r.1 r.2.1 r.2.2

/-! #### Codiagonal -/

def prepend {G : Rel A ((B ⊕ A) ⊕ A)} {a a' : A} {b : B} (g : G a (.inr a')) :
    Loop (Loop G) a' b → Loop (Loop G) a b
  | .exit p => .exit (.next g p)
  | .next p r => .next (.next g p) r

def codiagonalExit {G : Rel A ((B ⊕ A) ⊕ A)} {a : A} {b : B} :
    (t : (B ⊕ A) ⊕ A) → G a t → Sum.elim id Sum.inr t ≡ .inl b → Loop (Loop G) a b
  | .inl (.inl _), g, e =>
    .exit (.exit (Identity.transport (fun v => G a (.inl (.inl v))) (Identity.inlInject e) g))
  | .inl (.inr _), _, e => (Identity.inrNotInl e).elim
  | .inr _, _, e => (Identity.inrNotInl e).elim

def codiagonalNext {G : Rel A ((B ⊕ A) ⊕ A)} {a a' : A} {b : B} (rest : Loop (Loop G) a' b) :
    (t : (B ⊕ A) ⊕ A) → G a t → Sum.elim id Sum.inr t ≡ .inr a' → Loop (Loop G) a b
  | .inl (.inl _), _, e => (Identity.inlNotInr e).elim
  | .inl (.inr _), g, e =>
    .next (.exit (Identity.transport (fun v => G a (.inl (.inr v))) (Identity.inrInject e) g)) rest
  | .inr _, g, e =>
    prepend (Identity.transport (fun v => G a (.inr v)) (Identity.inrInject e) g) rest

/-- A run of the loop of the merged body is a run of the loop of the inner loop. -/
def codiagonalTo {G : Rel A ((B ⊕ A) ⊕ A)} :
    {a : A} → {b : B} → Loop (Rel.merged G) a b → Loop (Loop G) a b
  | _, _, .exit p => codiagonalExit p.1 p.2.1 p.2.2
  | _, _, .next p r => codiagonalNext (codiagonalTo r) p.1 p.2.1 p.2.2

def codiagonalInner {G : Rel A ((B ⊕ A) ⊕ A)} {b : B} :
    {a : A} → (s : B ⊕ A) → Loop G a s → Rel.copair Rel.id (Loop (Rel.merged G)) s b →
    Loop (Rel.merged G) a b
  | _, .inl b', .exit g, k =>
    .exit ⟨.inl (.inl b'), g, Identity.cong Sum.inl k.down⟩
  | _, .inr a', .exit g, k =>
    .next ⟨.inl (.inr a'), g, (Identity.refl : (Sum.inr a' : B ⊕ A) ≡ .inr a')⟩ k.down
  | _, s, .next (a' := a'') g p, k =>
    .next ⟨.inr a'', g, (Identity.refl : (Sum.inr a'' : B ⊕ A) ≡ .inr a'')⟩
      (codiagonalInner s p k)

/-- A run of the loop of the inner loop is a run of the loop of the merged body. -/
def codiagonalFrom {G : Rel A ((B ⊕ A) ⊕ A)} :
    {a : A} → {b : B} → Loop (Loop G) a b → Loop (Rel.merged G) a b
  | _, b, .exit p => codiagonalInner (.inl b) p ⟨(Identity.refl : b ≡ b)⟩
  | _, _, .next (a' := a') p r => codiagonalInner (.inr a') p ⟨codiagonalFrom r⟩

/-! #### The loop of a function -/

/-- The domain of the loop of a function body: the inputs from which the loop stops. -/
inductive Domain {A : Type u} {B : Type v} (f : A → B ⊕ A) : A → Type (max u v) where
  | exit {a : A} {b : B} : f a ≡ .inl b → Domain f a
  | next {a a' : A} : f a ≡ .inr a' → Domain f a' → Domain f a

namespace Domain

/-- The result of the loop, by recursion on the domain evidence. -/
def eval {f : A → B ⊕ A} : {a : A} → Domain f a → B
  | _, .exit (b := b) _ => b
  | _, .next _ d => d.eval

/-- The run of the loop that the domain evidence gives, with the result `d.eval`. -/
def run {f : A → B ⊕ A} : {a : A} → (d : Domain f a) → Loop (Rel.graph f) a d.eval
  | _, .exit p => .exit p
  | _, .next p d => .next p d.run

def step (f : A → B ⊕ A) {a : A} (rest : (a' : A) → f a ≡ .inr a' → Domain f a') :
    (s : B ⊕ A) → f a ≡ s → Domain f a
  | .inl _, e => .exit e
  | .inr a', e => .next e (rest a' e)

/-- Accessibility for the continue steps gives the domain evidence. -/
def ofAccessible (f : A → B ⊕ A) :
    {a : A} → Accessible (fun a' a => f a ≡ .inr a') a → Domain f a
  | a, .intro earlier => step f (fun a' e => ofAccessible f (earlier a' e)) (f a) .refl

/-- A measure that each continue step decreases gives the domain evidence. -/
def ofMeasure (f : A → B ⊕ A) (measure : A → Nat)
    (decreases : (a a' : A) → f a ≡ .inr a' → measure a' < measure a) :
    (n : Nat) → (a : A) → measure a < n → Domain f a
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, a, h =>
    step f (fun a' e => ofMeasure f measure decreases n a'
      (Nat.lt_of_lt_of_le (decreases a a' e) (Nat.le_of_lt_succ h))) (f a) .refl

def exitUnique {f : A → B ⊕ A} {a : A} {b b' : B} (p : f a ≡ .inl b) (p' : f a ≡ .inl b')
    (fiber : Identity.InlFiber (f a) p p') : Domain.exit p ≡ Domain.exit p' :=
  Identity.ind
    (fun b' e => (p' : f a ≡ .inl b') →
      Identity.transport (fun z => f a ≡ .inl z) e p ≡ p' → Domain.exit p ≡ Domain.exit p')
    (fun _ h => Identity.cong Domain.exit h) fiber.1 p' fiber.2

def nextUnique {f : A → B ⊕ A} {a : A} {a₁ a₂ : A} (p : f a ≡ .inr a₁) (p' : f a ≡ .inr a₂)
    (d : Domain f a₁) (d' : Domain f a₂) (fiber : Identity.InrFiber (f a) p p')
    (ih : (d'' : Domain f a₁) → d ≡ d'') : Domain.next p d ≡ Domain.next p' d' :=
  Identity.ind
    (fun a₂ e => (p' : f a ≡ .inr a₂) → (d' : Domain f a₂) →
      Identity.transport (fun z => f a ≡ .inr z) e p ≡ p' → Domain.next p d ≡ Domain.next p' d')
    (fun _ d' h => Identity.cong₂ Domain.next h (ih d')) fiber.1 p' d' fiber.2

/-- The domain evidence at an input is a proposition. -/
def unique {f : A → B ⊕ A} : {a : A} → IsProp (Domain f a)
  | _, .exit p, .exit p' => exitUnique p p' (Identity.inlFiber p p')
  | _, .exit p, .next p' _ => (Identity.inlNotInr (p.symm.trans p')).elim
  | _, .next p _, .exit p' => (Identity.inlNotInr (p'.symm.trans p)).elim
  | _, .next p d, .next p' d' =>
    nextUnique p p' d d' (Identity.inrFiber p p') (fun d'' => unique d d'')

end Domain

/-- A run of the loop of a function gives the domain evidence at its input. -/
def domain {f : A → B ⊕ A} : {a : A} → {b : B} → Loop (Rel.graph f) a b → Domain f a
  | _, _, .exit p => .exit p
  | _, _, .next p r => .next p r.domain

/-- The result from the domain evidence of a run is the result of the run. -/
def domainEval {f : A → B ⊕ A} :
    {a : A} → {b : B} → (r : Loop (Rel.graph f) a b) → r.domain.eval ≡ b
  | _, _, .exit _ => .refl
  | _, _, .next _ r => r.domainEval

/-- The loop of a function has one result at each input. -/
def resultUnique {f : A → B ⊕ A} :
    {a : A} → {b b' : B} → Loop (Rel.graph f) a b → Loop (Rel.graph f) a b' → b ≡ b'
  | _, _, _, .exit p, .exit p' => Identity.inlInject (p.symm.trans p')
  | _, _, _, .exit p, .next p' _ => (Identity.inlNotInr (p.symm.trans p')).elim
  | _, _, _, .next p _, .exit p' => (Identity.inlNotInr (p'.symm.trans p)).elim
  | _, _, _, .next p r, .next p' r' =>
    resultUnique r
      (Identity.transport (fun x => Loop (Rel.graph f) x _)
        (Identity.inrInject (p'.symm.trans p)) r')

/-- The loop of a function with fuel: at most `n` runs of the body. -/
def fuel (f : A → B ⊕ A) : Nat → A → Option B
  | 0, _ => none
  | n + 1, a => Sum.elim some (fuel f n) (f a)

def fuelSoundStep (f : A → B ⊕ A) (k : A → Option B)
    (ih : (a' : A) → (b : B) → k a' ≡ some b → Loop (Rel.graph f) a' b) {a : A} {b : B} :
    (s : B ⊕ A) → f a ≡ s → Sum.elim some k s ≡ some b → Loop (Rel.graph f) a b
  | .inl _, p, q => .exit (p.trans (Identity.cong Sum.inl (Identity.someInject q)))
  | .inr a', p, q => .next p (ih a' b q)

/-- A result of the function with fuel has a run. -/
def fuelSound (f : A → B ⊕ A) :
    (n : Nat) → (a : A) → (b : B) → fuel f n a ≡ some b → Loop (Rel.graph f) a b
  | 0, _, _, h => (Identity.noneNotSome h).elim
  | n + 1, a, _, h => fuelSoundStep f (fuel f n) (fuelSound f n) (f a) .refl h

/-- A run gives the fuel that the function needs: the length of the run. -/
def fuelComplete (f : A → B ⊕ A) :
    {a : A} → {b : B} → (r : Loop (Rel.graph f) a b) → fuel f r.length a ≡ some b
  | _, _, .exit p => Identity.cong (Sum.elim some (fuel f 0)) p
  | _, _, .next p r =>
    (Identity.cong (Sum.elim some (fuel f r.length)) p).trans (fuelComplete f r)

end Loop

end Prelude
