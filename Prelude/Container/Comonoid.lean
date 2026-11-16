import Prelude.Container.Agreement

/-! Comonoids for the composition product, and the state object.

The data of a comonoid for the composition product of containers is a counit and a
comultiplication. A homomorphism of comonoids is a morphism with the counit square and the
comultiplication square, each at each shape. The comultiplication square is an agreement of two
morphisms into a composite at the two layers. Homomorphisms compose.

The state object of a type has a value as a shape, and the next value as a position. A morphism
between two state objects is a lens: its shape map is the view, and its position map is the
update. The state object has a comonoid: the counit keeps the value, and the comultiplication
has the next value as the next shape. A lens is lawful when it is a homomorphism of the two
comonoids. The counit square is the law of the update with the view. The inner shapes of the
comultiplication square are the law of the view of an update, and its positions are the law of
two updates.

Ahman and Uustalu, *Directed Containers as Categories*, has the comonoids of containers. Niu
and Spivak, *Polynomial Functors: A Mathematical Theory of Interaction*, has the comonoid of a
state object and its homomorphisms. -/

set_option autoImplicit false
set_option genInjectivity false

universe s p s' p' s'' p'' u v r

namespace Prelude.Container

/-- The data of a comonoid for the composition product: a counit and a comultiplication. The
laws of a comonoid are not a part of this structure. -/
structure Comonoid (C : Container.{s, p}) where
  counit : Hom C identity
  comult : Hom C (C.comp C)

namespace Comonoid

variable {C : Container.{s, p}} {D : Container.{s', p'}} {E : Container.{s'', p''}}

/-- A homomorphism of comonoids: a morphism with the counit square and the comultiplication
square, each at each shape. -/
structure Morphism (cc : Comonoid C) (dd : Comonoid D) (f : Hom C D) where
  counit : (a : C.Shape) →
    f.position a (dd.counit.position (f.shape a) ()) ≡ cc.counit.position a ()
  comult : Hom.CompAgreement (f.trans dd.comult) (cc.comult.trans (Hom.comp f f))

/-- Homomorphisms of comonoids compose. -/
def Morphism.trans {cc : Comonoid C} {dd : Comonoid D} {ee : Comonoid E} {f : Hom C D}
    {g : Hom D E} (ff : cc.Morphism dd f) (gg : dd.Morphism ee g) :
    cc.Morphism ee (f.trans g) where
  counit a := (Identity.cong (f.position a) (gg.counit (f.shape a))).trans (ff.counit a)
  comult a :=
    Ext.CompAgreement.trans (Ext.CompAgreement.map (f.position a) (gg.comult (f.shape a)))
      (Ext.CompAgreement.comp g g (ff.comult a))

end Comonoid

/-- The state object of a type: a shape is a value, and a position is the next value. -/
abbrev state (A : Type u) : Container.{u, u} := ⟨A, fun _ => A⟩

/-- The comonoid of a state object. The counit keeps the value. The comultiplication has the
next value as the next shape, and the second of two next values as its position. -/
def Comonoid.state (A : Type u) : Comonoid (state A) where
  counit := ⟨fun _ => (), fun a _ => a⟩
  comult := ⟨fun a => ⟨a, fun b => b⟩, fun _ i => i.2⟩

/-- The left unit law of the comonoid of a state object. -/
def Comonoid.stateUnitLeft (A : Type u) :
    (Comonoid.state A).comult.trans (Hom.comp (Comonoid.state A).counit (Hom.id (Container.state A))) ≡
      Hom.unitLeft (Container.state A) :=
  .refl

/-- The right unit law of the comonoid of a state object. -/
def Comonoid.stateUnitRight (A : Type u) :
    (Comonoid.state A).comult.trans (Hom.comp (Hom.id (Container.state A)) (Comonoid.state A).counit) ≡
      Hom.unitRight (Container.state A) :=
  .refl

/-- The associativity of the comonoid of a state object. -/
def Comonoid.stateAssoc (A : Type u) :
    ((Comonoid.state A).comult.trans
        (Hom.comp (Comonoid.state A).comult (Hom.id (Container.state A)))).trans
      (Hom.assoc (Container.state A) (Container.state A) (Container.state A)) ≡
      (Comonoid.state A).comult.trans (Hom.comp (Hom.id (Container.state A)) (Comonoid.state A).comult) :=
  .refl

/-- A lawful lens: a morphism of two state objects that is a homomorphism of their
comonoids. -/
abbrev Hom.Lawful {R : Type r} {A : Type u} (ℓ : Hom (state R) (state A)) : Type (max r u) :=
  (Comonoid.state R).Morphism (Comonoid.state A) ℓ

namespace Hom.Lawful

variable {R : Type r} {A : Type u} {B : Type v} {ℓ : Hom (state R) (state A)}

/-- The update with the view keeps the value: the counit square. -/
def updateView (law : ℓ.Lawful) (s : R) : ℓ.position s (ℓ.shape s) ≡ s :=
  law.counit s

/-- The view of an update is the new value: the inner shapes of the comultiplication
square. -/
def viewUpdate (law : ℓ.Lawful) (s : R) (a : A) : ℓ.shape (ℓ.position s a) ≡ a :=
  (((law.comult s).inner a).trans
    (Identity.cong (fun j => ℓ.shape (ℓ.position s j))
      (Identity.transportConst (law.comult s).outer a))).symm

/-- The second of two updates stays: the positions of the comultiplication square. -/
def updateUpdate (law : ℓ.Lawful) (s : R) (a b : A) :
    ℓ.position (ℓ.position s a) b ≡ ℓ.position s b :=
  (((law.comult s).values a b).trans
    (Identity.cong₂ (fun x y => ℓ.position (ℓ.position s x) y)
      (Identity.transportConst (law.comult s).outer a)
      (Identity.transportConst ((law.comult s).inner a) b))).symm

/-- A lens with the three laws is lawful. -/
def ofLaws (viewUpdate : (s : R) → (a : A) → ℓ.shape (ℓ.position s a) ≡ a)
    (updateView : (s : R) → ℓ.position s (ℓ.shape s) ≡ s)
    (updateUpdate : (s : R) → (a b : A) → ℓ.position (ℓ.position s a) b ≡ ℓ.position s b) :
    ℓ.Lawful where
  counit s := updateView s
  comult s :=
    ⟨.refl, fun a => (viewUpdate s a).symm, fun a b =>
      (updateUpdate s a b).symm.trans
        (Identity.cong (ℓ.position (ℓ.position s a))
          (Identity.transportConst (viewUpdate s a).symm b).symm)⟩

/-- Lawful lenses compose: the composition of two homomorphisms. -/
def trans {f : Hom (state R) (state A)} {g : Hom (state A) (state B)} (ff : f.Lawful)
    (gg : g.Lawful) : (f.trans g).Lawful :=
  Comonoid.Morphism.trans ff gg

end Hom.Lawful

end Prelude.Container
