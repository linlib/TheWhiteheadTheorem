
def n : Int := 1


def reflexivity {X : Type} {x : X} (p : x = x) := Eq.refl p


def symmetry {X : Type} {x : X} {y : X}  (p : x = y) := Eq.symm p


def transitivity {X : Type} {x : X} {y : X} {z : X} (p : x = y) (q : y = z) := Eq.trans p q


def extensionality (f g : X → Y) (p : (x:X) → f x = g x) : f = g := funext p


def equal_arguments {X : Type} {Y : Type} {a : X} {b : X} (f : X → Y) (p : a = b) : f a = f b := congrArg f p

def equal_functions {X : Type} {Y : Type} {f₁ : X → Y} {f₂ : X → Y} (p : f₁ = f₂) (x : X) : f₁ x = f₂ x := congrFun p x

def pairwise {A : Type} {B : Type} (a₁ : A) (a₂ : A) (b₁ : B) (b₂ : B) (p : a₁ = a₂) (q : b₁ = b₂) : (a₁,b₁)=(a₂,b₂) := (congr ((congrArg Prod.mk) p) q)


-- A category C consists of:
structure category.{u₀,v₀} where
  Obj : Type u₀
  Hom : Obj → Obj → Type v₀
  Idn : (X:Obj) → Hom X X
  Cmp : (X:Obj) → (Y:Obj) → (Z:Obj) → (_:Hom X Y) → (_:Hom Y Z) → Hom X Z
  Id₁ : (X:Obj) → (Y:Obj) → (f:Hom X Y) →
    Cmp X Y Y f (Idn Y) = f
  Id₂ : (X:Obj) → (Y:Obj) → (f:Hom X Y) →
    Cmp X X Y (Idn X) f = f
  Ass : (W:Obj) → (X:Obj) → (Y:Obj) → (Z:Obj) → (f:Hom W X) → (g:Hom X Y) → (h:Hom Y Z) →
    (Cmp W X Z) f (Cmp X Y Z g h) = Cmp W Y Z (Cmp W X Y f g) h


-- Notation for the identity map which infers the category:
def identity_map (C : category) (X : C.Obj) := C.Idn X
notation "𝟙_(" C ")" => identity_map C



-- Notation for composition which infers the category and objects:
def composition (C : category) {X : C.Obj} {Y : C.Obj} {Z : C.Obj} (f : C.Hom X Y) (g : C.Hom Y Z) : C.Hom X Z := C.Cmp X Y Z f g
notation g "∘_(" C ")" f => composition C f g


theorem Id₁ {C : category} {X : C.Obj} { Y : C.Obj} {f : C.Hom X Y} :
  (f ∘_(C) (𝟙_(C) X)) = f := C.Id₂ X Y f

theorem Id₂ {C : category} {X Y : C.Obj} {f : C.Hom X Y} :
  (𝟙_(C) Y ∘_(C) f) = f := C.Id₁ X Y f

theorem Ass {C : category} {W X Y Z : C.Obj} {f : C.Hom W X} {g : C.Hom X Y} {h : C.Hom Y Z} :
  ((h ∘_(C) g) ∘_(C) f) = (h ∘_(C) (g ∘_(C) f)) := (C.Ass W X Y Z f g h)


macro "cat" : tactic => `(tactic| repeat (rw [Id₁]) ; repeat (rw [Id₂]) ; repeat (rw [Ass]))

example {C : category}
          {W : C.Obj}
          {X : C.Obj}
          {Y : C.Obj}
          {Z : C.Obj}
          {f : C.Hom W X}
          {g : C.Hom X Y}
          {h : C.Hom Y Z}
          {i : C.Hom Z W}:
     (i ∘_(C) (h ∘_(C) (g ∘_(C) (f ∘_(C) (𝟙_(C) W))) ))
  = ((i ∘_(C)  h) ∘_(C) ((𝟙_(C) Y) ∘_(C) g)) ∘_(C) (f) := by cat

ℵᶜᵃᵗ
ᵃ	ᵇ	ᶜ	ᵈ	ᵉ	ᶠ	ᵍ	ʰ	ⁱ	ʲ	ᵏ	ˡ	ᵐ	ⁿ	ᵒ	ᵖ	𐞥	ʳ	ˢ	ᵗ	ᵘ	ᵛ	ʷ	ˣ	ʸ	ᶻ

-- obtaining a morphism from an equality
def Map (C : category) {X : C.Obj} {Y : C.Obj} (p : X = Y) : C.Hom X Y := by
subst p
exact 𝟙_(C) X


notation "Map_(" C ")" p => Map C p


-- definition of an isomorphism from X to Y
structure isomorphism (C : category) (X : C.Obj) (Y : C.Obj) where
  Fst : C.Hom X Y
  Snd : C.Hom Y X
  Id₁ : (C.Cmp X Y X Fst Snd) = C.Idn X
  Id₂ : (C.Cmp Y X Y Snd Fst) = C.Idn Y


-- notation for isomorphisms from X to Y (≅)
notation X "≅_(" C ")" Y => isomorphism C X Y


-- defining the inverse of an isomorphism between objects X and Y
def inverse {C : category} {X : C.Obj} {Y : C.Obj} (f : X ≅_(C) Y) : Y ≅_(C) X := {Fst := f.Snd, Snd := f.Fst, Id₁ := f.Id₂, Id₂ := f.Id₁}


-- notation for inverse : isos from X to Y to isos from Y to X
notation f "⁻¹" => inverse f


def SetObj := Type

def SetHom (X : SetObj) (Y : SetObj) : Type := X → Y

def SetIdn (X : SetObj) : (SetHom X X) := λ (x : X) => x


def SetCmp (X : SetObj) (Y : SetObj) (Z : SetObj) (f : SetHom X Y) (g : SetHom Y Z) : SetHom X Z := λ (x : X) => (g (f x))


def SetId₁ (X : SetObj) (Y : SetObj) (f : SetHom X Y) : (SetCmp X Y Y f (SetIdn Y)) = f := funext (λ _ => rfl)

def SetId₂ (X : SetObj) (Y : SetObj) (f : SetHom X Y) : (SetCmp X X Y (SetIdn X) f) = f := rfl

def SetAss (W : SetObj) (X : SetObj) (Y : SetObj) (Z : SetObj) (f : SetHom W X) (g : SetHom X Y) (h : SetHom Y Z) : (SetCmp W X Z f (SetCmp X Y Z g h)) = (SetCmp W Y Z (SetCmp W X Y f g) h) := funext (λ _ => rfl)


def Set : category := {Obj := SetObj, Hom := SetHom, Idn := SetIdn, Cmp := SetCmp, Id₁ := SetId₁, Id₂ := SetId₂, Ass := SetAss}


-- definition of a functor
structure functor (C : category) (D : category) where
   Obj : ∀(_ : C.Obj),D.Obj
   Hom : ∀(X : C.Obj),∀(Y : C.Obj),∀(_ : C.Hom X Y),D.Hom (Obj X) (Obj Y)
   Idn : ∀(X : C.Obj),Hom X X (C.Idn X) = D.Idn (Obj X)
   Cmp : ∀(X : C.Obj),∀(Y : C.Obj),∀(Z : C.Obj),∀(f : C.Hom X Y),∀(g : C.Hom Y Z),
   D.Cmp (Obj X) (Obj Y) (Obj Z) (Hom X Y f) (Hom Y Z g) = Hom X Z (C.Cmp X Y Z f g)


--https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Dependent.20type.20hell.20golfing.20challenge






-- definition of the identity functor on objects
def CatIdnObj (C : category) :=
fun(X : C.Obj)=>
X

-- definition of the identity functor on morphisms
def CatIdnMor (C : category) :=
fun(X : C.Obj)=>
fun(Y : C.Obj)=>
fun(f : C.Hom X Y)=>
f

-- proving the identity law for the identity functor
def CatIdnIdn (C : category) :=
fun(X : C.Obj)=>
Eq.refl (C.Idn X)

-- proving the compositionality law for the identity functor
def CatIdnCmp (C : category) :=
fun(X : C.Obj)=>
fun(Y : C.Obj)=>
fun(Z : C.Obj)=>
fun(f : C.Hom X Y)=>
fun(g : C.Hom Y Z)=>
Eq.refl (C.Cmp X Y Z f g)


-- defining the identity functor
def CatIdn (C : category) : functor C C :=
{Obj := CatIdnObj C, Hom := CatIdnMor C, Idn := CatIdnIdn C, Cmp := CatIdnCmp C}


-- defining the composition G ∘_(Cat) F on objects
def CatCmpObj (C : category) (D : category) (E : category) (F : functor C D) (G : functor D E) :=
fun(X : C.Obj)=>
(G.Obj (F.Obj X))

-- defining the composition G ∘_(Cat) F on morphisms
def CatCmpHom (C : category) (D : category) (E : category) (F : functor C D) (G : functor D E) :=
fun(X : C.Obj)=>
fun(Y : C.Obj)=>
fun(f : C.Hom X Y)=>
(G.Hom) (F.Obj X) (F.Obj Y) (F.Hom X Y f)


-- proving the identity law for the composition G ∘_(Cat) F
def CatCmpIdn (C : category) (D : category) (E : category) (F : functor C D) (G : functor D E) :=
fun(X : C.Obj)=>
Eq.trans (congrArg (G.Hom (F.Obj X) (F.Obj X)) (F.Idn X) ) (G.Idn (F.Obj X))


-- proving the compositionality law for the composition G ∘_(Cat) F
def CatCmpCmp (C : category) (D : category) (E : category) (F : functor C D) (G : functor D E) :=
fun(X : C.Obj)=>
fun(Y : C.Obj)=>
fun(Z : C.Obj)=>
fun(f : C.Hom X Y)=>
fun(g : C.Hom Y Z)=>
((Eq.trans)
(G.Cmp (F.Obj X) (F.Obj Y) (F.Obj Z) (F.Hom X Y f) (F.Hom Y Z g))
(congrArg (G.Hom  (F.Obj X) (F.Obj Z)) (F.Cmp X Y Z f g)))


-- defining the composition in the category Cat
def CatCmp (C : category) (D : category) (E : category) (F : functor C D) (G : functor D E) : functor C E :=
{Obj := CatCmpObj C D E F G, Hom := CatCmpHom C D E F G,Idn := CatCmpIdn C D E F G, Cmp := CatCmpCmp C D E F G}


-- proving Cat.Id₁
def CatId₁ (C : category) (D : category) (F : functor C D) : ((CatCmp C D D) F (CatIdn D) = F) := Eq.refl F

-- Proof of Cat.Id₂
def CatId₂ (C : category) (D : category) (F : functor C D) : ((CatCmp C C D) (CatIdn C) F = F) := Eq.refl F

-- Proof of Cat.Ass
def CatAss (B : category) (C : category) (D : category) (E : category) (F : functor B C) (G : functor C D) (H : functor D E) : (CatCmp B C E F (CatCmp C D E G H) = CatCmp B D E (CatCmp B C D F G) H) :=
Eq.refl (CatCmp B C E F (CatCmp C D E G H))


-- The category of categories
universe u
universe v
def Cat : category := {Obj := category.{u, v}, Hom := functor, Idn := CatIdn, Cmp := CatCmp, Id₁:= CatId₁, Id₂:= CatId₂, Ass := CatAss}


notation "𝟙" X => 𝟙_(Cat) X

notation g "∘" f => g ∘_(Cat) f


-- defining the objects of the CatPrd C D
def CatPrdObj (C : category) (D : category) := (D.Obj) × (C.Obj)

-- defining the morphisms of CatPrd C D
def CatPrdHom (C : category) (D : category) (X : CatPrdObj C D) (Y : CatPrdObj C D) := (D.Hom X.1 Y.1) × (C.Hom X.2 Y.2)

-- defining the identity functor on an object in C × D
def CatPrdIdn (C : category) (D : category) (X : CatPrdObj C D) := ((D.Idn X.1),(C.Idn X.2))

-- defining the composition on morphisms in C × D
def CatPrdCmp (C : category) (D : category) (X : CatPrdObj C D) (Y : CatPrdObj C D) (Z : CatPrdObj C D) (f : CatPrdHom C D X Y) (g : CatPrdHom C D Y Z) : CatPrdHom C D X Z := (D.Cmp X.1 Y.1 Z.1 f.1 g.1, C.Cmp X.2 Y.2 Z.2 f.2 g.2)


-- proving the first identity law for morphisms in C ×_Cat D
theorem CatPrdId₁ (C : category) (D : category) (X : CatPrdObj C D) (Y : CatPrdObj C D) (f : CatPrdHom C D X Y) :
  CatPrdCmp C D X Y Y f (CatPrdIdn C D Y) = f := sorry

-- proving the second identity law for morphisms in C ×_Cat D
theorem CatPrdId₂ (C : category) (D : category) (X : CatPrdObj C D) (Y : CatPrdObj C D) (f : CatPrdHom C D X Y) : CatPrdCmp C D X X Y (CatPrdIdn C D X) f = f := sorry

-- proving associativity for morphisms in C ×_Cat D
theorem CatPrdAss
  (C : category) (D : category)
  (W : CatPrdObj C D) (X : CatPrdObj C D)
  (Y : CatPrdObj C D) (Z : CatPrdObj C D)
  (f : CatPrdHom C D W X) (g : CatPrdHom C D X Y) (h : CatPrdHom C D Y Z) :
  CatPrdCmp C D W X Z f (CatPrdCmp C D X Y Z g h) = CatPrdCmp C D W Y Z (CatPrdCmp C D W X Y f g) h := sorry


-- defining the CatPrd of two categories
def CatPrd (C : category) (D : category) : category := {Obj := CatPrdObj C D, Hom := CatPrdHom C D, Idn := CatPrdIdn C D, Cmp := CatPrdCmp C D, Id₁ := CatPrdId₁ C D, Id₂:= CatPrdId₂ C D, Ass := CatPrdAss C D}


notation:1000  D "×_Cat" C => CatPrd C D


def FunPrdObj
  {C₁ : category}
  {D₁ : category}
  {C₂ : category}
  {D₂ : category}
  (F : Cat.Hom C₁ D₁)
  (G : Cat.Hom C₂ D₂) :
  (C₁ ×_Cat C₂).Obj → (D₁ ×_Cat D₂).Obj :=
  sorry


def FunPrdHom
  {C₁ : category}
  {D₁ : category}
  {C₂ : category}
  {D₂ : category}
  (F : Cat.Hom C₁ D₁)
  (G : Cat.Hom C₂ D₂)
  (X : (C₁ ×_Cat C₂).Obj)
  (Y : (C₁ ×_Cat C₂).Obj)
  (f : (C₁ ×_Cat C₂).Hom X Y) :
  ((D₁ ×_Cat D₂).Hom (FunPrdObj F G X) (FunPrdObj F G Y) ) :=
  sorry


def FunPrdIdn
  {C₁ : category}
  {D₁ : category}
  {C₂ : category}
  {D₂ : category}
  (F : Cat.Hom C₁ D₁)
  (G : Cat.Hom C₂ D₂)
  (X : (C₁ ×_Cat C₂).Obj) :
  (FunPrdHom F G X X ((C₁ ×_Cat C₂).Idn X))  = ((D₁ ×_Cat D₂).Idn (FunPrdObj F G X)) :=
  sorry


def FunPrdCmp
  {C₁ : category}
  {D₁ : category}
  {C₂ : category}
  {D₂ : category}
  (F : Cat.Hom C₁ D₁)
  (G : Cat.Hom C₂ D₂)
  (X : (C₁ ×_Cat C₂).Obj)
  (Y : (C₁ ×_Cat C₂).Obj)
  (Z : (C₁ ×_Cat C₂).Obj)
  (f : (C₁ ×_Cat C₂).Hom X Y)
  (g : (C₁ ×_Cat C₂).Hom Y Z) :
  ((D₁ ×_Cat D₂).Cmp (FunPrdObj F G X) (FunPrdObj F G Y) (FunPrdObj F G Z) ((FunPrdHom F G) X Y f) (FunPrdHom F G Y Z g)) = (FunPrdHom F G X Z ((C₁ ×_Cat C₂).Cmp X Y Z f g)) :=
  sorry


def FunPrd
  {C₁ : category}
  {D₁ : category}
  {C₂ : category}
  {D₂ : category}
  (F : Cat.Hom C₁ D₁)
  (G : Cat.Hom C₂ D₂) :
  Cat.Hom (C₁ ×_Cat C₂) (D₁ ×_Cat D₂) :=
  {Obj := FunPrdObj F G, Hom := FunPrdHom F G, Idn := FunPrdIdn F G, Cmp := FunPrdCmp F G}


notation F "×_Fun" G => FunPrd F G


-- defining the category *_Cat
def PntObj : Type := Unit
def PntHom (_ : PntObj) (_ : PntObj) : Type := Unit
def PntIdn (X : PntObj) : PntHom X X := Unit.unit
def PntCmp (X : PntObj) (Y : PntObj) (Z : PntObj) (_ : PntHom X Y) (_ : PntHom Y Z) : PntHom X Z := Unit.unit
def PntId₁ (X : PntObj) (Y : PntObj) (f : PntHom X Y) : PntCmp X Y Y f (PntIdn Y) = f := Eq.refl f
def PntId₂ (X : PntObj) (Y : PntObj) (f : PntHom X Y) : PntCmp X X Y (PntIdn X) f = f := Eq.refl f
def PntAss (W : PntObj) (X : PntObj) (Y : PntObj) (Z : PntObj) (f : PntHom W X) (g : PntHom X Y) (h : PntHom Y Z) : PntCmp W Y Z (PntCmp W X Y f g) h = PntCmp W X Z f (PntCmp X Y Z g h) := Eq.refl Unit.unit
def Pnt : category := {Obj := PntObj, Hom := PntHom, Idn := PntIdn, Cmp := PntCmp, Id₁ := PntId₁, Id₂ := PntId₂, Ass := PntAss}


-- notation for the category *_Cat
notation "*_Cat" => Pnt


def PrdId₁Fst (C : category) : Cat.Hom C (C ×_Cat *_Cat) := sorry

def PrdId₁Snd (C : category) : Cat.Hom (C ×_Cat *_Cat) C := sorry


def PrdId₁Id₁ (C : category) : ((PrdId₁Snd C) ∘_(Cat) (PrdId₁Fst C)) = 𝟙_(Cat) C := sorry

def PrdId₁Id₂ (C : category) : ((PrdId₁Fst C) ∘_(Cat) (PrdId₁Snd C)) = 𝟙_(Cat) (C ×_Cat *_Cat) := sorry


def PrdId₁ (C : category) :  C ≅_(Cat) (C ×_Cat *_Cat)  := {Fst := PrdId₁Fst C, Snd:= PrdId₁Snd C, Id₁ := PrdId₁Id₁ C, Id₂ := PrdId₁Id₂ C}


def PrdId₂Fst (C : category) : Cat.Hom C (*_Cat ×_Cat C) := sorry

def PrdId₂Snd (C : category) : Cat.Hom (*_Cat ×_Cat C) C := sorry


def PrdId₂Id₁ (C : category) : ((PrdId₂Snd C) ∘_(Cat) (PrdId₂Fst C)) = 𝟙_(Cat) C := sorry

def PrdId₂Id₂ (C : category) : ((PrdId₂Fst C) ∘_(Cat) (PrdId₂Snd C)) = 𝟙_(Cat) (*_Cat ×_Cat C) := sorry


def PrdId₂ (C : category) :  C ≅_(Cat) (*_Cat ×_Cat C)  := {Fst := PrdId₂Fst C, Snd:= PrdId₂Snd C, Id₁ := PrdId₂Id₁ C, Id₂ := PrdId₂Id₂ C}


def PrdAssFst
  (C : category)
  (D : category)
  (E : category) :
  Cat.Hom (C ×_Cat D ×_Cat E) ((C ×_Cat D) ×_Cat E) := sorry

def PrdAssSnd
  (C : category)
  (D : category)
  (E : category) :
  Cat.Hom ((C ×_Cat D) ×_Cat E) (C ×_Cat D ×_Cat E) := sorry


def PrdAssId₁
  (C : category)
  (D : category)
  (E : category) : ((PrdAssSnd C D E) ∘_(Cat) (PrdAssFst C D E)) = 𝟙_(Cat) (C ×_Cat D ×_Cat E) := sorry

def PrdAssId₂
  (C : category)
  (D : category)
  (E : category) :  ((PrdAssFst C D E) ∘_(Cat) (PrdAssSnd C D E)) = 𝟙_(Cat) ((C ×_Cat D) ×_Cat E)  := sorry


def PrdAss
  (C : category)
  (D : category)
  (E : category) : (C ×_Cat D ×_Cat E)≅_(Cat) ((C ×_Cat D) ×_Cat E)    := {Fst := PrdAssFst C D E, Snd:= PrdAssSnd C D E, Id₁ := PrdAssId₁ C D E, Id₂ := PrdAssId₂ C D E}


-- definition of a (strict) twocategory
structure twocategory.{w} where
  Obj : Type w
  Hom : Obj →
        Obj →
        category
  Idn : (C : Obj) →
        Cat.Hom *_Cat (Hom C C)
  Cmp : (C : Obj) →
        (D : Obj) →
        (E : Obj) →
        Cat.Hom ((Hom C D) ×_Cat (Hom D E)) (Hom C E)
  Id₁ : (C : Obj) →
        (D : Obj) →
        ((Cmp C D D) ∘_(Cat) ((𝟙_(Cat) (Hom C D)) ×_Fun (Idn D)) ∘_(Cat) (PrdId₁ (Hom C D)).Fst) = (𝟙_(Cat) (Hom C D))
  Id₂ : (C : Obj) →
        (D : Obj) →
        ((Cmp C C D) ∘_(Cat) ((Idn C) ×_Fun (𝟙_(Cat) (Hom C D))) ∘_(Cat) (PrdId₂Fst (Hom C D))) = (𝟙_(Cat) (Hom C D))
  Ass : (B : Obj) →
        (C : Obj) →
        (D : Obj) →
        (E : Obj) →
        ((Cmp B C E) ∘_(Cat) ((𝟙_(Cat) (Hom B C)) ×_Fun (Cmp C D E))) = (Cmp B D E) ∘_(Cat) ((Cmp B C D) ×_Fun (𝟙_(Cat) (Hom D E))) ∘_(Cat) (PrdAss (Hom B C) (Hom C D) (Hom D E)).Fst


-- definition of a twofunctor
structure twofunctor (C : twocategory) (D : twocategory) where
  Obj : C.Obj → D.Obj
  Hom : (X : C.Obj) → (Y : C.Obj) → (functor (C.Hom X Y) (D.Hom (Obj X) (Obj Y)))
-- Idn : (X : C.Obj) → ()
-- Cmp : (X : C.Obj) → (Y : C.Obj) → (Z : C.Obj) →


-- defining the identity component of the category TwoCat
def TwoCatIdn (C : twocategory) : (twofunctor C C) := sorry


-- defining the composition component of the category TwoCat
def TwoCatCmp (C : twocategory) (D : twocategory) (E : twocategory) (F : twofunctor C D) (G : twofunctor D E) : twofunctor C E := sorry


-- defining the first identity component of the category TwoCat
/-

-/


-- defining the second identity component of the category TwoCat
/-

-/


-- defining the associativity component of the category TwoCat
/-

-/


-- Assembling the category TwoCat
def TwoCat : category := sorry


-- Notation for the identity map which infers the category:
def twocategory_identity_map (C : twocategory) (X : C.Obj) : (C.Hom X X).Obj := ((C.Idn X).Obj Unit.unit)
notation "𝟏_(" C ")" => twocategory_identity_map C



-- Notation for composition in a twocategory which infers the category and objects:

def composition_on_objects (C : twocategory) {X : C.Obj} {Y : C.Obj} {Z : C.Obj} (f : (C.Hom X Y).Obj) (g : (C.Hom Y Z).Obj) : (C.Hom X Z).Obj := (C.Cmp X Y Z).Obj (f, g)
notation: 1000 g "•_(" C ")" f => composition_on_objects C f g

def TwoCmpObj {C : twocategory} {X : C.Obj} {Y : C.Obj} {Z : C.Obj} (f : (C.Hom X Y).Obj) (g : (C.Hom Y Z).Obj) : (C.Hom X Z).Obj :=  (C.Cmp X Y Z).Obj (f, g)
notation: 1000 g "•" f => TwoCmpObj f g


def composition_on_morphisms (C : twocategory) {X : C.Obj} {Y : C.Obj} {Z : C.Obj} {F₁ : (C.Hom X Y).Obj} {F₂ : (C.Hom X Y).Obj} {G₁ : (C.Hom Y Z).Obj} {G₂ : (C.Hom Y Z).Obj} (η : (C.Hom X Y).Hom F₁ F₂) (ε : (C.Hom Y Z).Hom G₁ G₂) : (C.Hom X Z).Hom (G₁ • F₁) (G₂ • F₂) := (C.Cmp X Y Z).Hom (F₁,G₁) (F₂,G₂) (η,ε)
notation: 1000 g "∙_(" C ")" f => composition_on_morphisms C f g

def TwoCmpHom {C : twocategory} {X : C.Obj} {Y : C.Obj} {Z : C.Obj} {F₁ : (C.Hom X Y).Obj} {F₂ : (C.Hom X Y).Obj} {G₁ : (C.Hom Y Z).Obj} {G₂ : (C.Hom Y Z).Obj} (η : (C.Hom X Y).Hom F₁ F₂) (ε : (C.Hom Y Z).Hom G₁ G₂) : (C.Hom X Z).Hom (G₁ • F₁) (G₂ • F₂) := (C.Cmp X Y Z).Hom (F₁,G₁) (F₂,G₂) (η,ε)
notation : 1000 g "∙" f => TwoCmpHom f g


/-
theorem Id₁Obj {C : category} {X : C.Obj} {Y : C.Obj} {f : C.Hom X Y} :
  (f ∘_(C) (𝟙_(C) X)) = f := C.Id₂ X Y f

theorem Id₁Hom {C : category} {X : C.Obj} {Y : C.Obj} {f : C.Hom X Y} :
  (f ∘_(C) (𝟙_(C) X)) = f := C.Id₂ X Y f

theorem Id₂Obj {C : category} {X Y : C.Obj} {f : C.Hom X Y} :
  (𝟙_(C) Y ∘_(C) f) = f := C.Id₁ X Y f

theorem Id₂Hom {C : category} {X Y : C.Obj} {f : C.Hom X Y} :
  (𝟙_(C) Y ∘_(C) f) = f := C.Id₁ X Y f

theorem AssObj {C : category} {W X Y Z : C.Obj} {f : C.Hom W X} {g : C.Hom X Y} {h : C.Hom Y Z} :
  ((h ∘_(C) g) ∘_(C) f) = (h ∘_(C) (g ∘_(C) f)) := (C.Ass W X Y Z f g h)

theorem AssHom {C : category} {W X Y Z : C.Obj} {f : C.Hom W X} {g : C.Hom X Y} {h : C.Hom Y Z} :
  ((h ∘_(C) g) ∘_(C) f) = (h ∘_(C) (g ∘_(C) f)) := (C.Ass W X Y Z f g h)
-/


/-
theorem CmpHom
-/


/-
macro "twocat" : tactic => `(tactic| repeat (rw [Id₁Obj]) ; repeat (rw [Id₁Hom]) ; repeat (rw [Id₂Obj]) ; repeat (rw [Id₂Hom]); repeat (rw [AssObj])) ; repeat (rw [AssHom]))

-- example of the cat tactic
example {C : category}
          {W : C.Obj}
          {X : C.Obj}
          {Y : C.Obj}
          {Z : C.Obj}
          {A : C.Obj}
          {f : C.Hom W X}
          {g : C.Hom X Y}
          {h : C.Hom Y Z}
          {i : C.Hom Z A}:
     (i ∘_(C) (h ∘_(C) (g ∘_(C) (f ∘_(C) (𝟙_(C) W))) ))
  = ((i ∘_(C)  h) ∘_(C) ((𝟙_(C) Y) ∘_(C) g)) ∘_(C) (f) := by cat
-/


-- obtaining a morphism from an equality
def TwoMap (C : twocategory) {X : C.Obj} {Y : C.Obj} (p : X = Y) : (C.Hom X Y).Obj := by
subst p
exact 𝟏_(C) X


notation "TwoMap_(" C ")" p => TwoMap C p


-- definition of an equivalence from X to Y
structure equivalence (T : twocategory) (X : T.Obj) (Y : T.Obj) where
  Fst : (T.Hom X Y).Obj
  Snd : (T.Hom Y X).Obj
  Id₁ : (T.Cmp X Y X).Obj (Fst,Snd) ≅_(T.Hom X X) (𝟏_(T) X)
  Id₂ : (T.Cmp Y X Y).Obj (Snd,Fst) ≅_(T.Hom Y Y) (𝟏_(T) Y)


-- notation for equivalences from C to D (≃)
notation C "≃_(" T ")" D => equivalence T C D


-- defining the inverse of an isomorphism between objects X and Y
/-
def twocategory_inverse {C : category} {X : C.Obj} {Y : C.Obj} (f : X ≅_(C) Y) : Y ≅_(C) X := {Fst := f.Snd, Snd := f.Fst, Id₁ := f.Id₂, Id₂ := f.Id₁}
-/


-- notation for inverse of an equivalence : isos from X to Y to isos from Y to X
-- notation f "⁻¹" => inverse f


-- defining natural transformations for a category C and a category D
structure HomHom (C : category.{u,v}) (D : category.{u,v}) (F : functor C D) (G : functor C D) where
  Obj : (X : C.Obj) → (D.Hom (F.Obj X) (G.Obj X))
  Nat : (X : C.Obj) → (Y : C.Obj) → (f : C.Hom X Y) → (D.Cmp (F.Obj X) (F.Obj Y) (G.Obj Y) (F.Hom X Y f) (Obj Y)) = (D.Cmp (F.Obj X) (G.Obj X) (G.Obj Y) (Obj X) (G.Hom X Y f))


-- notation for natural transformations
def natural_transformation {C : category.{u,v}} {D : category.{u,v}} (F : functor C D) (G : functor C D) := HomHom C D F G


-- defining (C →_Cat D).Idn.Obj, the identity natural transformation of a functor on objects
def HomIdnObj (C : category.{u,v}) (D : category.{u,v}) (F : functor C D) (X : C.Obj) : (D.Hom (F.Obj X) (F.Obj X)) := D.Idn (F.Obj X)


-- helping to prove the naturality of the identity functor
def HomIdnNat₁ (C : category.{u,v}) (D : category.{u,v}) (F : functor C D) (X : C.Obj) (Y : C.Obj) (f : C.Hom X Y) : (D.Cmp (F.Obj X) (F.Obj Y) (F.Obj Y) (F.Hom X Y f) (HomIdnObj C D F Y)) = F.Hom X Y f := D.Id₁ (functor.Obj F X) (functor.Obj F Y) (functor.Hom F X Y f)

-- starting to prove the naturality of the identity functor
def HomIdnNat₂ (C : category.{u,v}) (D : category.{u,v}) (F : functor C D) (X : C.Obj) (Y : C.Obj) (f : C.Hom X Y) : (D.Cmp (F.Obj X) (F.Obj X) (F.Obj Y) (HomIdnObj C D F X) (F.Hom X Y f)) = F.Hom X Y f := D.Id₂ (functor.Obj F X) (functor.Obj F Y) (functor.Hom F X Y f)

-- proving the naturality of the identity functor, (C →_Cat D).Idn.Nat
def HomIdnNat (C : category.{u,v}) (D : category.{u,v}) (F : functor C D) (X : C.Obj) (Y : C.Obj) (f : C.Hom X Y) : (D.Cmp (F.Obj X) (F.Obj Y) (F.Obj Y) (F.Hom X Y f) (HomIdnObj C D F Y)) = (D.Cmp (F.Obj X) (F.Obj X) (F.Obj Y) (HomIdnObj C D F X) (F.Hom X Y f)) := Eq.trans (HomIdnNat₁ C D F X Y f) (Eq.symm (HomIdnNat₂ C D F X Y f))


-- defining (C →_Cat D).Idn for a category C and a category D
def HomIdn (C : category.{u,v}) (D : category.{u,v}) (F : Cat.Hom C D) : HomHom C D F F := {Obj := HomIdnObj C D F, Nat := HomIdnNat C D F}


-- defining composition of natural transformations
def HomCmpObj (C : category.{u,v}) (D : category.{u,v}) (F : functor C D) (G : functor C D) (H : functor C D) (f : HomHom C D F G) (g : HomHom C D G H) (X : C.Obj) :  D.Hom (F.Obj X) (H.Obj X) := (g.Obj X) ∘_(D) (f.Obj X)

-- defining composition of natural transformations
def HomCmpNat (C : category.{u,v}) (D : category.{u,v}) (F : functor C D) (G : functor C D) (H : functor C D) (f : HomHom C D F G) (g : HomHom C D G H) (X : C.Obj) (Y : C.Obj) (α : C.Hom X Y) : (((g.Obj Y) ∘_(D) (f.Obj Y)) ∘_(D) (F.Hom X Y α))  = ((H.Hom X Y α) ∘_(D) ((g.Obj X) ∘_(D) (f.Obj X)))  := sorry

-- defining composition of natural transformations
def HomCmp (C : category.{u,v}) (D : category.{u,v}) (F : functor C D) (G : functor C D) (H : functor C D) (f : HomHom C D F G) (g : HomHom C D G H) : HomHom C D F H := {Obj := HomCmpObj C D F G H f g, Nat := HomCmpNat C D F G H f g}


-- proving the identity laws and associativity for the category C →_Cat D

-- proving the first identity law of the functor category C →_Cat D
def HomId₁ (C : category.{u,v}) (D : category.{u,v}) (F : functor C D) (G : functor C D) (f : HomHom C D F G) : HomCmp C D F G G f (HomIdn C D G) = f := sorry

-- proving the second identity law of the functor category C →_Cat D
def HomId₂ (C : category.{u,v}) (D : category.{u,v}) (F : functor C D) (G : functor C D) (f : HomHom C D F G) : HomCmp C D F F G (HomIdn C D F) f = f := sorry

-- proving associativity of the functor category C →_Cat D
def HomAss (C : category.{u,v}) (D : category.{u,v}) (F : functor C D) (G : functor C D) (H : functor C D) (I : functor C D) (α : HomHom C D F G) (β : HomHom C D G H) (γ : HomHom C D H I) : (HomCmp C D F G I α (HomCmp C D G H I β γ)) = (HomCmp C D F H I (HomCmp C D F G H α β) γ) := sorry


-- defining the category C →_Cat D for a category C and a category D
def ℂ𝕒𝕥Hom (C : category) (D : category) : category := sorry -- {Obj := functor C D, Hom := HomHom C D, Idn := HomIdn C D, Cmp := HomCmp C D, Id₁ := HomId₁ C D, Id₂ := HomId₂ C D, Ass := HomAss C D}


-- defining categories.Idn.Obj
-- def CatIdnObj (C : category) (_ : Unit) := Cat.Idn C


-- defining the functor categories.Idn.Hom on morphisms
-- def categoriesIdnHom (C : category) (_ : Unit) (_ : Unit) (_: Unit) := (Hom C C).Idn (Cat.Idn C)


-- proving the identity law for the functor categories.TwoIdn
-- def TwoIdnIdn (C : category) (_ : Unit) (_ : Unit) (_: Unit) := (Hom C C).Idn (Cat.Idn C)


-- proving compositionality for the functor categories.TwoIdn
-- def Two.Idn.Cmp (C : category) (_ : Unit) (_ : Unit) (_: Unit) := (Hom C C).Idn (Cat.Idn C)


-- def ℂ𝕒𝕥.Idn
def ℂ𝕒𝕥Idn (C : category) : Cat.Hom *_Cat (ℂ𝕒𝕥Hom C C) := sorry


--  defining ℂ𝕒𝕥.Cmp.Obj
/-
-/


--  defining ℂ𝕒𝕥.Cmp.Hom
/-
def categoriesTwoHom (C : Obj) (D : Obj) (E : Obj) : FG.1 FG.2
def categoriesTwoHom (C : Obj) (D : Obj) (E : Obj) (f : ((Hom C D) × (Hom D E)).Hom )
def CatsHom (C : Obj) (D : Obj) (E : Obj)
(F₁G₁ : ((Hom C D) × (Hom D E)).Obj) (F₂G₂ : ((Hom C D) × (Hom D E)).Obj)
-/



-- defining the horizontal composition of natural transformations
-- def horizontal_composition {C : category} {D : category} {E : category} {F₁ : C → D} {F₂ : C → D} {G₁ : D → E} {G₂ : D → E} (η₁ : F₁ ⇨ F₂) (η₂ : G₁ ⇨ G₂) : ((Cat.Cmp C D E F₁ G₁) ⇨ (Cat.Cmp C D E F₂ G₂)) := sorry


-- notation for the horizontal composition of natural transformations
-- notation η₂ "∙" η₁ => horizontal_composition η₁ η₂


-- proving the identity law equation for ℂ𝕒𝕥.Cmp
/-
-- def CmpIdn :
-/


-- proving compositionality for the functor ℂ𝕒𝕥.Cmp
-- def CmpCmp : (C : category) → (D : category) → (E : category) → (CatPrd (Hom C D) (Hom D E)) → (Hom C E) := sorry


--  categories.Cmp : (C : Obj) → (D : Obj) → (E : Obj) → (Hom C D) × (Hom D E) → (Hom C E)
def ℂ𝕒𝕥Cmp : (C : category.{u,v}) → (D : category.{u,v}) → (E : category.{u,v}) → functor ((ℂ𝕒𝕥Hom C D) ×_Cat (ℂ𝕒𝕥Hom D E)) (ℂ𝕒𝕥Hom C E) := sorry


--  Id₁ : (C : Obj) → (D : Obj) → (Cats.Id₁)
/-
def Id₁ : (C : category) → (D : category) → (F : functor C D) →
-/

def ℂ𝕒𝕥Id₁ :  ∀ (C D : category.{u,v}),
  ((ℂ𝕒𝕥Cmp C D D)∘_(Cat)(𝟙_(Cat) (ℂ𝕒𝕥Hom C D) ×_Fun ℂ𝕒𝕥Idn D)∘_(Cat)(PrdId₁ (ℂ𝕒𝕥Hom C D)).Fst) =
  𝟙_(Cat) (ℂ𝕒𝕥Hom C D) := sorry




--
def ℂ𝕒𝕥Id₂ : (C : category.{u,v}) →
        (D : category.{u,v}) →
        ((ℂ𝕒𝕥Cmp C C D) ∘_(Cat) ((ℂ𝕒𝕥Idn C) ×_Fun (𝟙_(Cat) (ℂ𝕒𝕥Hom C D))) ∘_(Cat) (PrdId₂Fst (ℂ𝕒𝕥Hom C D))) = (𝟙_(Cat) (ℂ𝕒𝕥Hom C D))  := sorry


-- proving associativity of composition for the twocategory of categories
def ℂ𝕒𝕥Ass : (B : category.{u,v}) →
          (C : category.{u,v}) →
          (D : category.{u,v}) →
          (E : category.{u,v}) →
          ((ℂ𝕒𝕥Cmp B C E) ∘_(Cat) ((𝟙_(Cat) (ℂ𝕒𝕥Hom B C)) ×_Fun (ℂ𝕒𝕥Cmp C D E))) = (ℂ𝕒𝕥Cmp B D E) ∘_(Cat) ((ℂ𝕒𝕥Cmp B C D) ×_Fun (𝟙_(Cat) (ℂ𝕒𝕥Hom D E))) ∘_(Cat) (PrdAss (ℂ𝕒𝕥Hom B C) (ℂ𝕒𝕥Hom C D) (ℂ𝕒𝕥Hom D E)).Fst := sorry



-- twocategory_of_categories
def ℂ𝕒𝕥 : twocategory := {Obj:= category.{u,v}, Hom := ℂ𝕒𝕥Hom, Idn := ℂ𝕒𝕥Idn, Cmp := ℂ𝕒𝕥Cmp, Id₁ := ℂ𝕒𝕥Id₁, Id₂ := ℂ𝕒𝕥Id₂, Ass := ℂ𝕒𝕥Ass}


notation C "≃" D => equivalence ℂ𝕒𝕥 C D



def TwoIdn {C : twocategory} (X : C.Obj) : (C.Hom X X).Obj := ((C.Idn X).Obj Unit.unit)
notation "𝟏" X => 𝟏_(ℂ𝕒𝕥) X


-- definition of the right triangle identity
-- def AdjId₁ (C : category) (D : category) (F : (C →_Cat D).Obj) (G : (D →_Cat C).Obj) (unit : (C →_Cat C).Hom (𝟙_Cat C) (G ∘_Cat F)) ( counit : (D →_Cat D).Hom (F ∘_Cat G) (𝟙_Cat D) ) : Prop := sorry


-- definition of the left triangle identity
-- def AdjId₂ (C : category) (D : category) (F : (C →_Cat D).Obj) (G : (D →_Cat C).Obj) (unit : (C →_Cat C).Hom (𝟙_Cat C) (G ∘_Cat F)) ( counit : (D →_Cat D).Hom (F ∘_Cat G) (𝟙_Cat D) ) : Prop := sorry


-- definition of an adjunction

structure adjunction (C : twocategory) where
  Dom : C.Obj
  Cod : C.Obj
  left_adjoint : (C.Hom Dom Cod).Obj
  right_adjoint : (C.Hom Cod Dom).Obj
  unit : (C.Hom Dom Dom).Hom (𝟏_(C) Dom) (G •_(C) F)
  counit : (C.Hom Cod Cod).Hom (F •_(C) G) (𝟏_(C) Cod)
--  left_triangle_identity : AdjId₁ Dom Cod F G η ε
--  right_triangle_identity : AdjId₂ Dom Cod F G η ε



def left_adjoint {C : twocategory} (f : adjunction C) : (C.Hom f.Dom f.Cod).Obj := f.left_adjoint


notation f "𛲔" => left_adjoint f


def right_adjoint {C : twocategory} (f : adjunction C) : (C.Hom f.Cod f.Dom).Obj := f.right_adjoint


notation f "ॱ" => right_adjoint f


/-
def is_adjoint (C : category) (D : category) (F : (C →_Cat D).Obj) (G : (D →_Cat C).Obj) : Prop := ∃ (η : (C →_Cat C).Hom (𝟙_Cat C) (G ∘_Cat F)), ∃ (ε : (D →_Cat D).Hom (F ∘_Cat G) (𝟙_Cat D)), (AdjId₁ C D F G η ε) ∧ (AdjId₂ C D F G η ε)
notation F "⊣" G => adjoint F G
/-
∃ (G : (D →_Cat D).Obj), ∃ (η : (C →_Cat C).Hom (𝟙_Cat C) (G ∘_Cat F)), ∃ (ε : (D →_Cat D).Hom (F ∘_Cat G) (𝟙_Cat D)), (AdjId₁ C D F G η ε) ∧ (AdjId₂ C D F G η ε)
-/
-/


def is_left_adjoint {C : category} {D : category} (F : Cat.Hom C D) : Prop := sorry

notation F "⊣" "-" => is_left_adjoint F


def is_right_adjoint {C : category} {D : category} (G : Cat.Hom D C) : Prop := sorry

notation "-" "⊣" G => is_right_adjoint G





-- the first identity law for a monad
-- def monadId₁ (C : category) (T : (C →_Cat C).Obj) (η : (C →_Cat C).Hom (Cat.Idn C) (T)) (μ : (C →_Cat C).Hom (T ∘_Cat T) (T)) : Prop := sorry -- μ ∘ (η ∙ (𝟙 T)) = 𝟙 T


-- the second identity law for a monad
-- def monadId₂ (C : category) (T : (C →_Cat C).Obj) (η : (C →_Cat C).Hom (Cat.Idn C) (T)) (μ : (C →_Cat C).Hom (T ∘_Cat T) (T)) : Prop := sorry -- μ ∘ ((𝟙 T) • η) = 𝟙 T


-- the associativity law for a monad
-- def monadAss (C : category) (T : (C →_Cat C).Obj) (η : (C →_Cat C).Hom (Cat.Idn C) (T)) (μ : (C →_Cat C).Hom (T ∘_Cat T) (T)) : Prop := sorry -- μ ∘ (μ • (𝟙 T)) = μ ∘ ((𝟙 T) • μ)


-- definition of a monad
structure monad (C : twocategory) where
  Dom : C.Obj
  Fun : (C.Hom Dom Dom).Obj
  η : (C.Hom Dom Dom).Hom (𝟏_(C) Dom) Fun
  μ : (C.Hom Dom Dom).Hom (Fun •_(C) Fun) Fun
--  Id₁ : monadId₁ Dom Fun η μ
--  Id₂ : monadId₂ Dom Fun η μ
--  Ass : monadAss Dom Fun η μ


-- the first comonad identity law for a comonad
-- def comonadId₁ (C : category) (T : (C →_Cat C).Obj) (ε : (C →_Cat C).Hom (T) (Cat.Idn C)) (Δ : (C →_Cat C).Hom (T) (T ∘_Cat T)) : Prop := sorry


-- the second comonad identity law for a comonad
-- def comonadId₂ (C : category) (T : (C →_Cat C).Obj) (ε : (C →_Cat C).Hom (T) (Cat.Idn C)) (Δ : (C →_Cat C).Hom (T) (T ∘_Cat T)) : Prop := sorry


-- the associativity identity law for a comonad
-- def comonadAss (C : category) (T : (C →_Cat C).Obj) (ε : (C →_Cat C).Hom (T) (Cat.Idn C)) (Δ : (C →_Cat C).Hom (T) (T ∘_Cat T)) : Prop := sorry


-- definition of a comonad
structure comonad (C : twocategory) where
  Cod : C.Obj
  Fun : (C.Hom Cod Cod).Obj
  ε : (C.Hom Cod Cod).Hom Fun (𝟏_(C) Cod)
  Δ : (C.Hom Cod Cod).Hom Fun (Fun •_(C) Fun)
--  Id₁ : comonadId₁ Dom Fun ε Δ
--  Id₂ : comonadId₂ Dom Fun ε Δ
--  Ass : comonadAss Dom Fun ε Δ


def MonAdjDom (C : twocategory) (f : adjunction C) : C.Obj := f.Dom


-- def MonAdjFun (C : twocategory) (f : adjunction C) : (C.Hom (MonDom C f) (MonDom C f)).Obj := sorry


-- def MonAdjEta (f : adjunction) : ((MonDom f) →_Cat (MonDom f)).Hom (𝟙_Cat (MonDom f)) (MonFun f) := sorry


-- def MonAdjMu (f : adjunction) : ((MonDom f) →_Cat (MonDom f)).Hom ((MonFun f) ∘_Cat (MonFun f)) (MonFun f) := sorry


-- def MonAdjId₁ (f : adjunction) : monadId₁ (MonDom f) (MonFun f) (MonEta f) (MonMu f) := sorry


-- def MonAdjId₂ (f : adjunction) : monadId₂ (MonDom f) (MonFun f) (MonEta f) (MonMu f) := sorry



-- def MonAdjAss (f : adjunction) : monadAss (MonDom f) (MonFun f) (MonEta f) (MonMu f) := sorry


-- the monad corresponding to an adjunction
def MonAdj (C : twocategory) (f : adjunction C) : monad C := sorry --{Dom := MonDom f, Fun := MonFun f, μ}


notation : 1000 "?_(" C ")" => MonAdj C

-- notation "?" => MonAdj Cat


-- def ComAdjDom (f : adjunction) : category := sorry


-- def ComAdjFun (f : adjunction) : ( (ComDom f) →_Cat (ComDom f) ).Obj := sorry


-- def ComAdjEps (f : adjunction) : ( (ComDom f) →_Cat (ComDom f) ).Hom (ComFun f) (𝟙_Cat (ComDom f)) := sorry


-- def ComAdjDel (f : adjunction) : ( (ComDom f) →_Cat (ComDom f) ).Hom (ComFun f) ((ComFun f) ∘_Cat (ComFun f)) := sorry


-- def ComAdjId₁ (f : adjunction) : comonadId₁ (ComDom f) (ComFun f) (ComEps f) (ComDel f) := sorry


-- def ComAdjId₂ (f : adjunction) : comonadId₂ (ComDom f) (ComFun f) (ComEps f) (ComDel f) := sorry


-- def ComAdjAss (f : adjunction) : comonadAss (ComDom f) (ComFun f) (ComEps f) (ComDel f) := sorry


-- the monad corresponding to an adjunction
def ComAdj {C : twocategory} (f : adjunction C) : comonad C := sorry


-- ¿

notation "¿_(" C ")" => ComAdj C

notation "¿" => ComAdj ℂ𝕒𝕥


-- defining the object component of the codomain of the Eilenberg-Moore adjunction for Cat
/-

-/


-- defining the hom component of the codomain of the Eilenberg-Moore adjunction for Cat
/-

-/


-- defining the identity component of the codomain of the Eilenberg-Moore adjunction for Cat
/-

-/







-- constructing the right adjoint of the Eilenberg-Moore adjunction in Cat on objects
/-

-/


-- constructing the right adjoint of the Eilenberg-Moore adjunction in Cat on morphisms
/-

-/


-- proving the first identity law for the right adjoint of the Eilenberg-Moore adjunction in Cat
/-

-/


-- proving the compositionality law for the right adjoint of Eilenberg-Moore adjunction in Cat
/-

-/


-- assembling the right adjoint of the Eilenberg-Moore adjunction in Cat
/-

-/


-- constructing the left adjoint of the Eilenberg-Moore adjunction in Cat on objects
/-

-/


-- constructing the left adjoint of the Eilenberg-Moore adjunction in Cat on morphisms
/-

-/


-- proving the first identity law for the left adjoint of the Eilenberg-Moore adjunction in Cat
/-

-/


-- proving the compositionality law for the left adjoint of Eilenberg-Moore adjunction in Cat
/-

-/


-- assembling the left adjoint of the Eilenberg-Moore adjunction in Cat
/-

-/


-- constructing the unit of the Eilenberg-Moore adjunction in Cat on objects
/-

-/


-- proving naturality for the unit of the eilenberg moore adjunction unit in Cat
/-

-/



-- constructing the counit of the eilenberg moore adjunction in Cat on objects
/-

-/


-- proving naturality for the counit of the eilenberg moore adjunction in Cat
/-

-/


-- assembling the counit of the eilenberg moore adjunction in Cat
/-

-/


-- the coeilenberg comoore adjunction in Cat triangle identity 1
/-
def
-/


-- the coeilenberg comoore adjunction in Cat triangle identity 1
/-
def
-/


-- assembling the Eilenberg-Moore adjunction in Cat
/-

-/


-- notation for the Eilenberg-Moore categrory in Cat
/-

-/


























-- the co-Eilenberg-co-Moore adjunction in Cat triangle identity 1
/-
def
-/


-- the coeilenberg comoore adjunction in Cat triangle identity 1
/-
def
-/



/-
 ¡
 -/


-- constructing the canonical map out of the codomain of the eilenberg moore adjunction in Cat
/-

-/


-- notation for the canonical map from eilenberg moore category of the corresponding monad for an adjunction
-- notation "ꜝ" => exponential


-- proving the universal property of the eilenberg-moore adjunction in Cat
-- theorem universal_property_of_the_eilenberg_moore_adjunction (φ:adjunction) : ∃!(F : functor (!?φ).Cod φ.Cod),F •_(Cat) (!?φ)𛲔 = (φ𛲔) := sorry



-- notation for the canonical map from co-Eilenberg-co-Moore category of the corresponding monad for an adjunction
-- notation "ꜞ" => exponential


-- proving the universal property of the co-Eilenberg-co-Moore adjunction in Cat
/-
def
-/


-- defining monadicity
-- def monadic_adjunction (C : twocategory) (f : adjunction C) : Prop := sorry


-- !M is monadic
/-

-/


-- defining comonadic adjunction
-- def comonadic (C : twocategory) (f : adjunction C) : Prop := sorry


-- comonadicity of a monad
/-

-/


-- ¡M is comonadic
/-

-/


-- defining a bimonadic adjunction
--structure bimonadic_adjunction where
--  f : adjunction
--  Mon : functor (?f)ꜝ  -- need to replace the first Cod with (?f)ꜝ
--  Com :




-- constructing the hom component of Adj_(C)
def LadjHom (_ : category) (_ : category) : Type := sorry


-- constructing the identity component of Adj_(ℂ𝕒𝕥)
def LadjIdn (X : category) : (LadjHom X X) := sorry


-- constructing the composition component of Adj
def LadjCmp (X : category) (Y : category) (Z : category) (_ : LadjHom X Y) (_ : LadjHom Y Z) : (LadjHom X Z) := sorry


-- proving the first identity law in Adj
def LadjId₁ (X : category) (Y : category) (f : (LadjHom X Y)):
  (LadjCmp X Y Y f (LadjIdn Y)) = f := sorry


-- proving the second identity law in Ladj
def LadjId₂ (X: category) (Y : category) (f : (LadjHom X Y)):
  (LadjCmp X X Y (LadjIdn X) f) = f := sorry


-- proving the associativity law in Adj
def LadjAss
  (W : category)
  (X : category)
  (Y : category)
  (Z : category)
  (f : LadjHom W X)
  (g : LadjHom X Y)
  (h : LadjHom Y Z): (LadjCmp W X Z f (LadjCmp X Y Z g h)) = (LadjCmp W Y Z (LadjCmp W X Y f g) h) := sorry


-- assembling the twocategory of adjunctions
def Ladj : category := {Obj := Cat.Obj, Hom := LadjHom, Idn := LadjIdn, Cmp := LadjCmp, Id₁ := LadjId₁, Id₂:= LadjId₂, Ass := LadjAss}

/-
-- constructing the objects in Adj
def RadjObj (T : twocategory) := T.Obj
-/
/-
-- constructing the hom component of Adj_(C)
def left_adjunction (_ : T.Obj) (_ : T.Obj) : Type := sorry
-/
/-
-- constructing the identity component of Adj_(ℂ𝕒𝕥)
def LadjIdn: (X : category) → (LadjHom X X) := sorry
-/
/-
-- constructing the composition component of Adj
def LadjCmp : (X : category) (Y : category) (Z : category) (_ : LadjHom X Y) (_ : LadjHom Y Z) : (LadjHom T X Z) := sorry
-/
/-
-- proving the first identity law in Adj
def LadjId₁ :∀ (X Y : category T) (f : (AdjHom T X Y)),
  (AdjCmp T X Y Y f (AdjIdn T Y)) = f := sorry
-/
/-
-- proving the second identity law in Adj
def LadjId₂ :  ∀ (X Y : category) (f : (AdjHom X Y)),
  (AdjCmp X X Y (AdjIdn X) f) = f := sorry
-/
/-
-- proving the associativity law in Adj
def LadjAss :∀ (W X Y Z : category) (f : AdjHom W X) (g : AdjHom X Y)
  (h : AdjHom Y Z),
  AdjCmp W X Z f (AdjCmp X Y Z g h) =
  AdjCmp W Y Z f (AdjCmp W X Y f g) h := sorry
-/
/-
-- assembling the twocategory of adjunctions
def Ladj : category := {Obj := category, Hom := LadjHom, Idn := LadjIdn, Cmp := LadjCmp, Id₁ := LadjId₁, Id₂:= LadjId₂, Ass := LadjAss}
-/

structure geode where
  Obj : (Cat).Obj
  Pnt : Obj.Obj
  Cmp : Cat.Hom Obj Cat
--  Pul (C : Obj.Obj) (D : Obj.Obj) (F : Obj.Hom C D) : Cat.Hom () ()
--  ε
--  η
--  Id₁
--  Id₂
--
--
--  Bot : Obj.Obj Pnt (μ.Obj Pnt)
-- Ovr : (X : Obj.Obj) → (Y : Obj.Obj) →  ... For each object in F : (U/C).Obj, there is a unique map χ_(F) : C → ∞ such that the pullback along χ_(F), of type Hom (U/∞) (U/C) sends ⊥ to F.
-- Existence
-- Uniqueness


-- def Put (Γ : geode.{u+1,v+1}) :


def geodeObj (Γ: geode) : Cat.Obj := Γ.Obj


notation "∞_(" Γ ")" => geodeObj Γ


def geodePnt (Γ : geode) : Γ.Obj.Obj := Γ.Pnt


notation : 1000 "*_(" Γ ")" => geodePnt Γ


-- def pullback {Γ : geode} {C : Γ.Obj} {D : Γ.Obj} (F : Γ.Obj.Hom C D) : (Cat.Hom Obj Cat) := Γ.pullback.Hom C D F


-- notation "D(" "p_" "(" ")"  F ")" => pullback Γ


-- def geodeBot (Γ:geode) : Γ.Obj.Obj ⊛_(Γ) (Γ.:μ.Obj Pnt) := Γ.Idn


-- notation : 1000 "⊥_(" Γ ")" => geodeBot Γ


-- def geodeOvrType (Γ : geode) : Type := sorry

-- def geodeOvr (Γ:geode) (X : Γ.Obj.Obj) : Γ.geodeOvrType := sorry


-- notation "χ_(" ")"








def Geo : category := sorry







def P (Γ : geode) : Cat.Hom Γ.Obj Γ.Obj := sorry


notation "P_(" Γ ")" => P Γ


-- definition of a geodesic
/-
def geodesic (Γ : representation)
-/


-- defining a map of unitial geodes
/-

-/


-- defining the identity map of a unitial geode
/-

-/


-- defining the identity map of a unitial geode
/-

-/


-- proving the first identity law for composition of unitial geode maps
/-

-/


-- proving the second identity law for composition of unitial geode maps
/-

-/


-- proving the associativity law for composition of unitial geode maps
/-

-/


-- proving the
def IdnGeo : category := sorry


notation : 1000 "𝔾𝕖𝕠" => IdnGeo


-- Set.Obj
def 𝕊𝕖𝕥Obj : category := Set


--


--


--


-- Set.point


-- Set.universe


-- Set.⊥


-- Set.overobject classifier axiom


-- definition of an internal category in a pullback system
-- structure internal_category (Γ : Geo.Obj) (C : Geo.Obj) where
--  Obj : Γ.Obj.Obj
--  Mor : Γ.Obj.Obj
--  Dom : Γ.Obj.Hom Mor Obj
--  Cod : Γ.Obj.Hom Mor Obj
--  Idn : Γ.Obj.Hom Obj Mor
--  Cmp : Γ.M
--
--
--


-- definition of an internal functor in a pullback system
-- def internal_functor ()


-- definition of the identity internal functor in a pullback system
-- def


-- definition of the composition of internal functors in a pullback system
/-

-/


-- definition of the first identity law in a pullback system
/-

-/


-- definition of the second identity law in a pullback system
/-

-/


-- definition of the associativity law in a pullback system
/-

-/


-- internal C-sheaves
/-

-/


-- defining an internal functor between internal C-sheaves
/-

-/


-- defining the identity internal functor of an internal C-sheaf
/-

-/


-- defining the composition of internal functors
/-

-/


-- proving the second identity law for internal functors
/-

-/


-- proving the associativity law for internal functors
/-

-/


-- assembling the category of internal categories in a pullback system
/-

-/


-- notation "D(∞-Cat⁄" C ")" => D(∞-ℂ𝕒𝕥).μ.Obj C
-- notation F ": D(∞-Cat/" C ")" =>


-- F
-- notation "D(∞-Cat⁄" C ")" => D(∞-ℂ𝕒𝕥).μ.Hom C C (𝟙_(Cat)C)


def homotopy_yoneda_principal : Prop := sorry


-- f pullback Id is an internal C-sheaf
/-

-/


-- defining ∞-category
inductive infinity_category where
| Pnt : infinity_category


notation "∞-category" => infinity_category


-- defining ∞-functor (C : ∞-category) (D : ∞-category)
--inductive infinity_functor (C : ∞-category) (D : ∞-category) where
--| Idn : (C₀ : ∞-category) → infinity_functor C₀ C₀


--notation "∞-functor" => infinity_functor


-- defining ∞-natural_transformation
--inductive infinity_natural_transformation (C : ∞-category) (D : ∞-category) (F : ∞-functor C D) (G : ∞-functor C D) where
--| Idn : infinity_natural_transformation C D F G


-- notation for infinity_natural_transformation


-- defining a homotopy
-- inductive homotopy (C : ∞-category) (D : ∞-category) (F : ∞-functor C D) (G : ∞-functor C D) (ε : )


-- defining
--def infinity_natural_transformation_up_to_homotopy (C : ∞-category) (D : ∞-category) (F : ∞-functor C D) (G : ∞-functor C D) : Type := sorry


def InfCat : category := sorry


notation ∞-Cat => InfCat


-- theorem  : Prop := sorry
/-
∞-Cat is the universal representation with the fixed point principal.
-/



-- definition of an internal groupoid
/-

-/


-- map of internal groupoids
/-

-/


-- idn for internal groupoids
/-

-/


-- idn for internal groupoids
/-

-/


-- defining the first identity component for internal groupoids
/-

-/


-- defining the second identity component for internal groupoids
/-

-/


-- defining the associativity of internal groupoids
/-

-/


-- assembling internal groupoids
/-

-/



-- def goal₁ : ℕ ≅_(Set) Nat


-- def goal₂ : ℤ ≅_(Set) Int


-- def goal₃ : D(∞-Grpd/S¹).Hom *_(∞-ℂ𝕒𝕥) ℝ ≅_(Set) Reals
