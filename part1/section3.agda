module category.basic-category-theory.part1.section3 where

open import Data.Product using (proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Level
open import Categories.Category
open import Categories.Category.Equivalence
open import Categories.Category.SubCategory
open import Categories.Functor renaming (id to Fid)
open import Categories.Functor.Properties
open import Categories.NaturalTransformation
open import Categories.NaturalTransformation.NaturalIsomorphism
open import Categories.Morphism using (Iso; IsIso; _≅_)
open import Categories.Morphism.Reasoning.Core
open import Function.Surjection using (Surjective)
open import Function.Equality using (_⟨$⟩_; cong; _⟶_)
open import Function.Base renaming (id to id→)

-- essentially-surjective-and-fullyfaithful-intro-equivalence
prop18 : ∀ {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} (F : Functor C D)
  → EssentiallySurjective F
  → FullyFaithful F
    -----------------------
  → StrongEquivalence C D
prop18 {C = C} {D} F surj ⟨ full , faith ⟩ =
  record
    { F = F
    ; G = G
    ; weak-inverse = record
      { F∘G≈id = F∘G≈id
      ; G∘F≈id = G∘F≈id } }
  where
  module C = Category C
  module D = Category D
  module Cₕ = C.HomReasoning
  module Dₕ = D.HomReasoning
  module F = Functor F
  open Surjective
  
  -- D[F A, F B] → C[A, B]
  ff : ∀ {A B} → D.hom-setoid ⟶ C.hom-setoid
  ff {A} {B} = from (full {A} {B})

  ff-right-inv : ∀ {A B} (g : F.₀ A D.⇒ F.₀ B) → F.₁ (ff ⟨$⟩ g) D.≈ g
  ff-right-inv = right-inverse-of full

  ff-left-inv : ∀ {A B} (f : A C.⇒ B) → ff ⟨$⟩ F.₁ f C.≈ f
  ff-left-inv f = faith (ff ⟨$⟩ F.₁ f) f (ff-right-inv (F.₁ f))

  G₀ : D.Obj → C.Obj
  G₀ X = proj₁ (surj X)

  -- F ∘ G ⇒ I
  η : ∀ X → F.₀ (G₀ X) D.⇒ X
  η X = _≅_.from (proj₂ (surj X))

  η⁻¹ : ∀ X → X D.⇒ F.₀ (G₀ X)
  η⁻¹ X = _≅_.to (proj₂ (surj X))

  η-iso : ∀ X → Iso D (η X) (η⁻¹ X)
  η-iso X = _≅_.iso (proj₂ (surj X))

  η⁻¹∘η≈id : ∀ {X} → (η⁻¹ X D.∘ η X) D.≈ D.id
  η⁻¹∘η≈id {X} = Iso.isoˡ (η-iso X)

  η∘η⁻¹≈id : ∀ {X} → (η X D.∘ η⁻¹ X) D.≈ D.id
  η∘η⁻¹≈id {X} = Iso.isoʳ (η-iso X)

  G₁ : ∀ {X Y} → X D.⇒ Y → G₀ X C.⇒ G₀ Y
  G₁ {X} {Y} f = ff ⟨$⟩ (η⁻¹ Y) D.∘ f D.∘ (η X)

  G : Functor D C
  G =
    record
      { F₀ = G₀
      ; F₁ = G₁
      ; identity = identity
      ; homomorphism = homomorphism
      ; F-resp-≈ = F-resp-≈
      }
    where
    module G = Functor G

    identity : ∀ {A} → G₁ (D.id {A}) C.≈ C.id {G₀ A}
    identity {A} = Cₕ.begin
      G₁ D.id                           Cₕ.≈⟨ C.Equiv.refl ⟩
      ff ⟨$⟩ (η⁻¹ A) D.∘ D.id D.∘ (η A)  Cₕ.≈⟨ cong ff (Dₕ.refl⟩∘⟨ D.identityˡ) ⟩
      ff ⟨$⟩ (η⁻¹ A) D.∘ (η A)           Cₕ.≈⟨ cong ff η⁻¹∘η≈id ⟩
      ff ⟨$⟩ D.id                        Cₕ.≈˘⟨ cong ff F.identity ⟩
      ff ⟨$⟩ F.₁ C.id                    Cₕ.≈⟨ ff-left-inv C.id ⟩
      C.id                              Cₕ.∎
    
    homomorphism : ∀ {X Y Z} {f : X D.⇒ Y} {g : Y D.⇒ Z}
      → G₁ (g D.∘ f) C.≈ G₁ g C.∘ G₁ f
    homomorphism {X} {Y} {Z} {f} {g} = Cₕ.begin
      G₁ (g D.∘ f)                                                                  Cₕ.≈⟨ C.Equiv.refl ⟩
      ff ⟨$⟩ η⁻¹ Z D.∘ (g D.∘ f) D.∘ η X                                             Cₕ.≈⟨ cong ff (Dₕ.refl⟩∘⟨ insertInner D η∘η⁻¹≈id Dₕ.⟩∘⟨refl) ⟩
      ff ⟨$⟩ η⁻¹ Z D.∘ ((g D.∘ η Y) D.∘ (η⁻¹ Y D.∘ f)) D.∘ η X                       Cₕ.≈⟨ cong ff (pull-first D D.Equiv.refl) ⟩
      ff ⟨$⟩ (η⁻¹ Z D.∘ g D.∘ η Y) D.∘ (η⁻¹ Y D.∘ f) D.∘ η X                         Cₕ.≈⟨ cong ff (Dₕ.refl⟩∘⟨ D.assoc) ⟩
      ff ⟨$⟩ (η⁻¹ Z D.∘ g D.∘ η Y) D.∘ (η⁻¹ Y D.∘ f D.∘ η X)                         Cₕ.≈˘⟨ cong ff (ff-right-inv _ Dₕ.⟩∘⟨ ff-right-inv _) ⟩
      ff ⟨$⟩ F.₁ (ff ⟨$⟩ η⁻¹ Z D.∘ g D.∘ η Y) D.∘ F.₁ (ff ⟨$⟩ η⁻¹ Y D.∘ f D.∘ η X)     Cₕ.≈⟨ cong ff D.Equiv.refl ⟩
      ff ⟨$⟩ F.₁ (G₁ g) D.∘ F.₁ (G₁ f)                                              Cₕ.≈˘⟨ cong ff F.homomorphism ⟩
      ff ⟨$⟩ F.₁ (G₁ g C.∘ G₁ f)                                                    Cₕ.≈⟨ ff-left-inv _ ⟩
      G₁ g C.∘ G₁ f                                                                 Cₕ.∎

    F-resp-≈ : ∀ {A B} {f g : A D.⇒ B} → f D.≈ g → G₁ f C.≈ G₁ g
    F-resp-≈ {A} {B} {f} {g} f≈g = Cₕ.begin
      G₁ f                           Cₕ.≈⟨ C.Equiv.refl ⟩
      ff ⟨$⟩ (η⁻¹ B) D.∘ f D.∘ (η A)  Cₕ.≈⟨ cong ff (Dₕ.refl⟩∘⟨ f≈g Dₕ.⟩∘⟨refl) ⟩
      ff ⟨$⟩ (η⁻¹ B) D.∘ g D.∘ (η A)  Cₕ.≈⟨ C.Equiv.refl ⟩
      G₁ g                           Cₕ.∎
  
  F∘G≈id : F ∘F G ≃ Fid
  F∘G≈id =
    record
      { F⇒G = record
        { η = η
        ; commute = commute
        ; sym-commute = sym-commute }
      ; F⇐G = record
        { η = η⁻¹
        ; commute = commute′
        ; sym-commute = sym-commute′ }
      ; iso = η-iso }
    where
    module F∘G = Functor (F ∘F G)

    commute : ∀ {X Y} (f : X D.⇒ Y)
      → η Y D.∘ F∘G.₁ f D.≈ f D.∘ η X
    commute {X} {Y} f = Dₕ.begin
      η Y D.∘ F∘G.₁ f                         Dₕ.≈⟨ D.Equiv.refl ⟩
      η Y D.∘ F.₁ (ff ⟨$⟩ η⁻¹ Y D.∘ f D.∘ η X) Dₕ.≈⟨ Dₕ.refl⟩∘⟨ ff-right-inv _ ⟩
      η Y D.∘ η⁻¹ Y D.∘ f D.∘ η X              Dₕ.≈⟨ cancelˡ D η∘η⁻¹≈id ⟩
      f D.∘ η X                               Dₕ.∎

    sym-commute : ∀ {X Y} (f : X D.⇒ Y)
      → f D.∘ η X D.≈ η Y D.∘ F∘G.₁ f
    sym-commute {X} {Y} f = Dₕ.begin
      f D.∘ η X                                Dₕ.≈⟨ insertˡ D η∘η⁻¹≈id ⟩
      η Y D.∘ η⁻¹ Y D.∘ f D.∘ η X              Dₕ.≈˘⟨ Dₕ.refl⟩∘⟨ ff-right-inv _ ⟩
      η Y D.∘ F.₁ (ff ⟨$⟩ η⁻¹ Y D.∘ f D.∘ η X)  Dₕ.≈⟨ D.Equiv.refl ⟩
      η Y D.∘ F∘G.₁ f                          Dₕ.∎

    commute′ : ∀ {X Y} (f : X D.⇒ Y)
      → η⁻¹ Y D.∘ f D.≈ F∘G.₁ f D.∘ η⁻¹ X
    commute′ {X} {Y} f = Dₕ.begin
      η⁻¹ Y D.∘ f                                Dₕ.≈⟨ insertʳ D η∘η⁻¹≈id ⟩
      ((η⁻¹ Y D.∘ f) D.∘ η X) D.∘ η⁻¹ X          Dₕ.≈⟨ pullʳ D D.Equiv.refl Dₕ.⟩∘⟨refl ⟩
      (η⁻¹ Y D.∘ f D.∘ η X) D.∘ η⁻¹ X            Dₕ.≈˘⟨ ff-right-inv _ Dₕ.⟩∘⟨refl ⟩
      F.₁ (ff ⟨$⟩ η⁻¹ Y D.∘ f D.∘ η X) D.∘ η⁻¹ X  Dₕ.≈⟨ D.Equiv.refl ⟩
      F∘G.₁ f D.∘ η⁻¹ X                          Dₕ.∎

    sym-commute′ : ∀ {X Y} (f : X D.⇒ Y)
      → F∘G.₁ f D.∘ η⁻¹ X D.≈ η⁻¹ Y D.∘ f
    sym-commute′ {X} {Y} f = Dₕ.begin
      F∘G.₁ f D.∘ η⁻¹ X                          Dₕ.≈⟨ D.Equiv.refl ⟩
      F.₁ (ff ⟨$⟩ η⁻¹ Y D.∘ f D.∘ η X) D.∘ η⁻¹ X  Dₕ.≈⟨ ff-right-inv _ Dₕ.⟩∘⟨refl ⟩
      (η⁻¹ Y D.∘ f D.∘ η X) D.∘ η⁻¹ X            Dₕ.≈⟨ pushʳ D D.Equiv.refl Dₕ.⟩∘⟨refl ⟩
      ((η⁻¹ Y D.∘ f) D.∘ η X) D.∘ η⁻¹ X          Dₕ.≈⟨ cancelʳ D η∘η⁻¹≈id ⟩
      η⁻¹ Y D.∘ f                                Dₕ.∎

  G∘F≈id : G ∘F F ≃ Fid
  G∘F≈id =
    record
      { F⇒G = record
        { η = ε
        ; commute = commute
        ; sym-commute = sym-commute }
      ; F⇐G = record
        { η = ε⁻¹
        ; commute = commute′
        ; sym-commute = sym-commute′ }
      ; iso = ε-iso }
    where
    module G = Functor G
    module G∘F = Functor (G ∘F F)
    module F∘G = Functor (F ∘F G)

    ε : ∀ A → G∘F.₀ A C.⇒ A
    ε A = ff ⟨$⟩ η (F.₀ A)

    ε⁻¹ : ∀ A → A C.⇒ G∘F.₀ A
    ε⁻¹ A = ff ⟨$⟩ η⁻¹ (F.₀ A)

    ε-iso : ∀ A → Iso C (ε A) (ε⁻¹ A)
    ε-iso A =
      record
        { isoˡ = faith (ε⁻¹ A C.∘ ε A) C.id Fε∘ε⁻¹≈Fid
        ; isoʳ = faith (ε A C.∘ ε⁻¹ A) C.id Fε⁻¹∘ε≈Fid }
      where
      
      Fε∘ε⁻¹≈Fid : F.₁ (ε⁻¹ A C.∘ ε A) D.≈ F.₁ C.id
      Fε∘ε⁻¹≈Fid = Dₕ.begin
        F.₁ (ε⁻¹ A C.∘ ε A)                                Dₕ.≈⟨ F.homomorphism ⟩
        F.₁ (ε⁻¹ A) D.∘ F.₁ (ε A)                          Dₕ.≈⟨ D.Equiv.refl ⟩
        F.₁ (ff ⟨$⟩ η⁻¹ (F.₀ A)) D.∘ F.₁ (ff ⟨$⟩ η (F.₀ A)) Dₕ.≈⟨ ff-right-inv _ Dₕ.⟩∘⟨ ff-right-inv _ ⟩
        η⁻¹ (F.₀ A) D.∘ η (F.₀ A)                          Dₕ.≈⟨ η⁻¹∘η≈id ⟩
        D.id                                               Dₕ.≈˘⟨ F.identity ⟩
        F.₁ C.id                                           Dₕ.∎
      
      Fε⁻¹∘ε≈Fid : F.₁ (ε A C.∘ ε⁻¹ A) D.≈ F.₁ C.id
      Fε⁻¹∘ε≈Fid = Dₕ.begin
        F.₁ (ε A C.∘ ε⁻¹ A)                                 Dₕ.≈⟨ F.homomorphism ⟩
        F.₁ (ε A) D.∘ F.₁ (ε⁻¹ A)                           Dₕ.≈⟨ D.Equiv.refl ⟩
        F.₁ (ff ⟨$⟩ η (F.₀ A)) D.∘ F.₁ (ff ⟨$⟩ η⁻¹ (F.₀ A))  Dₕ.≈⟨ ff-right-inv _ Dₕ.⟩∘⟨ ff-right-inv _ ⟩
        η (F.₀ A) D.∘ η⁻¹ (F.₀ A)                           Dₕ.≈⟨ η∘η⁻¹≈id ⟩
        D.id                                                Dₕ.≈˘⟨ F.identity ⟩
        F.₁ C.id                                            Dₕ.∎
    
    commute : ∀ {A B} (f : A C.⇒ B)
      → ε B C.∘ G∘F.₁ f C.≈ f C.∘ ε A
    commute {A} {B} f = Cₕ.begin
      ε B C.∘ G∘F.₁ f                                                               Cₕ.≈⟨ C.Equiv.refl ⟩
      ε B C.∘ (ff ⟨$⟩ η⁻¹ (F.₀ B) D.∘ F.₁ f D.∘ η (F.₀ A))                           Cₕ.≈˘⟨ Cₕ.refl⟩∘⟨ cong ff (ff-right-inv _ Dₕ.⟩∘⟨ Dₕ.refl⟩∘⟨ ff-right-inv _) ⟩
      ε B C.∘ (ff ⟨$⟩ F.₁ (ff ⟨$⟩ η⁻¹ (F.₀ B)) D.∘ F.₁ f D.∘ F.₁ (ff ⟨$⟩ η (F.₀ A)))  Cₕ.≈⟨ Cₕ.refl⟩∘⟨ cong ff D.Equiv.refl ⟩
      ε B C.∘ (ff ⟨$⟩ F.₁ (ε⁻¹ B) D.∘ F.₁ f D.∘ F.₁ (ε A))                           Cₕ.≈˘⟨ Cₕ.refl⟩∘⟨ cong ff (Dₕ.refl⟩∘⟨ F.homomorphism) ⟩
      ε B C.∘ (ff ⟨$⟩ F.₁ (ε⁻¹ B) D.∘ F.₁ (f C.∘ ε A))                               Cₕ.≈˘⟨ Cₕ.refl⟩∘⟨ cong ff F.homomorphism ⟩
      ε B C.∘ (ff ⟨$⟩ F.₁ (ε⁻¹ B C.∘ f C.∘ ε A))                                     Cₕ.≈⟨ Cₕ.refl⟩∘⟨ ff-left-inv _ ⟩
      ε B C.∘ ε⁻¹ B C.∘ f C.∘ ε A                                                    Cₕ.≈⟨ cancelˡ C (Iso.isoʳ (ε-iso B)) ⟩
      f C.∘ ε A                                                                     Cₕ.∎
    
    sym-commute : ∀ {A B} (f : A C.⇒ B)
      → f C.∘ ε A C.≈ ε B C.∘ G∘F.₁ f
    sym-commute {A} {B} f = Cₕ.begin
      f C.∘ ε A                                                                      Cₕ.≈⟨ insertˡ C (Iso.isoʳ (ε-iso B)) ⟩
      ε B C.∘ ε⁻¹ B C.∘ f C.∘ ε A                                                    Cₕ.≈˘⟨ Cₕ.refl⟩∘⟨ ff-left-inv _ ⟩
      ε B C.∘ (ff ⟨$⟩ F.₁ (ε⁻¹ B C.∘ f C.∘ ε A))                                      Cₕ.≈⟨ Cₕ.refl⟩∘⟨ cong ff F.homomorphism ⟩
      ε B C.∘ (ff ⟨$⟩ F.₁ (ε⁻¹ B) D.∘ F.₁ (f C.∘ ε A))                                Cₕ.≈⟨ Cₕ.refl⟩∘⟨ cong ff (Dₕ.refl⟩∘⟨ F.homomorphism) ⟩
      ε B C.∘ (ff ⟨$⟩ F.₁ (ε⁻¹ B) D.∘ F.₁ f D.∘ F.₁ (ε A))                            Cₕ.≈⟨ Cₕ.refl⟩∘⟨ cong ff D.Equiv.refl ⟩
      ε B C.∘ (ff ⟨$⟩ F.₁ (ff ⟨$⟩ η⁻¹ (F.₀ B)) D.∘ F.₁ f D.∘ F.₁ (ff ⟨$⟩ η (F.₀ A)))   Cₕ.≈⟨ Cₕ.refl⟩∘⟨ cong ff (ff-right-inv _ Dₕ.⟩∘⟨ Dₕ.refl⟩∘⟨ ff-right-inv _) ⟩
      ε B C.∘ (ff ⟨$⟩ η⁻¹ (F.₀ B) D.∘ F.₁ f D.∘ η (F.₀ A))                            Cₕ.≈⟨ C.Equiv.refl ⟩
      ε B C.∘ G∘F.₁ f                                                                Cₕ.∎

    commute′ : ∀ {A B} (f : A C.⇒ B)
      → ε⁻¹ B C.∘ f C.≈ G∘F.₁ f C.∘ ε⁻¹ A
    commute′ {A} {B} f = Cₕ.begin
      ε⁻¹ B C.∘ f                                                                     Cₕ.≈⟨ insertʳ C (Iso.isoʳ (ε-iso A)) ⟩
      ((ε⁻¹ B C.∘ f) C.∘ ε A)                                              C.∘ ε⁻¹ A  Cₕ.≈⟨ pullʳ C C.Equiv.refl Cₕ.⟩∘⟨refl ⟩
      (ε⁻¹ B C.∘ f C.∘ ε A)                                                C.∘ ε⁻¹ A  Cₕ.≈˘⟨ ff-left-inv _ Cₕ.⟩∘⟨refl ⟩
      (ff ⟨$⟩ F.₁ (ε⁻¹ B C.∘ f C.∘ ε A))                                    C.∘ ε⁻¹ A  Cₕ.≈⟨ cong ff F.homomorphism Cₕ.⟩∘⟨refl ⟩
      (ff ⟨$⟩ F.₁ (ε⁻¹ B) D.∘ F.₁ (f C.∘ ε A))                              C.∘ ε⁻¹ A  Cₕ.≈⟨ cong ff (Dₕ.refl⟩∘⟨ F.homomorphism) Cₕ.⟩∘⟨refl ⟩
      (ff ⟨$⟩ F.₁ (ε⁻¹ B) D.∘ F.₁ f D.∘ F.₁ (ε A))                          C.∘ ε⁻¹ A  Cₕ.≈⟨ cong ff D.Equiv.refl Cₕ.⟩∘⟨refl ⟩
      (ff ⟨$⟩ F.₁ (ff ⟨$⟩ η⁻¹ (F.₀ B)) D.∘ F.₁ f D.∘ F.₁ (ff ⟨$⟩ η (F.₀ A))) C.∘ ε⁻¹ A  Cₕ.≈⟨ cong ff (ff-right-inv _ Dₕ.⟩∘⟨ Dₕ.refl⟩∘⟨ ff-right-inv _) Cₕ.⟩∘⟨refl ⟩
      (ff ⟨$⟩ η⁻¹ (F.₀ B) D.∘ F.₁ f D.∘ η (F.₀ A))                          C.∘ ε⁻¹ A  Cₕ.≈⟨ C.Equiv.refl ⟩
      G∘F.₁ f                                                              C.∘ ε⁻¹ A  Cₕ.∎
    
    sym-commute′ : ∀ {A B} (f : A C.⇒ B)
      → G∘F.₁ f C.∘ ε⁻¹ A C.≈ ε⁻¹ B C.∘ f
    sym-commute′ {A} {B} f = Cₕ.begin
      G∘F.₁ f                                                              C.∘ ε⁻¹ A  Cₕ.≈⟨ C.Equiv.refl ⟩
      (ff ⟨$⟩ η⁻¹ (F.₀ B) D.∘ F.₁ f D.∘ η (F.₀ A))                          C.∘ ε⁻¹ A  Cₕ.≈˘⟨ cong ff (ff-right-inv _ Dₕ.⟩∘⟨ Dₕ.refl⟩∘⟨ ff-right-inv _) Cₕ.⟩∘⟨refl ⟩
      (ff ⟨$⟩ F.₁ (ff ⟨$⟩ η⁻¹ (F.₀ B)) D.∘ F.₁ f D.∘ F.₁ (ff ⟨$⟩ η (F.₀ A))) C.∘ ε⁻¹ A  Cₕ.≈⟨ cong ff D.Equiv.refl Cₕ.⟩∘⟨refl ⟩
      (ff ⟨$⟩ F.₁ (ε⁻¹ B) D.∘ F.₁ f D.∘ F.₁ (ε A))                          C.∘ ε⁻¹ A  Cₕ.≈˘⟨ cong ff (Dₕ.refl⟩∘⟨ F.homomorphism) Cₕ.⟩∘⟨refl ⟩
      (ff ⟨$⟩ F.₁ (ε⁻¹ B) D.∘ F.₁ (f C.∘ ε A))                              C.∘ ε⁻¹ A  Cₕ.≈˘⟨ cong ff F.homomorphism Cₕ.⟩∘⟨refl ⟩
      (ff ⟨$⟩ F.₁ (ε⁻¹ B C.∘ f C.∘ ε A))                                    C.∘ ε⁻¹ A  Cₕ.≈⟨ ff-left-inv _ Cₕ.⟩∘⟨refl ⟩
      (ε⁻¹ B C.∘ f C.∘ ε A)                                                C.∘ ε⁻¹ A  Cₕ.≈⟨ pushʳ C C.Equiv.refl Cₕ.⟩∘⟨refl ⟩
      ((ε⁻¹ B C.∘ f) C.∘ ε A)                                              C.∘ ε⁻¹ A  Cₕ.≈⟨ cancelʳ C (Iso.isoʳ (ε-iso A)) ⟩
      ε⁻¹ B C.∘ f                                                                     Cₕ.∎

prop19 : ∀ {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} (F : Functor C D)
  → FullyFaithful F
  → StrongEquivalence C (FullSubCategory D (Functor.₀ F))
prop19 {C = C} {D} F fullfaith = prop18 F′ surj fullfaith
  where
  module C = Category C
  module D = Category D
  module F = Functor F

  C′ = FullSubCategory D F.₀
  module C′ = Category C′
  open Surjective

  F′ : Functor C C′
  F′ = record
    { F₀ = id→
    ; F₁ = F.₁
    ; identity = F.identity
    ; homomorphism = F.homomorphism
    ; F-resp-≈ = F.F-resp-≈
    }

  surj : EssentiallySurjective F′
  surj A′ = ⟨ A′ , Categories.Morphism.≅.refl C′ ⟩
