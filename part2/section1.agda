module category.basic-category-theory.part2.section1 where

open import Level
open import Categories.Category
open import Categories.Functor
open import Categories.Functor.Hom using (module Hom; Hom[_][_,-]; Hom[_][-,_]; Hom[_][_,_])
open import Categories.Adjoint
open import Categories.Morphism using (Iso; IsIso; _≅_)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism)

postulate
  -- natural condition 1
  def1-1 : ∀ {o ℓ e} {C D : Category o ℓ e} {L : Functor C D} {R : Functor D C} (A : Category.Obj C)
      --------------------------------------------------------------------
    → NaturalIsomorphism Hom[ D ][ Functor.₀ L A ,-] (Hom[ C ][ A ,-] ∘F R)
  -- natural condition 2
  def1-2 : ∀ {o ℓ e} {C D : Category o ℓ e} {L : Functor C D} {R : Functor D C} (B : Category.Obj D)
      --------------------------------------------------------------------
    → NaturalIsomorphism (Hom[ D ][-, B ] ∘F (Functor.op L)) Hom[ C ][-, Functor.₀ R B ]
