{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Residence.Constructors.Comparison where

-- A map between interpreted families acts on one layer of constructors.
-- `change` moves a layer along an identity of its interpretation map; `map`
-- then uses the literal composite source. `compare` obtains that identity
-- from a retained pointwise triangle under local extensionality. Each
-- construction preserves the selected parent interpretation by an identity;
-- the pointwise triangle alone supplies no conversion law.

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Mahlo.Specification using (Formers; Operator)
open import SPT.Mahlo.Residence.Constructors using (Code; interpret)
import SPT.Mahlo.Residence.Constructors as Constructors
open import SPT.Mahlo.Residence.Families using (Map)

------------------------------------------------------------------------
-- Change of interpretation on one carrier

module _
  {κ ℓ α : Level} {C : Set κ} {D : C → Set ℓ}
  {Ψ : Operator D} {A : Set α}
  where

  change : (j k : A → C) → j ＝ k → Code Ψ A j → Code Ψ A k
  change j k refl c = c

  change-interpret :
    (Q : Formers C D) (j k : A → C) (e : j ＝ k) (c : Code Ψ A j)
    → interpret Q (change j k e c) ＝ interpret Q c
  change-interpret Q j k refl c = refl

------------------------------------------------------------------------
-- A whole-map triangle supplies the action without extensionality

module _
  {κ ℓ α β : Level} {C : Set κ} {D : C → Set ℓ}
  {Ψ : Operator D} {A : Set α} {B : Set β}
  where

  map :
    (h : A → B) (j : A → C) (k : B → C)
    → (λ a → k (h a)) ＝ j → Code Ψ A j → Code Ψ B k
  map h j k e c =
    Constructors.map h k (change j (λ a → k (h a)) (e ⁻¹) c)

  interpret-map :
    (Q : Formers C D) (h : A → B) (j : A → C) (k : B → C)
    (e : (λ a → k (h a)) ＝ j) (c : Code Ψ A j)
    → interpret Q (map h j k e c) ＝ interpret Q c
  interpret-map Q h j k e c =
    Constructors.interpret-map Q h k (change j (λ a → k (h a)) (e ⁻¹) c)
    ∙ change-interpret Q j (λ a → k (h a)) (e ⁻¹) c

------------------------------------------------------------------------
-- A pointwise triangle needs extensionality only for the name maps

module _
  {κ ℓ α β : Level} {C : Set κ} {D : C → Set ℓ}
  {Ψ : Operator D} {A : Set α} {B : Set β}
  where

  compare :
    (ext : FunExt A (λ a → C)) (j : A → C) (k : B → C)
    → Map j k → Code Ψ A j → Code Ψ B k
  compare ext j k f c =
    map (Map.arrow f) j k
      (ext (λ a → k (Map.arrow f a)) j (Map.triangle f)) c

  interpret-compare :
    (Q : Formers C D) (ext : FunExt A (λ a → C))
    (j : A → C) (k : B → C) (f : Map j k) (c : Code Ψ A j)
    → interpret Q (compare ext j k f c) ＝ interpret Q c
  interpret-compare Q ext j k f c =
    interpret-map Q (Map.arrow f) j k
      (ext (λ a → k (Map.arrow f a)) j (Map.triangle f)) c
