{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Residence.Adjoined.Realizability.ExcludedMiddle where

-- Uniform realizers of sums over two have one tag (one-tag). If a lower
-- name has an empty left summand and another has an empty right summand,
-- that uniformity identifies the two projection combinators. refuted
-- excludes a tracker when those combinators differ.

open import SPT.Base
open import SPT.Foundation.Impredicative.Realizability.CombinatoryAlgebra
  using (Partial-Combinatory-Algebra; second)
open import SPT.Foundation.Impredicative.Realizability.Tripos using
  (Entailment; predicates-are-subsets)
open import SPT.Foundation.Impredicative.Realizability.Two using (Bit)
open import SPT.Mahlo.Residence.Adjoined using
  (Name; decode; two; product; sum; below)
open import SPT.Mahlo.Residence.Adjoined.Realizability using (realized)

------------------------------------------------------------------------
-- The tag of a point with an empty summand

module _ {ℓ : Level} (L : Set ℓ) (D : L → Set ℓ) (I : Set (lsuc ℓ))
  (E : I → Set ℓ) where

  tag-right :
      (F : Lift ℓ 𝟚 → Name L D I E)
    → (decode L D I E (F (lift ₀)) → 𝟘)
    → (v : Σ (Lift ℓ 𝟚) (λ c → decode L D I E (F c)))
    → lower (pr₁ v) ＝ ₁
  tag-right F absent (lift ₀ , y) = 𝟘-elim (absent y)
  tag-right F absent (lift ₁ , y) = refl

  tag-left :
      (F : Lift ℓ 𝟚 → Name L D I E)
    → (decode L D I E (F (lift ₁)) → 𝟘)
    → (v : Σ (Lift ℓ 𝟚) (λ c → decode L D I E (F c)))
    → lower (pr₁ v) ＝ ₀
  tag-left F absent (lift ₀ , y) = refl
  tag-left F absent (lift ₁ , y) = 𝟘-elim (absent y)

------------------------------------------------------------------------
-- One realizer has one tag

module _
  (𝔸 : Partial-Combinatory-Algebra lzero)
  (let open Partial-Combinatory-Algebra 𝔸 using
         (Carrier; apply; k; functional))
  {ℓ : Level} (L : Set ℓ) (D : L → Set ℓ) (I : Set (lsuc ℓ))
  (E : I → Set ℓ) (atoms : (l : L) → D l → Carrier → Set ℓ)
  (let Entails = λ (X : Set ℓ) (φ ψ : X → Carrier → Set ℓ) →
         Entailment ℓ 𝔸 (predicates-are-subsets Carrier ℓ) X φ ψ)
  where

  one-tag :
      (F : L → Lift ℓ 𝟚 → Name L D I E)
      (l₀ l₁ : L)
    → (decode L D I E (F l₀ (lift ₀)) → 𝟘)
    → (decode L D I E (F l₁ (lift ₁)) → 𝟘)
    → (f : (l : L) → Σ (Lift ℓ 𝟚) (λ c → decode L D I E (F l c)))
    → (s : Carrier)
    → realized 𝔸 L D I E atoms (product below (λ l → sum two (F l))) f s
    → k ＝ second 𝔸
  one-tag F l₀ l₁ absent-left absent-right f s m =
    let (c₀ , p₀ , ((a₀ , q₀ , lift b₀) , r₀)) = m l₀ k (lift ⋆)
        (c₁ , p₁ , ((a₁ , q₁ , lift b₁) , r₁)) = m l₁ k (lift ⋆)
    in (transport (λ b → Bit 𝔸 b a₁)
          (tag-left L D I E (F l₁) absent-right (f l₁)) b₁) ⁻¹
       ∙ functional q₁
           (transport (λ c → apply c k a₀) (functional p₀ p₁) q₀)
       ∙ transport (λ b → Bit 𝔸 b a₀)
           (tag-right L D I E (F l₀) absent-left (f l₀)) b₀

  -- A tracker of a closed term of such a product is refuted.
  refuted :
      (F : L → Lift ℓ 𝟚 → Name L D I E)
      (l₀ l₁ : L)
    → (decode L D I E (F l₀ (lift ₀)) → 𝟘)
    → (decode L D I E (F l₁ (lift ₁)) → 𝟘)
    → (k ＝ second 𝔸 → 𝟘)
    → (f : Lift ℓ 𝟙 → (l : L)
        → Σ (Lift ℓ 𝟚) (λ c → decode L D I E (F l c)))
    → Entails (Lift ℓ 𝟙) (λ x r → Lift ℓ 𝟙)
        (λ x →
          realized 𝔸 L D I E atoms (product below (λ l → sum two (F l)))
            (f x))
    → 𝟘
  refuted F l₀ l₁ absent-left absent-right differ f (e , tracker) =
    let (s , ps , ms) = tracker (lift ⋆) k (lift ⋆)
    in differ
         (one-tag F l₀ l₁ absent-left absent-right (f (lift ⋆)) s ms)
