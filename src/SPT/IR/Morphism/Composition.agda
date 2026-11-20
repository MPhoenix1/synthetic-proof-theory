{-# OPTIONS --safe --without-K #-}

module SPT.IR.Morphism.Composition where

-- Identity and composition of morphisms of algebras (Morphism)
-- at Layers' adjusted extensionality, as the morphisms along the identity
-- translation (Translation.Morphism). The identity sends each code to
-- itself with refl (`identity`). The composite carries each point of N's
-- fiber by the second morphism, extended to the fibers of N's decoding
-- (`compose`). On valuations the identity is a two-sided unit and
-- composition is associative, pointwise (`identity-left`,
-- `identity-right`, `associative`).

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Fibers using (fiber)
open import SPT.Foundation.Induction.Initiality using (Section)

open import SPT.IR.Algebra using (Algebra; Law)
open import SPT.IR.Description using
  (Desc; Indexed; carrier; index; indexed)
open import SPT.IR.Layers using (normal)
open import SPT.IR.Morphism using (Morphism)
import SPT.IR.Translation as Translation
open import SPT.IR.Translation using (extend)
open import SPT.IR.Translation.Morphism using
  (identity-along; compose-along; along-morphism; morphism-along)

------------------------------------------------------------------------
-- Identity and composition

module _
  {s κ j : Level} {E : Set j} {γ : Desc {s = s} E}
  (arities : (A : Set s) (B : A → Set j) → FunExt A B)
  (M : Algebra κ γ) (law : Law M)
  where

  identity : Morphism (normal E arities) M M law law
  identity =
    along-morphism arities M M law law (identity-along arities M law)

module _
  {s κ κ′ κ″ j : Level} {E : Set j} {γ : Desc {s = s} E}
  (arities : (A : Set s) (B : A → Set j) → FunExt A B)
  (positions′ : (A : Set s) (B : A → Set (κ′ ⊔ j)) → FunExt A B)
  (positions″ : (A : Set s) (B : A → Set (κ″ ⊔ j)) → FunExt A B)
  (M : Algebra κ γ) (N : Algebra κ′ γ) (P : Algebra κ″ γ)
  (law : Law M) (law′ : Law N) (law″ : Law P)
  where

  compose :
    Morphism (normal E arities) N P law′ law″
    → Morphism (normal E arities) M N law law′
    → Morphism (normal E arities) M P law law″
  compose u v =
    along-morphism arities M P law law″
      ( compose-along arities positions′ arities positions″
          (Translation.identity γ) (Translation.identity γ) M N P
          law law′ law″
          (morphism-along arities N P law′ law″ u)
          (morphism-along arities M N law law′ v))

------------------------------------------------------------------------
-- Unit and associativity on valuations

-- A composite's valuation extends the second morphism along the first's
-- point in the fiber. Precomposing with the identity is computation;
-- postcomposing with it and reassociating are path induction on the
-- identification of decodings (`fiber-unit`, `extend-associative`).

fiber-unit :
  {ℓ κ : Level} {A : Set ℓ} {B : Set κ} (f : A → B) {b : B} (x : fiber f b)
  → transport (fiber f) (pr₂ x) (pr₁ x , refl) ＝ x
fiber-unit f (a , refl) = refl

module _
  {κ κ′ κ″ j : Level} {E : Set j}
  (Y : Indexed κ E) (Z : Indexed κ′ E) (W : Indexed κ″ E)
  (u : (k : carrier Y) → fiber (index Z) (index Y k))
  (v : (k : carrier Z) → fiber (index W) (index Z k))
  where

  extend-associative :
    (e : E) (x : fiber (index Y) e)
    → extend (λ a → a) Z W v e (extend (λ a → a) Y Z u e x)
      ＝ extend (λ a → a) Y W
          (λ k → extend (λ a → a) Z W v (index Y k) (u k)) e x
  extend-associative e (k , refl) = refl

module _
  {s κ κ′ j : Level} {E : Set j} {γ : Desc {s = s} E}
  (arities : (A : Set s) (B : A → Set j) → FunExt A B)
  (positions : (A : Set s) (B : A → Set (κ ⊔ j)) → FunExt A B)
  (positions′ : (A : Set s) (B : A → Set (κ′ ⊔ j)) → FunExt A B)
  (M : Algebra κ γ) (N : Algebra κ′ γ) (law : Law M) (law′ : Law N)
  (f : Morphism (normal E arities) M N law law′)
  where

  identity-right :
    (k : Algebra.K M)
    → Section.valuation
        ( compose arities positions positions′ M M N law law law′ f
            (identity arities M law))
        k
      ＝ Section.valuation f k
  identity-right k = refl

  identity-left :
    (k : Algebra.K M)
    → Section.valuation
        ( compose arities positions′ positions′ M N N law law′ law′
            (identity arities N law′) f)
        k
      ＝ Section.valuation f k
  identity-left k = fiber-unit (Algebra.value N) (Section.valuation f k)

module _
  {s κ κ′ κ″ κ‴ j : Level} {E : Set j} {γ : Desc {s = s} E}
  (arities : (A : Set s) (B : A → Set j) → FunExt A B)
  (positions′ : (A : Set s) (B : A → Set (κ′ ⊔ j)) → FunExt A B)
  (positions″ : (A : Set s) (B : A → Set (κ″ ⊔ j)) → FunExt A B)
  (positions‴ : (A : Set s) (B : A → Set (κ‴ ⊔ j)) → FunExt A B)
  (M : Algebra κ γ) (N : Algebra κ′ γ) (P : Algebra κ″ γ) (Q : Algebra κ‴ γ)
  (law : Law M) (law′ : Law N) (law″ : Law P) (law‴ : Law Q)
  (f : Morphism (normal E arities) M N law law′)
  (g : Morphism (normal E arities) N P law′ law″)
  (h : Morphism (normal E arities) P Q law″ law‴)
  where

  associative :
    (k : Algebra.K M)
    → Section.valuation
        ( compose arities positions′ positions‴ M N Q law law′ law‴
            ( compose arities positions″ positions‴ N P Q law′ law″ law‴
                h g)
            f)
        k
      ＝ Section.valuation
          ( compose arities positions″ positions‴ M P Q law law″ law‴ h
              ( compose arities positions′ positions″ M N P law law′ law″
                  g f))
          k
  associative k =
    extend-associative
      (indexed (Algebra.K N) (Algebra.value N))
      (indexed (Algebra.K P) (Algebra.value P))
      (indexed (Algebra.K Q) (Algebra.value Q))
      (Section.valuation g) (Section.valuation h)
      (Algebra.value M k) (Section.valuation f k)
      ⁻¹
