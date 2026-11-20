{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Residence.Adjoined.Realizability where

-- Realizers of points of the generated Tarski names, by recursion on
-- their formation (Realized). Products act uniformly on realizers,
-- sums pair them, and Realized-Tree pairs the label realizer with a
-- function on the realizers of the branches. A given atoms predicate
-- realizes the lower family; identities, the lower names and adjoined
-- points are realized uniformly. realized reads a name's formation.

open import SPT.Base
open import SPT.Foundation.Impredicative.Realizability.CombinatoryAlgebra
  using (Partial-Combinatory-Algebra)
open import SPT.Foundation.Impredicative.Realizability.Recursion
  using (Numeral)
open import SPT.Foundation.Impredicative.Realizability.Two using (Bit)
open import SPT.Foundation.Impredicative.Realizability.Tripos using
  (predicates-are-subsets; Projections; Implies)
open import SPT.Foundation.Tree.W using (W; sup)
open import SPT.Mahlo.Residence.Adjoined using
  (Form; emptyᶠ; unitᶠ; twoᶠ; naturalᶠ; productᶠ; sumᶠ; treeᶠ; identityᶠ;
   liftedᶠ; belowᶠ; adjoinedᶠ; Name; decode)

module _ (𝔸 : Partial-Combinatory-Algebra lzero)
  (let open Partial-Combinatory-Algebra 𝔸 using (Carrier))
  {ℓ : Level} (L : Set ℓ) (D : L → Set ℓ) (I : Set (lsuc ℓ))
  (E : I → Set ℓ) (atoms : (l : L) → D l → Carrier → Set ℓ)
  (let Presented = predicates-are-subsets Carrier ℓ)
  (let Meet = λ (S T : Carrier → Set ℓ) → Projections ℓ 𝔸 Presented S T)
  (let Arrow = λ (S T : Carrier → Set ℓ) → Implies ℓ 𝔸 Presented S T)
  where

  mutual
    Realized : {X : Set ℓ} → Form L D I E X → X → Carrier → Set ℓ
    Realized emptyᶠ x r = Lift ℓ 𝟘
    Realized unitᶠ x r = Lift ℓ 𝟙
    Realized twoᶠ (lift b) r = Lift ℓ (Bit 𝔸 b r)
    Realized naturalᶠ (lift n) r = Lift ℓ (Numeral 𝔸 n r)
    Realized (productᶠ {A} F G) f e =
      (x : A) → Arrow (Realized F x) (Realized (G x) (f x)) e
    Realized (sumᶠ F G) (x , y) r =
      Meet (Realized F x) (Realized (G x) y) r
    Realized (treeᶠ F G) w r = Realized-Tree F G w r
    Realized (identityᶠ F x y) e r = Lift ℓ 𝟙
    Realized (liftedᶠ l) x r = atoms l x r
    Realized belowᶠ x r = Lift ℓ 𝟙
    Realized (adjoinedᶠ i) x r = Lift ℓ 𝟙

    -- A tree is realized by a pair of a realizer of its label and a
    -- function on the realizers of the branches.
    Realized-Tree :
        {A : Set ℓ}
        {B : A → Set ℓ}
      → Form L D I E A
      → ((x : A) → Form L D I E (B x))
      → W A B
      → Carrier
      → Set ℓ
    Realized-Tree {B = B} F G (sup x f) r =
      Meet
        ( Realized F x)
        ( λ e →
          (y : B x) →
            Arrow (Realized (G x) y) (Realized-Tree F G (f y)) e)
        r

  -- The realizers of the points of a name, read at its formation.
  realized : (a : Name L D I E) → decode L D I E a → Carrier → Set ℓ
  realized a x r = Realized (pr₂ a) x r
