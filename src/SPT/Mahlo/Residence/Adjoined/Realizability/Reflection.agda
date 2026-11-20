{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Residence.Adjoined.Realizability.Reflection where

-- Uniform-Mahlo asks for Mahlo reflection of the generated Tarski names
-- whose reflected carriers are realized by every element of the given
-- combinatory algebra. It retains the reflection and its uniformity
-- witness, with no assumption on the realizers of the lower family.

open import SPT.Base
open import SPT.Foundation.Impredicative.Realizability.CombinatoryAlgebra
  using (Partial-Combinatory-Algebra)
import SPT.Mahlo.Specification as Reflection
open import SPT.Mahlo.Residence.Adjoined using (decode; name-formers)
open import SPT.Mahlo.Residence.Adjoined.Realizability using (realized)

module _ (𝔸 : Partial-Combinatory-Algebra lzero)
  (let open Partial-Combinatory-Algebra 𝔸 using (Carrier))
  {ℓ : Level} (L : Set ℓ) (D : L → Set ℓ) (I : Set (lsuc ℓ))
  (E : I → Set ℓ) (atoms : (l : L) → D l → Carrier → Set ℓ) where

  record Uniform-Mahlo : Set (lsuc ℓ) where
    field
      reflecting : Reflection.Mahlo (name-formers L D I E)
      uniform :
          (Ψ : Reflection.Operator (decode L D I E))
          (x : decode L D I E
            (Reflection.Reflection.carrier
              (Reflection.Mahlo.reflect reflecting Ψ)))
          (r : Carrier)
        → realized 𝔸 L D I E atoms
            (Reflection.Reflection.carrier
              (Reflection.Mahlo.reflect reflecting Ψ))
            x r
