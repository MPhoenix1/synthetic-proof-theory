{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Univalent.Reflector.Universes where

-- The Mahlo rule with unique names and Shulman's univalent universes
-- without elimination, each from the other. A univalent universe of a
-- description γ, with its formation, introduction and path rules, is an
-- algebra of γ with its law (`algebra`, `law`). At Ambient's description
-- of an operator Ψ that algebra is a closure of Ψ under the formers
-- (Ambient.closure), and by Lumsdaine's lemma (Universe.fibers) every
-- type has at most one name in it. So universes of the descriptions of
-- all operators give the rule with unique names (`reflector`), under
-- extensionality for families of types. Conversely the family of all
-- points is a generation of every algebra (`all-generated`), so the rule
-- with unique names gives the universe of every description through
-- Univalent.Reflector's `universe`, with no further hypothesis
-- (`universes`):
--
--   (Π Ψ. Universe ℓ (description Ψ))  →  Reflector ℓ,
--   Reflector ℓ  →  Π γ. Universe ℓ γ.
--
-- No derivation of those universes avoids unique names. Elimination
-- needs a least generation in place of all points
-- (Univalent.Reflector.elimination).

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
import SPT.Mahlo.Ambient as Ambient

open import SPT.IR.Algebra using (Algebra; Law)
open import SPT.Mahlo.DS.Ambient using (description; closure)
open import SPT.IR.Description using (Desc)
import SPT.Mahlo.DS.Realization as Realization
open import SPT.IR.Univalent.Generation using (Closed-Family)
open import SPT.Mahlo.DS.Univalent.Reflector using
  (Reflector; universe)
open import SPT.IR.Univalent.Universe using (Universe; fibers)

------------------------------------------------------------------------
-- The algebra of introductions

-- Mathematical shape: (Code , El , intro), with El (intro z) ＝ Mark γ z.

module _
  {ℓ : Level} {γ : Desc {s = ℓ} (Set ℓ)} (U : Universe ℓ γ)
  where

  algebra : Algebra ℓ γ
  algebra = record
    { K = Universe.Code U
    ; value = Universe.El U
    ; operation = Universe.intro U
    }

  law : Law algebra
  law = Universe.intro-β U

------------------------------------------------------------------------
-- The rule with unique names from the universes

-- Each operator's reflection is the algebra of introductions of the
-- universe of its description; its names are the fibers of El.

reflector :
  {ℓ : Level} → ((X : Set ℓ) → FunExt X (λ _ → Set ℓ))
  → ((Ψ : Ambient.Operator ℓ) → Universe ℓ (description Ψ))
  → Reflector ℓ
reflector extensionality universes = record
  { mahlo = record
      { reflect = λ Ψ → record
          { carrier = Algebra.K (algebra (universes Ψ))
          ; closure =
              closure extensionality Ψ (algebra (universes Ψ))
                (law (universes Ψ))
          }
      }
  ; unique = λ Ψ X → fibers (universes Ψ) X
  }

------------------------------------------------------------------------
-- The universes from the rule with unique names

-- Every point is generated: the family constantly the one-point type is
-- propositional and closed.

all-generated :
  {s κ j : Level} {E : Set j} {γ : Desc {s = s} E} (M : Algebra κ γ)
  {ν : Level} → Closed-Family M ν
all-generated M {ν} = record
  { family = λ _ → Lift ν 𝟙
  ; proposition = λ _ x y → refl
  ; closed = λ _ _ → lift ⋆
  }

-- Univalent.Reflector's universe at the generation of all points.

universes :
  {ℓ : Level} → Reflector ℓ → (γ : Desc {s = ℓ} (Set ℓ)) → Universe ℓ γ
universes R γ =
  universe R γ
    (all-generated (Realization.reflected-algebra (Reflector.mahlo R) γ))
