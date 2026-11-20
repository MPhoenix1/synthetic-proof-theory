{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Polynomial.Discriminator where

-- The carriers built from smallness keep the returned family that selects
-- each continuation domain. A branching gives two rules: a seed at each
-- point of B, read out by a family, and a branch taking an A-indexed family
-- of seeds and then a family of seeds over the type chosen from their
-- readouts (`Branching`, `rule`, `rules`). For any extensionality and any
-- smallness, a derived seed reads out to the family (`seed-β`) and a branch
-- to its chosen domain (`domain`, `branch-β`). In the example the readouts
-- are empty at ₀ and unit at ₁ and the domain is the product of the two
-- readouts: two families of seeds empty the domain while a third inhabits
-- it (`no-left`, `no-right`, `point`), so one branch reads out to an
-- inhabited type and another to an empty one (`inhabited`, `empty`). Every
-- algebra of the example keeps its two seeds apart (`distinct`).

open import SPT.Base

open import SPT.IR.Polynomial using
  (var; con; sigma; pi; Description; described; Rules; scheme;
   Extensionality; readout)
open import SPT.IR.Polynomial.Algebra using (Algebra)
import SPT.Mahlo.DS.Polynomial.Smallness as Derived
open import SPT.IR.Smallness using (Smallness)

------------------------------------------------------------------------
-- Branchings and their rules

record Branching (ℓ : Level) : Set (lsuc ℓ) where
  field
    A B : Set ℓ
    family : B → Set ℓ
    choose : (A → Set ℓ) → Set ℓ

-- ₀ ↦ a seed at a point of B; ₁ ↦ a branch.
rule :
  {ℓ : Level} → Branching ℓ → (i : Lift ℓ 𝟚)
  → Description ℓ (lsuc ℓ) (λ (_ : Lift ℓ 𝟚) → Set ℓ) (Set ℓ)
rule b (lift ₀) =
  described (con (Branching.B b)) (λ x → Branching.family b (lower x))
rule b (lift ₁) =
  described
    (sigma (pi (Branching.A b) (λ _ → var (lift ₀)))
      (λ u → pi (Branching.choose b u) (λ _ → var (lift ₀))))
    (λ v → Branching.choose b (pr₁ v))

rules : {ℓ : Level} → Branching ℓ → Rules ℓ
rules {ℓ} b = record { Index = Lift ℓ 𝟚 ; rule = rule b }

------------------------------------------------------------------------
-- The derived carriers keep the selecting family

module _
  {ℓ : Level} (extensionality : Extensionality ℓ (lsuc ℓ))
  (small : Smallness ℓ) (b : Branching ℓ)
  where

  seed : Branching.B b → Derived.μ extensionality small (rules b) (lift ₀)
  seed x = Derived.make extensionality small (rules b) (lift ₀) x

  seed-β :
    (x : Branching.B b)
    → Derived.value extensionality small (rules b) (lift ₀) (seed x)
      ＝ Branching.family b x
  seed-β x = Derived.make-β extensionality small (rules b) (lift ₀) x

  domain :
    (Branching.A b → Derived.μ extensionality small (rules b) (lift ₀))
    → Set ℓ
  domain f =
    Branching.choose b
      (λ a → Derived.value extensionality small (rules b) (lift ₀) (f a))

  branch :
    (f : Branching.A b → Derived.μ extensionality small (rules b) (lift ₀))
    → (domain f → Derived.μ extensionality small (rules b) (lift ₀))
    → Derived.μ extensionality small (rules b) (lift ₁)
  branch f g = Derived.make extensionality small (rules b) (lift ₁) (f , g)

  branch-β :
    (f : Branching.A b → Derived.μ extensionality small (rules b) (lift ₀))
    (g : domain f → Derived.μ extensionality small (rules b) (lift ₀))
    → Derived.value extensionality small (rules b) (lift ₁) (branch f g)
      ＝ domain f
  branch-β f g =
    Derived.make-β extensionality small (rules b) (lift ₁) (f , g)

------------------------------------------------------------------------
-- An example

-- Readouts empty at ₀ and unit at ₁; the domain is the product of the two
-- readouts.

readouts : 𝟚 → Set
readouts ₀ = 𝟘
readouts ₁ = 𝟙

example : Branching lzero
example = record
  { A = 𝟚
  ; B = 𝟚
  ; family = readouts
  ; choose = λ F → F ₀ × F ₁
  }

-- Every algebra of the example keeps its two seeds apart.
distinct :
  (M : Algebra (scheme (rules example)))
  → Algebra.operation M (lift ₀) ₀ ＝ Algebra.operation M (lift ₀) ₁ → 𝟘
distinct M same =
  transport (λ X → X)
    ( Algebra.law M (lift ₀) ₁ ⁻¹
    ∙ ( ap (readout (Algebra.family M) (lift ₀)) same ⁻¹
      ∙ Algebra.law M (lift ₀) ₀))
    ⋆

module _
  (extensionality : Extensionality lzero (lsuc lzero))
  (small : Smallness lzero)
  where

  -- The seeds as they are, swapped, and constant at ₁.
  left right full :
    𝟚 → Derived.μ extensionality small (rules example) (lift ₀)
  left x = seed extensionality small example x
  right ₀ = seed extensionality small example ₁
  right ₁ = seed extensionality small example ₀
  full x = seed extensionality small example ₁

  no-left : domain extensionality small example left → 𝟘
  no-left (x , y) =
    transport (λ X → X) (seed-β extensionality small example ₀) x

  no-right : domain extensionality small example right → 𝟘
  no-right (x , y) =
    transport (λ X → X) (seed-β extensionality small example ₀) y

  point : domain extensionality small example full
  point =
    transport (λ X → X) (seed-β extensionality small example ₁ ⁻¹) ⋆ ,
    transport (λ X → X) (seed-β extensionality small example ₁ ⁻¹) ⋆

  continued : Derived.μ extensionality small (rules example) (lift ₁)
  continued =
    branch extensionality small example full
      (λ _ → seed extensionality small example ₁)

  inhabited :
    Derived.value extensionality small (rules example) (lift ₁) continued
  inhabited =
    transport (λ X → X)
      ( branch-β extensionality small example full
          (λ _ → seed extensionality small example ₁)
      ⁻¹)
      point

  vacant : Derived.μ extensionality small (rules example) (lift ₁)
  vacant =
    branch extensionality small example left (λ d → 𝟘-elim (no-left d))

  empty :
    Derived.value extensionality small (rules example) (lift ₁) vacant → 𝟘
  empty v =
    no-left
      ( transport (λ X → X)
          ( branch-β extensionality small example left
              (λ d → 𝟘-elim (no-left d)))
          v)
