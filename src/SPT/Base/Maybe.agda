{-# OPTIONS --safe --without-K #-}

module SPT.Base.Maybe where

-- A point of `Maybe A` is either `nothing` or `just a` for a point `a` of `A`:
-- a value that may be absent, such as the entry of an enumeration at an index
-- where it has none. The two cases never meet, and `just` is injective. It is
-- the `Maybe` of `Agda.Builtin.Maybe`.
--
-- A partial value is just when it has the form `just a`, and is nothing
-- otherwise. These are types with at most one point, `𝟙` or `𝟘`, decided by
-- inspecting the value, never both; a value that is just has its point
-- (`from-just`), and is `just` of it.
--
-- Partial values under a map: `maybe-map f` sends `just a` to `just (f a)`
-- and `nothing` to `nothing`. A partial value is read with a default
-- (`maybe-rec`):
--
--   maybe-rec b f nothing = b,   maybe-rec b f (just a) = f a.

open import Agda.Builtin.Maybe public

open import SPT.Base.Universes
open import SPT.Base.Empty using (𝟘; ¬_)
open import SPT.Base.Unit using (𝟙; ⋆)
open import SPT.Base.Identity using (_＝_; refl; _≠_)
open import SPT.Base.Sigma using (Σ; _,_)
open import SPT.Base.Sum using (inl; inr)
open import SPT.Base.Decidable using (is-decidable)

module _ {ℓ : Level} {A : Set ℓ} where

  is-just : Maybe A → Set
  is-just nothing = 𝟘
  is-just (just _) = 𝟙

  is-nothing : Maybe A → Set
  is-nothing nothing = 𝟙
  is-nothing (just _) = 𝟘

  from-just : (m : Maybe A) → is-just m → A
  from-just (just a) _ = a

------------------------------------------------------------------------
-- Properties

module _ {ℓ : Level} {A : Set ℓ} where

  nothing-is-not-just : {a : A} → nothing ≠ just a
  nothing-is-not-just ()

  just-is-injective : {a b : A} → just a ＝ just b → a ＝ b
  just-is-injective refl = refl

  is-just-gives-just : (m : Maybe A) (h : is-just m) →
    m ＝ just (from-just m h)
  is-just-gives-just (just a) _ = refl

  just-gives-is-just : (m : Maybe A) (a : A) → m ＝ just a → is-just m
  just-gives-is-just (just b) a _ = ⋆

  read-just : (m : Maybe A) → is-just m → Σ A (λ a → m ＝ just a)
  read-just (just a) _ = a , refl

  is-just-has-one-point : (m : Maybe A) (u v : is-just m) → u ＝ v
  is-just-has-one-point (just a) u v = refl

  is-nothing-has-one-point : (m : Maybe A) (u v : is-nothing m) → u ＝ v
  is-nothing-has-one-point nothing u v = refl

  not-both-just-and-nothing : (m : Maybe A) → is-just m → ¬ is-nothing m
  not-both-just-and-nothing (just a) _ ()

  being-just-is-decidable : (m : Maybe A) → is-decidable (is-just m)
  being-just-is-decidable nothing = inr (λ ())
  being-just-is-decidable (just a) = inl ⋆

  nothing-from-refutation : (m : Maybe A) → ¬ is-just m → is-nothing m
  nothing-from-refutation nothing _ = ⋆
  nothing-from-refutation (just a) refutation = refutation ⋆

------------------------------------------------------------------------
-- Maps and recursion

module _ {ℓ κ : Level} {A : Set ℓ} {B : Set κ} where

  maybe-map : (A → B) → Maybe A → Maybe B
  maybe-map f nothing = nothing
  maybe-map f (just a) = just (f a)

  maybe-rec : B → (A → B) → Maybe A → B
  maybe-rec b f nothing = b
  maybe-rec b f (just a) = f a
