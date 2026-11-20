{-# OPTIONS --safe --without-K #-}

module SPT.IR.Polynomial.Factorization.Discriminator where

-- The factorization at the finite stages. The numbers are stages whose
-- small types are the finitely covered ones, bounded by maxima (`numbers`).
-- A product of two recursive inputs lies in the stage of its larger input
-- (`pair-stage`, by refl), so the stages are not one. The product over the
-- numbers of the numbers themselves lies in no stage (`unbounded`), so at
-- the finite stages its growth hypothesis fails (`no-growth`): the bound at
-- products is what the factorization uses.

open import SPT.Base

open import SPT.IR.Polynomial using
  (Poly; var; pi; Family; carrier; Scheme; described)
open import SPT.IR.Polynomial.Factorization using
  (Stages; Within; Factored; Growth; onto)

------------------------------------------------------------------------
-- The finite stages

-- A finitely covered type: a cover by the numbers below some n. The
-- maximum of finitely many numbers lies above each of them.

record Covered (A : Set) : Set where
  field
    size : ℕ
    cover : Fin size → A
    covers : (x : A) → Σ (Fin size) (λ i → cover i ＝ x)

counted : (n : ℕ) → Covered (Fin n)
counted n = record
  { size = n
  ; cover = λ i → i
  ; covers = λ x → x , refl
  }

top : (n : ℕ) → (Fin n → ℕ) → ℕ
top zero g = zero
top (suc n) g = g fzero ⊔ℕ top n (λ i → g (fsuc i))

top-above : (n : ℕ) (g : Fin n → ℕ) (i : Fin n) → g i ≤ℕˢ top n g
top-above zero g ()
top-above (suc n) g fzero = ≤ℕˢ-⊔ˡ (g fzero) (top n (λ i → g (fsuc i)))
top-above (suc n) g (fsuc i) =
  ≤ℕˢ-trans (top-above n (λ j → g (fsuc j)) i)
    (≤ℕˢ-⊔ʳ (g fzero) (top n (λ j → g (fsuc j))))

-- The bound of a family over a finitely covered type: the maximum over
-- its cover.

maximum : (A : Set) → Covered A → (A → ℕ) → ℕ
maximum A c f = top (Covered.size c) (λ i → f (Covered.cover c i))

maximum-above :
  (A : Set) (c : Covered A) (f : A → ℕ) (x : A) → f x ≤ℕˢ maximum A c f
maximum-above A c f x =
  transport (λ y → f y ≤ℕˢ maximum A c f) (pr₂ (Covered.covers c x))
    (top-above (Covered.size c) (λ i → f (Covered.cover c i))
      (pr₁ (Covered.covers c x)))

numbers : Stages lzero lzero
numbers = record
  { Stage = ℕ
  ; _⊑_ = _≤ℕˢ_
  ; ⊑-refl = ≤ℕˢ-refl
  ; ⊑-trans = ≤ℕˢ-trans
  ; join = _⊔ℕ_
  ; join-left = ≤ℕˢ-⊔ˡ
  ; join-right = ≤ℕˢ-⊔ʳ
  ; Small = Covered
  ; bound = maximum
  ; bound-above = maximum-above
  }

------------------------------------------------------------------------
-- Two products of recursive inputs

-- One index carrying no information, and the numbers as the union, each
-- number lying in the stage it names. The product of two recursive inputs
-- grows boundedly: its only arity is finite.

Point : 𝟙 → Set
Point i = 𝟙

union : Family lzero lzero Point
union = record
  { carrier = λ i → ℕ
  ; readout = λ i n → ⋆
  }

rank : Σ 𝟙 (carrier union) → ℕ
rank x = pr₂ x

pair : Poly lzero lzero Point ((x : Fin 2) → Point ⋆)
pair = pi (Fin 2) {λ x → Point ⋆} (λ x → var ⋆)

pairs : Scheme lzero lzero
pairs = record
  { Index = 𝟙
  ; Data = Point
  ; rule = λ i → described pair (λ x → ⋆)
  }

pair-growth : Growth numbers pairs union rank
pair-growth i δ (inl z) o t = counted 2
pair-growth i δ (inr (x , z)) o ()

-- Inputs 3 and 5: the pair lies in stage 5, computed as the maximum.

three-five : Fin 2 → ℕ
three-five fzero = 3
three-five (fsuc i) = 5

pair-stage :
  Factored.stage (onto numbers pairs union rank pair-growth 0 ⋆ three-five)
  ＝ 5
pair-stage = refl

------------------------------------------------------------------------
-- The product over the numbers

-- The numbers themselves, as one argument of the product over the
-- numbers, have inputs in every stage, so they lie in none; by the
-- factorization the product's arity is then not small at any stage.

number : Poly lzero lzero Point ((x : ℕ) → Point ⋆)
number = pi ℕ {λ x → Point ⋆} (λ x → var ⋆)

naturals : Scheme lzero lzero
naturals = record
  { Index = 𝟙
  ; Data = Point
  ; rule = λ i → described number (λ x → ⋆)
  }

identity : ℕ → ℕ
identity n = n

unbounded : (γ : ℕ) → ¬ Within numbers union rank γ number identity
unbounded γ w = <ℕˢ-irrefl γ (w (suc γ , lift ⋆))

no-growth : ¬ Growth numbers naturals union rank
no-growth g =
  unbounded
    ( Factored.stage (onto numbers naturals union rank g 0 ⋆ identity))
    ( Factored.within (onto numbers naturals union rank g 0 ⋆ identity))
