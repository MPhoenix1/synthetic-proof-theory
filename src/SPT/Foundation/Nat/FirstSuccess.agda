{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Nat.FirstSuccess where

-- A partial sequence `enum : ℕ → Maybe X` hits at `n` when `enum n` is `just`,
-- and misses there otherwise; both are types with at most one point, decided at
-- each index, never both. The first success is an index that hits with a miss
-- at every earlier index. Its type `First` is a proposition, since two first
-- successes have the same index. Every successful address normalizes to it by
-- bounded search (`normalize`), and only the finite prefix of misses before it
-- is kept, so no identification of minimality functions is needed. Hits and
-- misses consist of natural numbers and units only, whatever the universe level
-- of `X`.
--
-- Because `First` is a proposition, a covered statement about a type `A` with
-- maps between `A` and the successful addresses selects an actual point of `A`
-- (`Selection`). No inverse law for those maps is assumed, so the selected
-- point need not be the point that was covered. Function extensionality is used
-- only to state that the selection is constant as an identification of
-- functions.

open import SPT.Base
open import SPT.Foundation.Propositions using (is-proposition)
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Covers using
  (Covered; covered-by-point; map-covered; extract-proposition)
open import SPT.Foundation.Nat.Order using
  ( _<ℕᶜ_; _≤ℕᶜ_; cmpℕᶜ; cmpℕ<zero-impossible; <ℕᶜ-suc; <ℕᶜ-suc-split
  ; <ℕᶜ-trans )
import SPT.Foundation.Nat.Least as Least

------------------------------------------------------------------------
-- The hits and misses of one sequence

module Sequence {κ : Level} {X : Set κ} (enum : ℕ → Maybe X) where

  Hit Miss : ℕ → Set
  Hit n = is-just (enum n)
  Miss n = is-nothing (enum n)

  value : (n : ℕ) → Hit n → X
  value n = from-just (enum n)

  selects : (n : ℕ) (hit : Hit n) → enum n ＝ just (value n hit)
  selects n = is-just-gives-just (enum n)

  hit : (n : ℕ) (x : X) → enum n ＝ just x → Hit n
  hit n = just-gives-is-just (enum n)

  read : (n : ℕ) → Hit n → Σ X (λ x → enum n ＝ just x)
  read n = read-just (enum n)

  hit-proposition : (n : ℕ) → is-proposition (Hit n)
  hit-proposition n = is-just-has-one-point (enum n)

  miss-proposition : (n : ℕ) → is-proposition (Miss n)
  miss-proposition n = is-nothing-has-one-point (enum n)

  clash : (n : ℕ) → Hit n → Miss n → 𝟘
  clash n = not-both-just-and-nothing (enum n)

  decide : (n : ℕ) → is-decidable (Hit n)
  decide n = being-just-is-decidable (enum n)

  missing : (n : ℕ) → ¬ Hit n → Miss n
  missing n = nothing-from-refutation (enum n)

------------------------------------------------------------------------
-- The misses before an index

  Before : ℕ → Set
  Before zero = 𝟙
  Before (suc n) = Before n × Miss n

  before-proposition : (n : ℕ) → is-proposition (Before n)
  before-proposition zero u v = refl
  before-proposition (suc n) (a , b) (a′ , b′) =
    ap₂ _,_ (before-proposition n a a′) (miss-proposition n b b′)

  at : (m n : ℕ) → m <ℕᶜ n → Before n → Miss m
  at m zero earlier prefix = 𝟘-elim (cmpℕ<zero-impossible m earlier)
  at m (suc n) earlier (prefix , last) =
    cases
      (λ smaller → at m n smaller prefix)
      (λ same → transport Miss (same ⁻¹) last)
      (<ℕᶜ-suc-split m n earlier)

  prefix : (n : ℕ) → ((m : ℕ) → m <ℕᶜ n → Miss m) → Before n
  prefix zero absent = ⋆
  prefix (suc n) absent =
    prefix n (λ m earlier →
      absent m (<ℕᶜ-trans m n (suc n) earlier (<ℕᶜ-suc n)))
    , absent n (<ℕᶜ-suc n)

------------------------------------------------------------------------
-- Addresses and the first success

  Address First : Set
  Address = Σ ℕ Hit
  First = Σ ℕ (λ n → Before n × Hit n)

------------------------------------------------------------------------
-- The first success is unique and least

  -- An earlier success would be a miss in the prefix of a later first success,
  -- so two first successes have the same index, and a first success lies at or
  -- below every successful address (`least-by-comparison` reads the case of the
  -- trichotomy).

  index-unique : (a b : First) → pr₁ a ＝ pr₁ b
  index-unique (n , before , hit) (m , before′ , hit′) =
    compared (cmpℕᶜ n m)
    where
    compared : Trichotomy _＝_ _<ℕᶜ_ n m → n ＝ m
    compared (inl earlier) = 𝟘-elim (clash n hit (at n m earlier before′))
    compared (inr (inl same)) = same
    compared (inr (inr earlier)) =
      𝟘-elim (clash m hit′ (at m n earlier before))

  least-by-comparison : (m n : ℕ) → Before m → Hit n →
    Trichotomy _＝_ _<ℕᶜ_ m n → m ≤ℕᶜ n
  least-by-comparison m n before hit (inl earlier) = inl earlier
  least-by-comparison m n before hit (inr (inl same)) = inr same
  least-by-comparison m n before hit (inr (inr earlier)) =
    𝟘-elim (clash n hit (at n m earlier before))

  least : (m : First) (a : Address) → pr₁ m ≤ℕᶜ pr₁ a
  least (m , before , found) (n , hit) =
    least-by-comparison m n before hit (cmpℕᶜ m n)

  certificate-proposition : (n : ℕ) → is-proposition (Before n × Hit n)
  certificate-proposition n (a , b) (a′ , b′) =
    ap₂ _,_ (before-proposition n a a′) (hit-proposition n b b′)

  proposition : is-proposition First
  proposition (n , c) (m , d) =
    same-index n m c d (index-unique (n , c) (m , d))
    where
    same-index : (n m : ℕ) (c : Before n × Hit n) (d : Before m × Hit m) →
      n ＝ m → (n , c) ＝ (m , d)
    same-index n .n c d refl = ap (n ,_) (certificate-proposition n c d)

------------------------------------------------------------------------
-- Normalization by bounded search

  first-from-least : Least.LeastWitness Hit → First
  first-from-least (Least.least-witness m found minimal) =
    m , prefix m (λ k earlier → missing k (minimal k earlier)) , found

  normalize : Address → First
  normalize (n , hit) = first-from-least (Least.leastUpTo Hit decide n hit)

  include : First → Address
  include (n , before , hit) = n , hit

  normalize-include : (m : First) → normalize (include m) ＝ m
  normalize-include m = proposition (normalize (include m)) m

  normalize-constant : (a b : Address) → normalize a ＝ normalize b
  normalize-constant a b = proposition (normalize a) (normalize b)

  normalize-bound : (a : Address) → pr₁ (normalize a) ≤ℕᶜ pr₁ a
  normalize-bound a = least (normalize a) a

------------------------------------------------------------------------
-- The first success at a universe level

  M : (ℓ : Level) → Set ℓ
  M ℓ = Lift ℓ First

  M-proposition : (ℓ : Level) → is-proposition (M ℓ)
  M-proposition ℓ (lift a) (lift b) = ap lift (proposition a b)

  first : (ℓ : Level) → Covered ℓ Address → M ℓ
  first ℓ covered =
    extract-proposition (map-covered (λ a → lift (normalize a)) covered)
      (M-proposition ℓ)

  choose : (ℓ : Level) → Covered ℓ Address → Address
  choose ℓ covered = include (lower (first ℓ covered))

  choose-first : (ℓ : Level) → Covered ℓ Address → First
  choose-first ℓ covered = lower (first ℓ covered)

------------------------------------------------------------------------
-- Selection in a type through successful addresses

module Selection {ℓ κ ν : Level} {X : Set κ} {A : Set ν}
  (enum : ℕ → Maybe X)
  (address : A → Sequence.Address enum)
  (decode : Sequence.Address enum → A) where

  M : Set ℓ
  M = Sequence.M enum ℓ

  proposition : is-proposition M
  proposition = Sequence.M-proposition enum ℓ

  admit : A → M
  admit x = lift (Sequence.normalize enum (address x))

  out : M → A
  out m = decode (Sequence.include enum (lower m))

  admit-out : (m : M) → admit (out m) ＝ m
  admit-out m = proposition (admit (out m)) m

  first : Covered ℓ A → M
  first covered = extract-proposition (map-covered admit covered) proposition

  choose : Covered ℓ A → A
  choose covered = out (first covered)

  choose-constant : (u v : Covered ℓ A) → choose u ＝ choose v
  choose-constant u v = ap out (proposition (first u) (first v))

  first-on-point : (x : A) → first (covered-by-point x) ＝ admit x
  first-on-point x = refl

  choose-on-point : (x : A) → choose (covered-by-point x) ＝ out (admit x)
  choose-on-point x = refl

  constant : FunExt (Covered ℓ A) (λ _ → A) →
    (u : Covered ℓ A) → choose ＝ (λ _ → choose u)
  constant maps u = maps choose (λ _ → choose u) (λ v → choose-constant v u)
