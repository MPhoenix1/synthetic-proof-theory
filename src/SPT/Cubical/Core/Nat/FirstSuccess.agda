{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Core.Nat.FirstSuccess where

-- The first successful index of a partial sequence ℕ → Maybe X.  Its type
-- is a proposition, and every successful index normalizes to it.  Through
-- maps between a type A and successful indices, this selects an actual
-- point of A from a proposition-only existence statement about A.

open import Agda.Primitive using (Level)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Level using (Lift; lift; lower)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; cong₂)
open import Relation.Nullary using (Dec; yes; no)

open import SPT.Cubical.Core.Equality using (IsProposition; DependentΠExt)
open import SPT.Cubical.Core.Nat.Order using
  (_<ℕᶜ_; _≤ℕᶜ_; cmpℕᶜ; cmpℕ<zero-impossible; <ℕᶜ-suc;
   <ℕᶜ-suc-split; <ℕᶜ-trans)
import SPT.Cubical.Core.Nat.Least as Least
import SPT.Cubical.Core.Equality.Cover as Cover

-- Hits and misses of one partial sequence.  A successful address and the
-- prefix of misses before it consist of natural numbers and units only,
-- whatever the universe level of X.
module Sequence {κ : Level} {X : Set κ} (enum : ℕ → Maybe X) where

  Hit Miss : ℕ → Set
  Hit n with enum n
  ... | nothing = ⊥
  ... | just x = ⊤
  Miss n with enum n
  ... | nothing = ⊤
  ... | just x = ⊥

  value : (n : ℕ) → Hit n → X
  value n with enum n
  ... | nothing = λ ()
  ... | just x = λ _ → x

  selects : (n : ℕ) (hit : Hit n) → enum n ≡ just (value n hit)
  selects n hit with enum n
  selects n () | nothing
  selects n hit | just x = refl

  hit : (n : ℕ) (x : X) → enum n ≡ just x → Hit n
  hit n x selected with enum n
  hit n x () | nothing
  hit n x selected | just y = tt

  read : (n : ℕ) → Hit n → Σ X (λ x → enum n ≡ just x)
  read n hit with enum n
  read n () | nothing
  read n hit | just x = x , refl

  hit-proposition : (n : ℕ) → IsProposition (Hit n)
  hit-proposition n with enum n
  ... | nothing = λ ()
  ... | just x = λ { tt tt → refl }

  miss-proposition : (n : ℕ) → IsProposition (Miss n)
  miss-proposition n with enum n
  ... | nothing = λ { tt tt → refl }
  ... | just x = λ ()

  clash : (n : ℕ) → Hit n → Miss n → ⊥
  clash n with enum n
  ... | nothing = λ ()
  ... | just x = λ _ ()

  decide : (n : ℕ) → Dec (Hit n)
  decide n with enum n
  ... | nothing = no (λ ())
  ... | just x = yes tt

  missing : (n : ℕ) → (Hit n → ⊥) → Miss n
  missing n with enum n
  ... | nothing = λ _ → tt
  ... | just x = λ refute → refute tt

  Before : ℕ → Set
  Before zero = ⊤
  Before (suc n) = Before n × Miss n

  before-proposition : (n : ℕ) → IsProposition (Before n)
  before-proposition zero tt tt = refl
  before-proposition (suc n) (a , b) (a′ , b′) =
    cong₂ _,_ (before-proposition n a a′) (miss-proposition n b b′)

  at : (m n : ℕ) → m <ℕᶜ n → Before n → Miss m
  at m zero earlier prefix = ⊥-elim (cmpℕ<zero-impossible m earlier)
  at m (suc n) earlier (prefix , last) with <ℕᶜ-suc-split m n earlier
  ... | inj₁ smaller = at m n smaller prefix
  ... | inj₂ refl = last

  prefix : (n : ℕ) → ((m : ℕ) → m <ℕᶜ n → Miss m) → Before n
  prefix zero absent = tt
  prefix (suc n) absent =
    prefix n (λ m earlier → absent m
      (<ℕᶜ-trans {a = m} {b = n} {c = suc n} earlier (<ℕᶜ-suc n)))
    , absent n (<ℕᶜ-suc n)

  Address First : Set
  Address = Σ ℕ Hit
  First = Σ ℕ (λ n → Before n × Hit n)

  index-unique : (a b : First) → proj₁ a ≡ proj₁ b
  index-unique (n , before , hit) (m , before′ , hit′) with cmpℕᶜ n m
  ... | inj₁ earlier = ⊥-elim (clash n hit (at n m earlier before′))
  ... | inj₂ (inj₁ same) = same
  ... | inj₂ (inj₂ earlier) = ⊥-elim (clash m hit′ (at m n earlier before))

  least : (m : First) (a : Address) → proj₁ m ≤ℕᶜ proj₁ a
  least (m , before , found) (n , hit) with cmpℕᶜ m n
  ... | inj₁ earlier = inj₁ earlier
  ... | inj₂ (inj₁ same) = inj₂ same
  ... | inj₂ (inj₂ earlier) = ⊥-elim (clash n hit (at n m earlier before))

  certificate-proposition : (n : ℕ) → IsProposition (Before n × Hit n)
  certificate-proposition n (a , b) (a′ , b′) =
    cong₂ _,_ (before-proposition n a a′) (hit-proposition n b b′)

  proposition : IsProposition First
  proposition a b with index-unique a b
  proposition (n , a) (.n , b) | refl =
    cong (n ,_) (certificate-proposition n a b)

  -- Normalization by bounded search (Nat.Least).  Only the finite prefix of
  -- misses is kept, so no equality of minimality functions is needed.
  normalize : Address → First
  normalize (n , hit) with Least.leastUpTo Hit decide n hit
  ... | Least.least-witness m found minimal =
    m , prefix m (λ k earlier → missing k (minimal k earlier)) , found

  include : First → Address
  include (n , before , hit) = n , hit

  normalize-include : (m : First) → normalize (include m) ≡ m
  normalize-include m = proposition (normalize (include m)) m

  normalize-constant : (a b : Address) → normalize a ≡ normalize b
  normalize-constant a b = proposition (normalize a) (normalize b)

  normalize-bound : (a : Address) → proj₁ (normalize a) ≤ℕᶜ proj₁ a
  normalize-bound a = least (normalize a) a

  -- The proposition First, lifted to an arbitrary level ℓ.
  module Lifted (ℓ : Level) where

    M : Set ℓ
    M = Lift ℓ First

    M-proposition : IsProposition M
    M-proposition (lift a) (lift b) = cong lift (proposition a b)

    first : Cover.CoveredAt ℓ Address → M
    first covered = Cover.extractProposition
      (Cover.mapCovered (λ a → lift (normalize a)) covered) M-proposition

    choose : Cover.CoveredAt ℓ Address → Address
    choose covered = include (lower (first covered))

    choose-first : (covered : Cover.CoveredAt ℓ Address) → First
    choose-first covered = lower (first covered)


-- Selection in A through successful addresses of one sequence.  Since First
-- is a proposition, a CoveredAt-statement about A yields an actual point of
-- A.  No inverse law for `address` and `decode` is assumed, so the selected
-- point need not be the point that was covered.
module Selection
    {ℓ κ ν : Level} {X : Set κ} {A : Set ν}
    (enum : ℕ → Maybe X)
    (address : A → Sequence.Address enum)
    (decode : Sequence.Address enum → A)
  where

  private
    module Enumeration = Sequence enum
    module Raised = Enumeration.Lifted ℓ

  M : Set ℓ
  M = Raised.M

  proposition : IsProposition M
  proposition = Raised.M-proposition

  admit : A → M
  admit x = lift (Enumeration.normalize (address x))

  out : M → A
  out m = decode (Enumeration.include (lower m))

  admit-out : (m : M) → admit (out m) ≡ m
  admit-out m = proposition (admit (out m)) m

  first : Cover.CoveredAt ℓ A → M
  first covered = Cover.extractProposition
    (Cover.mapCovered admit covered) proposition

  choose : Cover.CoveredAt ℓ A → A
  choose covered = out (first covered)

  choose-constant : (u v : Cover.CoveredAt ℓ A) → choose u ≡ choose v
  choose-constant u v = cong out (proposition (first u) (first v))

  first-on-point : (x : A) → first (Cover.pointCovered x) ≡ admit x
  first-on-point x = refl

  choose-on-point : (x : A) → choose (Cover.pointCovered x) ≡ out (admit x)
  choose-on-point x = refl

  -- Extensionality is used only to state constancy as an equality of
  -- functions; everything above is constructed without it.
  module WithΠExt
      (maps : DependentΠExt (Cover.CoveredAt ℓ A) (λ _ → A))
    where

    constant : (u : Cover.CoveredAt ℓ A) → choose ≡ (λ _ → choose u)
    constant u = maps choose (λ _ → choose u) (λ v → choose-constant v u)
