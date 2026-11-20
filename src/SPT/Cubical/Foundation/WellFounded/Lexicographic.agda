{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.WellFounded.Lexicographic where

-- The lexicographic order on pairs compares first components and, when these
-- are identified, second components. On a product `A × B` it is a relation
-- defined by cases; on a dependent pair type `Σ A B` it is an inductive family
-- with two rules:
--
--         a <A a′                        x <B a y
--   -------------------- earlier   ------------------- within
--   (a , x) < (a′ , y)               (a , x) < (a , y)
--
-- A step within one fiber shares its first component outright, so no transport
-- along an identification of first components is needed. Both orders are
-- well-founded when their components are, and the dependent one is transitive
-- when its components are. The predecessors of `(a , b)` are accessible when
-- the pairs over smaller first components are, and the pairs over `a` below `b`
-- (`lexicographic-predecessors-are-accessible`); induction in the fiber over
-- `a` then makes the whole fiber accessible
-- (`lexicographic-fiber-is-accessible`), and induction on first components
-- every pair.

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Accessibility using
  (is-accessible; acc; is-well-founded; accessible-induction)

------------------------------------------------------------------------
-- On products

module _ {ℓ κ μ ν : Level} {A : Set ℓ} {B : Set κ}
  (_<A_ : A → A → Set μ) (_<B_ : B → B → Set ν) where

  lexicographic : A × B → A × B → Set (ℓ ⊔ μ ⊔ ν)
  lexicographic p q =
    (pr₁ p <A pr₁ q) ⊎ ((pr₁ p ＝ pr₁ q) × (pr₂ p <B pr₂ q))

------------------------------------------------------------------------
-- On dependent pairs

module _ {ℓ κ μ ν : Level} {A : Set ℓ} (B : A → Set κ)
  (_<A_ : A → A → Set μ) (_<B_ : (a : A) → B a → B a → Set ν) where

  data dependent-lexicographic : Σ A B → Σ A B → Set (ℓ ⊔ κ ⊔ μ ⊔ ν)
    where
    earlier : {a a′ : A} {x : B a} {y : B a′} → a <A a′ →
      dependent-lexicographic (a , x) (a′ , y)
    within : (a : A) {x y : B a} → _<B_ a x y →
      dependent-lexicographic (a , x) (a , y)

------------------------------------------------------------------------
-- Well-foundedness on products

module _ {ℓ κ μ ν : Level} {A : Set ℓ} {B : Set κ}
  (_<A_ : A → A → Set μ) (_<B_ : B → B → Set ν) where

  lexicographic-predecessors-are-accessible : (a : A) →
    ((a′ : A) → a′ <A a → (b′ : B) →
      is-accessible (lexicographic _<A_ _<B_) (a′ , b′)) →
    (b : B) →
    ((b′ : B) → b′ <B b →
      is-accessible (lexicographic _<A_ _<B_) (a , b′)) →
    (p : A × B) → lexicographic _<A_ _<B_ p (a , b) →
    is-accessible (lexicographic _<A_ _<B_) p
  lexicographic-predecessors-are-accessible a smallerA b smallerB
    (a′ , b′) (inl a′<a) = smallerA a′ a′<a b′
  lexicographic-predecessors-are-accessible a smallerA b smallerB
    (.a , b′) (inr (refl , b′<b)) = smallerB b′ b′<b

  lexicographic-fiber-is-accessible : is-well-founded _<B_ → (a : A) →
    ((a′ : A) → a′ <A a → (b′ : B) →
      is-accessible (lexicographic _<A_ _<B_) (a′ , b′)) →
    (b : B) → is-accessible (lexicographic _<A_ _<B_) (a , b)
  lexicographic-fiber-is-accessible wfB a smallerA b =
    accessible-induction
      (λ b → is-accessible (lexicographic _<A_ _<B_) (a , b))
      (λ b smallerB →
        acc (lexicographic-predecessors-are-accessible a smallerA b
          smallerB))
      b (wfB b)

  lexicographic-is-well-founded : is-well-founded _<A_ →
    is-well-founded _<B_ → is-well-founded (lexicographic _<A_ _<B_)
  lexicographic-is-well-founded wfA wfB (a , b) =
    accessible-induction
      (λ a → (b : B) → is-accessible (lexicographic _<A_ _<B_) (a , b))
      (lexicographic-fiber-is-accessible wfB) a (wfA a) b

------------------------------------------------------------------------
-- Transitivity and well-foundedness on dependent pairs

module _ {ℓ κ μ ν : Level} {A : Set ℓ} (B : A → Set κ)
  (_<A_ : A → A → Set μ) (_<B_ : (a : A) → B a → B a → Set ν) where

  dependent-lexicographic-is-transitive :
    ({a b c : A} → a <A b → b <A c → a <A c) →
    ((a : A) {x y z : B a} → _<B_ a x y → _<B_ a y z → _<B_ a x z) →
    {p q r : Σ A B} →
    dependent-lexicographic B _<A_ _<B_ p q →
    dependent-lexicographic B _<A_ _<B_ q r →
    dependent-lexicographic B _<A_ _<B_ p r
  dependent-lexicographic-is-transitive transA transB
    (earlier a<b) (earlier b<c) = earlier (transA a<b b<c)
  dependent-lexicographic-is-transitive transA transB
    (earlier a<b) (within _ y<z) = earlier a<b
  dependent-lexicographic-is-transitive transA transB
    (within _ x<y) (earlier b<c) = earlier b<c
  dependent-lexicographic-is-transitive transA transB
    (within a x<y) (within .a y<z) = within a (transB a x<y y<z)

  dependent-lexicographic-predecessors-are-accessible : (a : A) →
    ((a′ : A) → a′ <A a → (b′ : B a′) →
      is-accessible (dependent-lexicographic B _<A_ _<B_) (a′ , b′)) →
    (b : B a) →
    ((b′ : B a) → _<B_ a b′ b →
      is-accessible (dependent-lexicographic B _<A_ _<B_) (a , b′)) →
    (p : Σ A B) → dependent-lexicographic B _<A_ _<B_ p (a , b) →
    is-accessible (dependent-lexicographic B _<A_ _<B_) p
  dependent-lexicographic-predecessors-are-accessible a smallerA b smallerB
    (a′ , b′) (earlier a′<a) = smallerA a′ a′<a b′
  dependent-lexicographic-predecessors-are-accessible a smallerA b smallerB
    (.a , b′) (within .a b′<b) = smallerB b′ b′<b

  dependent-lexicographic-fiber-is-accessible :
    ((a : A) → is-well-founded (_<B_ a)) → (a : A) →
    ((a′ : A) → a′ <A a → (b′ : B a′) →
      is-accessible (dependent-lexicographic B _<A_ _<B_) (a′ , b′)) →
    (b : B a) → is-accessible (dependent-lexicographic B _<A_ _<B_) (a , b)
  dependent-lexicographic-fiber-is-accessible wfB a smallerA b =
    accessible-induction
      (λ b → is-accessible (dependent-lexicographic B _<A_ _<B_) (a , b))
      (λ b smallerB →
        acc (dependent-lexicographic-predecessors-are-accessible a smallerA
          b smallerB))
      b (wfB a b)

  dependent-lexicographic-is-well-founded : is-well-founded _<A_ →
    ((a : A) → is-well-founded (_<B_ a)) →
    is-well-founded (dependent-lexicographic B _<A_ _<B_)
  dependent-lexicographic-is-well-founded wfA wfB (a , b) =
    accessible-induction
      (λ a → (b : B a) →
        is-accessible (dependent-lexicographic B _<A_ _<B_) (a , b))
      (dependent-lexicographic-fiber-is-accessible wfB) a (wfA a) b
