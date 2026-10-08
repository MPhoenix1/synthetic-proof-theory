{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Core.WellFounded.Lex where

-- Lexicographic orders on products and on dependent sums, and their
-- well-foundedness.

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)

open import SPT.Cubical.Core.WellFounded

------------------------------------------------------------------------
-- Binary coproduct / disjoint sum

infixr 20 _⊎_

data _⊎_ {ℓ ℓ' : Level}
         (A : Set ℓ)
         (B : Set ℓ')
         : Set (ℓ ⊔ ℓ') where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

------------------------------------------------------------------------
-- Lexicographic products of relations

LexRel :
  {ℓA ℓB ℓa ℓb : Level}
  {A : Set ℓA}
  {B : Set ℓB} →
  (A → A → Set ℓa) →
  (B → B → Set ℓb) →
  Σ A (λ _ → B) →
  Σ A (λ _ → B) →
  Set (ℓA ⊔ ℓa ⊔ ℓb)
LexRel _<A_ _<B_ p q =
  (fst p <A fst q)
  ⊎
  (Σ (fst p ≡ fst q)
     (λ _ → snd p <B snd q))

lex-wf :
  {ℓA ℓB ℓa ℓb : Level}
  {A : Set ℓA}
  {B : Set ℓB}
  {_<A_ : A → A → Set ℓa}
  {_<B_ : B → B → Set ℓb} →
  WellFounded _<A_ →
  WellFounded _<B_ →
  WellFounded (LexRel _<A_ _<B_)
lex-wf {A = A} {B = B} {_<A_ = _<A_} {_<B_ = _<B_} wfA wfB (a , b) =
  acc-ind {_<_ = _<A_}
    (λ a → (b : B) → Acc (LexRel _<A_ _<B_) (a , b))
    stepA
    a
    (wfA a)
    b
  where
    stepB :
      (a : A) →
      ((a' : A) → a' <A a → (b' : B) →
        Acc (LexRel _<A_ _<B_) (a' , b')) →
      (b : B) →
      ((b' : B) → b' <B b →
        Acc (LexRel _<A_ _<B_) (a , b')) →
      Acc (LexRel _<A_ _<B_) (a , b)
    stepB a smallerA b smallerB =
      acc λ
        { (a' , b') (inj₁ a'<a) →
            smallerA a' a'<a b'
        ; (.a , b') (inj₂ (refl , b'<b)) →
            smallerB b' b'<b
        }

    stepA :
      (a : A) →
      ((a' : A) → a' <A a → (b' : B) →
        Acc (LexRel _<A_ _<B_) (a' , b')) →
      (b : B) →
      Acc (LexRel _<A_ _<B_) (a , b)
    stepA a smallerA b =
      acc-ind {_<_ = _<B_}
        (λ b → Acc (LexRel _<A_ _<B_) (a , b))
        (stepB a smallerA)
        b
        (wfB b)


------------------------------------------------------------------------
-- Dependent lexicographic totals

module Dependent
    {ℓA ℓB ℓa ℓb : Level}
    {A : Set ℓA}
    (B : A → Set ℓB)
    (_<A_ : A → A → Set ℓa)
    (_<B_ : (a : A) → B a → B a → Set ℓb)
  where

  -- The lexicographic order on Σ A B, as an inductive family:
  --
  --     a <A a′                      x <B[a] y
  --   ---------------- earlier     ---------------- within
  --   (a,x) < (a′,y)                 (a,x) < (a,y)
  --
  -- A step within one fiber shares its first component outright, so no
  -- transport along an equality of first components is needed.

  infix 4 _<_

  data _<_
      : Σ A B
      → Σ A B
      → Set (ℓA ⊔ ℓB ⊔ ℓa ⊔ ℓb)
    where

    earlier :
        ∀ {a a′}
          {x : B a}
          {y : B a′}
      → a <A a′
      → (a , x) < (a′ , y)

    within :
        (a : A)
        {x y : B a}
      → _<B_ a x y
      → (a , x) < (a , y)

  trans :
      (∀ {a b c}
        → a <A b
        → b <A c
        → a <A c)
    → ((a : A)
        → ∀ {x y z}
        → _<B_ a x y
        → _<B_ a y z
        → _<B_ a x z)
    → ∀ {x y z}
    → x < y
    → y < z
    → x < z
  trans transA transB
      (earlier a<b) (earlier b<c) =
    earlier (transA a<b b<c)
  trans transA transB
      (earlier a<b) (within _ y<z) =
    earlier a<b
  trans transA transB
      (within _ x<y) (earlier b<c) =
    earlier b<c
  trans transA transB
      (within a x<y) (within .a y<z) =
    within a (transB a x<y y<z)

  wf :
      WellFounded _<A_
    → ((a : A) → WellFounded (_<B_ a))
    → WellFounded _<_
  wf wfA wfB (a , b) =
    acc-ind
      (λ a →
        (b : B a) →
        Acc _<_ (a , b))
      outer
      a
      (wfA a)
      b
    where
      inner :
          (a : A)
        → ((a′ : A)
            → a′ <A a
            → (b′ : B a′)
            → Acc _<_ (a′ , b′))
        → (b : B a)
        → ((b′ : B a)
            → _<B_ a b′ b
            → Acc _<_ (a , b′))
        → Acc _<_ (a , b)
      inner a smallerA b smallerB =
        acc λ where
          (a′ , b′) (earlier a′<a) →
            smallerA a′ a′<a b′
          (.a , b′) (within .a b′<b) →
            smallerB b′ b′<b

      outer :
          (a : A)
        → ((a′ : A)
            → a′ <A a
            → (b′ : B a′)
            → Acc _<_ (a′ , b′))
        → (b : B a)
        → Acc _<_ (a , b)
      outer a smallerA b =
        acc-ind
          (λ b → Acc _<_ (a , b))
          (inner a smallerA)
          b
          (wfB a b)
