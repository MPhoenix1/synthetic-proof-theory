{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.ExactOrder.Exponential.Embedding where

-- Proper initial-segment embeddings of exact countable orders, retaining
-- their cut and point coverage. Exponentiation preserves them: a segment
-- P → Q maps every exponent of a finite support, giving a segment
-- ω^P → ω^Q whose cut is the principal support at the cut of P.

open import Agda.Primitive using (Level; lsuc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; sym; subst)

import SPT.Cubical.OrdinalGeometry.ExactOrder.Base as Order
import SPT.Cubical.OrdinalGeometry.ExactOrder.Exponential.Order as Exponential
import SPT.Cubical.OrdinalGeometry.ExactOrder.Exponential.Boundary as Boundary

-- A proper initial-segment embedding retains its actual cut and point
-- coverage. Coverage recovers endpoints; it does not identify arbitrary
-- witnesses of the target relation.
record Segment {ℓ : Level} {A B : Set ℓ}
  (P : Order.Order A) (Q : Order.Order B) : Set (lsuc ℓ) where
  module P = Order.Order P
  module Q = Order.Order Q
  field
    embed : A → B
    cut : B
    below : (a : A) → embed a Q.< cut
    preserve : ∀ {a b} → a P.< b → embed a Q.< embed b
    cover : (b : B) → b Q.< cut → Σ A (λ a → embed a ≡ b)

  reflect : ∀ {a b} → embed a Q.< embed b → a P.< b
  reflect {a} {b} q with P.compare a b
  ... | inj₁ p = p
  ... | inj₂ (inj₁ refl) = ⊥-elim (Q.irrefl (embed a) q)
  ... | inj₂ (inj₂ p) = ⊥-elim (Q.irrefl (embed a) (Q.trans q (preserve p)))

  proper : (a : A) → embed a ≡ cut → ⊥
  proper a q = Q.irrefl cut (subst (λ b → b Q.< cut) q (below a))

-- Exponentiation preserves a supplied proper initial-segment embedding.
-- Every exponent of a support below the new principal cut is returned using
-- the original coverage theorem; the complete support is then reconstructed.
module Along {A B : Set} {P : Order.Order A} {Q : Order.Order B}
  (e : Segment P Q) where

  module E = Segment e
  module Source = Exponential.Power P
  module Target = Exponential.Power Q
  module SourceSupports = Source.Supports
  module TargetSupports = Target.Supports
  module Cut = Boundary.Power Q

  raw : SourceSupports.Raw → TargetSupports.Raw
  raw [] = []
  raw ((a , n) ∷ xs) = (E.embed a , n) ∷ raw xs

  private
    valid : (xs : SourceSupports.Raw) → SourceSupports.Valid xs
      → TargetSupports.Valid (raw xs)
    valid [] tt = tt
    valid (_ ∷ []) tt = tt
    valid (_ ∷ ys@(_ ∷ _)) (p , q) =
      TargetSupports.complete (E.preserve (SourceSupports.sound p)) , valid ys q

    reflected : (xs : SourceSupports.Raw) → TargetSupports.Valid (raw xs)
      → SourceSupports.Valid xs
    reflected [] tt = tt
    reflected (_ ∷ []) tt = tt
    reflected (_ ∷ ys@(_ ∷ _)) (p , q) =
      SourceSupports.complete (E.reflect (TargetSupports.sound p))
      , reflected ys q

  embed : SourceSupports.Term → TargetSupports.Term
  embed (xs , q) = raw xs , valid xs q

  private
    pair : ∀ {a b m n} → (a , m) SourceSupports.Pair.< (b , n)
      → (E.embed a , m) TargetSupports.Pair.< (E.embed b , n)
    pair (SourceSupports.Pair.earlier p) =
      TargetSupports.Pair.earlier (E.preserve p)
    pair (SourceSupports.Pair.within a p) =
      TargetSupports.Pair.within (E.embed a) p

    comparison : ∀ {xs ys} → xs SourceSupports.≺ ys
      → raw xs TargetSupports.≺ raw ys
    comparison SourceSupports.empty = TargetSupports.empty
    comparison (SourceSupports.head p) = TargetSupports.head (pair p)
    comparison (SourceSupports.tail p) = TargetSupports.tail (comparison p)

  preserve : ∀ {x y} → x SourceSupports.< y → embed x TargetSupports.< embed y
  preserve = comparison

  cut : TargetSupports.Term
  cut = Cut.principal E.cut

  below : (x : SourceSupports.Term) → embed x TargetSupports.< cut
  below ([] , tt) = TargetSupports.empty
  below (((a , n) ∷ xs) , q) =
    TargetSupports.head (TargetSupports.Pair.earlier (E.below a))

  private
    unmap : (xs : TargetSupports.Raw) → Cut.All E.cut xs
      → Σ SourceSupports.Raw (λ ys → raw ys ≡ xs)
    unmap [] tt = [] , refl
    unmap ((b , n) ∷ xs) (p , q) with E.cover b p | unmap xs q
    ... | a , refl | ys , r = (a , n) ∷ ys , cong ((E.embed a , n) ∷_) r

  cover : (x : TargetSupports.Term) → x TargetSupports.< cut
    → Σ SourceSupports.Term (λ y → embed y ≡ x)
  cover (xs , q) p with unmap xs
    (Cut.all E.cut (xs , q) (Cut.bound E.cut (xs , q) p))
  ... | ys , r =
    (ys , reflected ys (subst TargetSupports.Valid (sym r) q))
    , TargetSupports.equal r

  segment : Segment Source.order Target.order
  segment = record
    { embed = embed
    ; cut = cut
    ; below = below
    ; preserve = λ {x} {y} → preserve {x} {y}
    ; cover = cover
    }

  open Segment segment public using (reflect; proper)
