{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.ExactOrder.Maps where

-- Embeddings, initial maps and order isomorphisms of exact orders.  An
-- order isomorphism stores an isomorphism of carriers A ≅ B
-- (Core.Equality.Isomorphism) whose forward map is strictly monotone;
-- `from-inverses` builds the carrier isomorphism from maps with pointwise
-- inverse laws.

open import Agda.Primitive using (Level; lsuc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; sym; trans; subst; subst₂)

open import SPT.Cubical.Core.WellFounded using (Acc; acc)
open import SPT.Cubical.Core.Equality using (MapΠExt)
open import SPT.Cubical.Core.Equality.Isomorphism using (_≅_)
import SPT.Cubical.OrdinalGeometry.ExactOrder.Base as Order
open import SPT.Cubical.OrdinalGeometry.ExactOrder.Exponential.Embedding
  using (Segment)

from-inverses : ∀ {ℓ κ} {A : Set ℓ} {B : Set κ}
  → (f : A → B) → (g : B → A)
  → ((x : A) → g (f x) ≡ x) → ((y : B) → f (g y) ≡ y)
  → A ≅ B
from-inverses f g η ε = record
  { forward = f
  ; backward = g
  ; backward-forward = η
  ; forward-backward = ε
  }

module Strict {ℓ : Level} {A B : Set ℓ}
  (P : Order.Order A) (Q : Order.Order B) (f : A → B)
  (strict : ∀ {x y}
    → Order.Order._<_ P x y → Order.Order._<_ Q (f x) (f y)) where

  module P = Order.Order P
  module Q = Order.Order Q

  reflect : ∀ {x y} → f x Q.< f y → x P.< y
  reflect {x} {y} q with P.compare x y
  ... | inj₁ p = p
  ... | inj₂ (inj₁ refl) = ⊥-elim (Q.irrefl (f x) q)
  ... | inj₂ (inj₂ p) = ⊥-elim (Q.irrefl (f x) (Q.trans q (strict p)))

  injective : ∀ {x y} → f x ≡ f y → x ≡ y
  injective {x} {y} q with P.compare x y
  ... | inj₁ p = ⊥-elim (Q.irrefl (f y) (subst (λ b → b Q.< f y) q (strict p)))
  ... | inj₂ (inj₁ p) = p
  ... | inj₂ (inj₂ p) =
    ⊥-elim (Q.irrefl (f y) (subst (Q._<_ (f y)) q (strict p)))

  module Onto (covers : (y : B) → Σ A (λ x → f x ≡ y)) where

    -- A strictly monotone surjection is an isomorphism of carriers: its
    -- inverse picks the covering point, and injectivity gives the laws.
    exact : A ≅ B
    exact = record
      { forward = f
      ; backward = λ y → proj₁ (covers y)
      ; backward-forward = λ x → injective (proj₂ (covers (f x)))
      ; forward-backward = λ y → proj₂ (covers y)
      }

-- A strictly increasing map of exact orders. It need not be initial: its
-- image may skip points, so it records no predecessor coverage or ceiling.
record Embedding {ℓ : Level} {A B : Set ℓ}
  (P : Order.Order A) (Q : Order.Order B) : Set ℓ where
  module P = Order.Order P
  module Q = Order.Order Q
  field
    map : A → B
    strict : ∀ {x y} → x P.< y → map x Q.< map y

  open Strict P Q map (λ {x} {y} → strict {x} {y}) public
    using (reflect; injective)

-- Initial maps include surjective maps. A Segment additionally specifies a
-- strict ceiling. Keeping these two kinds separate permits fixed boundaries
-- and their leastness to be stated without demanding a nonexistent ceiling.
record Initial {ℓ : Level} {A B : Set ℓ}
  (P : Order.Order A) (Q : Order.Order B) : Set (lsuc ℓ) where
  module P = Order.Order P
  module Q = Order.Order Q
  field
    map : A → B
    strict : ∀ {x y} → x P.< y → map x Q.< map y
    lower : (x : A) (b : B) → b Q.< map x → Σ A (λ y → map y ≡ b)

  open Strict P Q map (λ {x} {y} → strict {x} {y}) public
    using (reflect; injective)

  -- Forgetting the lower law leaves an embedding.
  embedding : Embedding P Q
  embedding = record { map = map ; strict = strict }

identity : ∀ {ℓ} {A : Set ℓ} (P : Order.Order A) → Initial P P
identity P = record
  { map = λ x → x ; strict = λ p → p ; lower = λ _ b _ → b , refl }

segment : ∀ {ℓ} {A B : Set ℓ} {P : Order.Order A} {Q : Order.Order B}
  → Segment P Q → Initial P Q
segment {Q = Q} e = record
  { map = S.embed ; strict = S.preserve
  ; lower = λ x b p → S.cover b (Order.Order.trans Q p (S.below x))
  }
  where module S = Segment e

compose : ∀ {ℓ} {A B C : Set ℓ}
  {P : Order.Order A} {Q : Order.Order B} {R : Order.Order C}
  → Initial P Q → Initial Q R → Initial P R
compose {R = R} f g = record
  { map = λ x → G.map (F.map x)
  ; strict = λ p → G.strict (F.strict p)
  ; lower = lower
  }
  where
  module F = Initial f
  module G = Initial g
  lower : ∀ x c → Order.Order._<_ R c (G.map (F.map x))
    → Σ _ (λ y → G.map (F.map y) ≡ c)
  lower x c p with G.lower (F.map x) c p
  ... | b , q with F.lower x b
    (G.reflect (subst (λ z → Order.Order._<_ R z (G.map (F.map x))) (sym q) p))
  ...   | a , r = a , trans (cong G.map r) q

record Iso {ℓ : Level} {A B : Set ℓ}
  (P : Order.Order A) (Q : Order.Order B) : Set (lsuc ℓ) where
  module P = Order.Order P
  module Q = Order.Order Q
  field
    equivalence : A ≅ B
    strict : ∀ {x y} → x P.< y
      → _≅_.forward equivalence x Q.< _≅_.forward equivalence y

  forward : A → B
  forward = _≅_.forward equivalence

  backward : B → A
  backward = _≅_.backward equivalence

  backward-forward : (x : A) → backward (forward x) ≡ x
  backward-forward = _≅_.backward-forward equivalence

  forward-backward : (y : B) → forward (backward y) ≡ y
  forward-backward = _≅_.forward-backward equivalence

  open Strict P Q forward (λ {x} {y} → strict {x} {y}) public
    using (reflect; injective)

  inverse-strict : ∀ {x y} → x Q.< y → backward x P.< backward y
  inverse-strict {x} {y} p = reflect
    (subst₂ Q._<_ (sym (forward-backward x)) (sym (forward-backward y)) p)

  initial : Initial P Q
  initial = record
    { map = forward ; strict = λ {x} {y} → strict {x} {y}
    ; lower = λ _ b _ → backward b , forward-backward b
    }

  inverse : Initial Q P
  inverse = record
    { map = backward ; strict = λ {x} {y} → inverse-strict {x} {y}
    ; lower = λ _ a _ → forward a , backward-forward a
    }

module Uniqueness {ℓ : Level} {A B : Set ℓ}
  {P : Order.Order A} {Q : Order.Order B} (f g : Initial P Q) where

  module P = Order.Order P
  module Q = Order.Order Q
  module F = Initial f
  module G = Initial g

  private
    agree : (x : A) → Acc P._<_ x → F.map x ≡ G.map x
    agree x (acc smaller) with Q.compare (F.map x) (G.map x)
    ... | inj₂ (inj₁ q) = q
    ... | inj₁ p with G.lower x (F.map x) p
    ...   | y , q = ⊥-elim (Q.irrefl (F.map x)
      (subst (λ b → b Q.< F.map x) (trans (agree y (smaller y r)) q)
        (F.strict r)))
      where
      r : y P.< x
      r = G.reflect (subst (λ b → b Q.< G.map x) (sym q) p)
    agree x (acc smaller) | inj₂ (inj₂ p) with F.lower x (G.map x) p
    ... | y , q = ⊥-elim (Q.irrefl (G.map x)
      (subst (λ b → b Q.< G.map x)
        (trans (sym (agree y (smaller y r))) q) (G.strict r)))
      where
      r : y P.< x
      r = F.reflect (subst (λ b → b Q.< F.map x) (sym q) p)

  abstract
    pointwise : (x : A) → F.map x ≡ G.map x
    pointwise x = agree x (P.wf x)

  module WithΠExt (ext : MapΠExt A B) where

    equality : F.map ≡ G.map
    equality = ext F.map G.map pointwise

no-self-segment : ∀ {ℓ} {A : Set ℓ} {P : Order.Order A} → Segment P P → ⊥
no-self-segment {P = P} e = Order.Order.irrefl P S.cut
  (subst (λ x → Order.Order._<_ P x S.cut)
    (Uniqueness.pointwise (segment e) (identity P) S.cut) (S.below S.cut))
  where module S = Segment e
