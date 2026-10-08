{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Presentation.Map where

-- Order embeddings and initial maps of presented ordinals, their comparison
-- laws, and proper principal segments with predecessor coverage.

open import Agda.Primitive using (Level)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (zero)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)

open import SPT.Cubical.Core.WellFounded using (Acc; acc)
import SPT.Cubical.OrdinalGeometry.Presentation.CountableOrdinal as Presented
open Presented using () renaming (CountableOrdinal𝒫 to 𝒫)
import SPT.Cubical.OrdinalGeometry.Presentation.Successor as Adjoin

-- An order embedding has no selected ceiling or predecessor-coverage law.
record Embedding {ℓ : Level} (P Q : 𝒫 ℓ) : Set ℓ where
  field
    map : 𝒫.X P → 𝒫.X Q
    resp : ∀ {x y} → 𝒫._≈_ P x y → 𝒫._≈_ Q (map x) (map y)
    strict : ∀ {x y} → 𝒫._<_ P x y → 𝒫._<_ Q (map x) (map y)

  reflect : ∀ {x y} → 𝒫._<_ Q (map x) (map y) → 𝒫._<_ P x y
  reflect {x} {y} p with 𝒫.compare P x y
  ... | inj₁ q = q
  ... | inj₂ (inj₁ q) = ⊥-elim (Presented.Presentation.≈↛< Q (resp q) p)
  ... | inj₂ (inj₂ q) =
    ⊥-elim (Presented.Presentation.<-asym Q p (strict q))

  reflect-≈ : ∀ {x y} → 𝒫._≈_ Q (map x) (map y) → 𝒫._≈_ P x y
  reflect-≈ {x} {y} p with 𝒫.compare P x y
  ... | inj₁ q = ⊥-elim (Presented.Presentation.≈↛< Q p (strict q))
  ... | inj₂ (inj₁ q) = q
  ... | inj₂ (inj₂ q) =
    ⊥-elim (Presented.Presentation.≈↛< Q (𝒫.≈-sym Q p) (strict q))

private
  ascending : ∀ {ℓ} {P : 𝒫 ℓ} (f : Embedding P P) (x : 𝒫.X P)
    → Acc (𝒫._<_ P) x → 𝒫._<_ P (Embedding.map f x) x → ⊥
  ascending f x (acc smaller) p = ascending f (Embedding.map f x)
    (smaller (Embedding.map f x) p) (Embedding.strict f p)

abstract
  nondecreasing : ∀ {ℓ} {P : 𝒫 ℓ} (f : Embedding P P) (x : 𝒫.X P)
    → 𝒫._<_ P (Embedding.map f x) x → ⊥
  nondecreasing {P = P} f x = ascending f x (𝒫.<-wf P x)

  no-reverse : ∀ {ℓ} {P Q : 𝒫 ℓ}
    → Embedding P Q → Q Presented.≺𝒫 P → ⊥
  no-reverse {Q = Q} f e = Presented.Embedding.irrefl Q record
    { to = λ x → Embedding.map f (Presented._≺𝒫_.to e x)
    ; to-≈ = λ p → Embedding.resp f (Presented._≺𝒫_.to-≈ e p)
    ; to-< = λ p → Embedding.strict f (Presented._≺𝒫_.to-< e p)
    ; reflects-< = λ p →
        Presented._≺𝒫_.reflects-< e (Embedding.reflect f p)
    ; ceiling = Embedding.map f (Presented._≺𝒫_.ceiling e)
    ; below = λ x → Embedding.strict f (Presented._≺𝒫_.below e x)
    }

-- Two order embeddings in turn.
composite : ∀ {ℓ} {P Q R : 𝒫 ℓ} → Embedding P Q → Embedding Q R
  → Embedding P R
composite f g = record
  { map = λ x → Embedding.map g (Embedding.map f x)
  ; resp = λ p → Embedding.resp g (Embedding.resp f p)
  ; strict = λ p → Embedding.strict g (Embedding.strict f p)
  }

-- An initial map retains a preimage, with its equivalence witness, for every
-- predecessor of every image point. Equivalence need not be raw identity.
-- No ceiling, image decision, or uniqueness of strict witnesses is required.
record Initial {ℓ : Level} (P Q : Presented.CountableOrdinal𝒫 ℓ) : Set ℓ where
  private
    module P = Presented.CountableOrdinal𝒫 P
    module Q = Presented.CountableOrdinal𝒫 Q
    module Laws = Presented.Presentation Q
  field
    map : P.X → Q.X
    resp : ∀ {x y} → x P.≈ y → map x Q.≈ map y
    strict : ∀ {x y} → x P.< y → map x Q.< map y
    lower : (x : P.X) (y : Q.X) → y Q.< map x
      → Σ P.X (λ z → map z Q.≈ y)

  reflect : ∀ {x y} → map x Q.< map y → x P.< y
  reflect {x} {y} p with P.compare x y
  ... | inj₁ q = q
  ... | inj₂ (inj₁ q) = ⊥-elim (Laws.≈↛< (resp q) p)
  ... | inj₂ (inj₂ q) = ⊥-elim (Laws.<-asym p (strict q))

  reflect-≈ : ∀ {x y} → map x Q.≈ map y → x P.≈ y
  reflect-≈ {x} {y} p with P.compare x y
  ... | inj₁ q = ⊥-elim (Laws.≈↛< p (strict q))
  ... | inj₂ (inj₁ q) = q
  ... | inj₂ (inj₂ q) = ⊥-elim (Laws.≈↛< (Q.≈-sym p) (strict q))

  -- Forgetting the lower law leaves an order embedding.
  embedding : Embedding P Q
  embedding = record { map = map ; resp = resp ; strict = strict }

identity : ∀ {ℓ} (P : Presented.CountableOrdinal𝒫 ℓ) → Initial P P
identity P = record
  { map = λ x → x ; resp = λ p → p ; strict = λ p → p
  ; lower = λ _ y _ → y , Presented.CountableOrdinal𝒫.≈-refl P y
  }

compose : ∀ {ℓ} {P Q R : Presented.CountableOrdinal𝒫 ℓ}
  → Initial P Q → Initial Q R → Initial P R
compose {Q = Q} {R = R} f g = record
  { map = λ x → G.map (F.map x)
  ; resp = λ p → G.resp (F.resp p)
  ; strict = λ p → G.strict (F.strict p)
  ; lower = lower
  }
  where
    module F = Initial f
    module G = Initial g
    module Q = Presented.CountableOrdinal𝒫 Q
    module R = Presented.CountableOrdinal𝒫 R

    lower : ∀ x z → z R.< G.map (F.map x)
      → Σ _ (λ y → G.map (F.map y) R.≈ z)
    lower x z p with G.lower (F.map x) z p
    ... | y , q with F.lower x y (G.reflect (R.<-respˡ-≈ (R.≈-sym q) p))
    ... | a , r = a , R.≈-trans (G.resp r) q

equivalence : ∀ {ℓ} {P Q : Presented.CountableOrdinal𝒫 ℓ}
  → P Presented.≃𝒫 Q → Initial P Q
equivalence e = record
  { map = E.to ; resp = E.to-≈ ; strict = E.to-<
  ; lower = λ _ y _ → E.from y , E.to-from-≈ y
  }
  where module E = Presented._≃𝒫_ e

bounded : ∀ {ℓ} {P Q R : Presented.CountableOrdinal𝒫 ℓ}
  → P Presented.≺𝒫 Q → Initial Q R → P Presented.≺𝒫 R
bounded e f = record
  { to = λ x → F.map (E.to x)
  ; to-≈ = λ p → F.resp (E.to-≈ p)
  ; to-< = λ p → F.strict (E.to-< p)
  ; reflects-< = λ p → E.reflects-< (F.reflect p)
  ; ceiling = F.map E.ceiling
  ; below = λ x → F.strict (E.below x)
  }
  where
    module E = Presented._≺𝒫_ e
    module F = Initial f

-- Initial maps have pointwise equivalent images. The witnesses remain
-- equivalences in Q; neither raw equality nor equality of maps is inferred.
module Uniqueness {ℓ : Level} {P Q : Presented.CountableOrdinal𝒫 ℓ}
  (f g : Initial P Q) where

  private
    module P = Presented.CountableOrdinal𝒫 P
    module Q = Presented.CountableOrdinal𝒫 Q
    module Laws = Presented.Presentation Q
    module F = Initial f
    module G = Initial g

    agree : (x : P.X) → Acc P._<_ x → F.map x Q.≈ G.map x
    agree x (acc smaller) with Q.compare (F.map x) (G.map x)
    ... | inj₂ (inj₁ q) = q
    ... | inj₁ p with G.lower x (F.map x) p
    ...   | y , q = ⊥-elim
      (Laws.≈↛< (Q.≈-trans (agree y (smaller y r)) q) (F.strict r))
      where
        r : y P.< x
        r = G.reflect (Q.<-respˡ-≈ (Q.≈-sym q) p)
    agree x (acc smaller) | inj₂ (inj₂ p) with F.lower x (G.map x) p
    ... | y , q = ⊥-elim
      (Laws.≈↛< (Q.≈-trans (Q.≈-sym (agree y (smaller y r))) q) (G.strict r))
      where
        r : y P.< x
        r = F.reflect (Q.<-respˡ-≈ (Q.≈-sym q) p)

  abstract
    pointwise : (x : P.X) → F.map x Q.≈ G.map x
    pointwise x = agree x (P.<-wf x)

antisymmetry : ∀ {ℓ} {P Q : Presented.CountableOrdinal𝒫 ℓ}
  → Initial P Q → Initial Q P → P Presented.≃𝒫 Q
antisymmetry {P = P} {Q = Q} f g = record
  { to = F.map ; from = G.map
  ; to-≈ = F.resp ; from-≈ = G.resp
  ; to-< = F.strict ; from-< = G.strict
  ; from-to-≈ = Uniqueness.pointwise (compose f g) (identity P)
  ; to-from-≈ = Uniqueness.pointwise (compose g f) (identity Q)
  }
  where
    module F = Initial f
    module G = Initial g

-- An initial map with an order embedding in the opposite direction is onto.
-- Comparing x with f(g(x)) gives a preimage; a strict decrease is impossible.
abstract
  surjective : ∀ {ℓ} {P Q : 𝒫 ℓ}
    → (f : Initial P Q) → Embedding Q P → (x : 𝒫.X Q)
    → Σ (𝒫.X P) (λ y → 𝒫._≈_ Q (Initial.map f y) x)
  surjective {Q = Q} f g x
    with 𝒫.compare Q x (Initial.map f (Embedding.map g x))
  ... | inj₁ p = Initial.lower f (Embedding.map g x) x p
  ... | inj₂ (inj₁ p) = Embedding.map g x , 𝒫.≈-sym Q p
  ... | inj₂ (inj₂ p) = ⊥-elim (nondecreasing self x p)
    where
    self : Embedding Q Q
    self = record
      { map = λ y → Initial.map f (Embedding.map g y)
      ; resp = λ {x} {y} q → Initial.resp f (Embedding.resp g {x} {y} q)
      ; strict = λ {x} {y} q →
          Initial.strict f (Embedding.strict g {x} {y} q)
      }

  onto : ∀ {ℓ} {P Q : 𝒫 ℓ} (f : Initial P Q)
    → ((x : 𝒫.X Q) → Σ (𝒫.X P) (λ y → 𝒫._≈_ Q (Initial.map f y) x))
    → P Presented.≃𝒫 Q
  onto {P = P} {Q = Q} f covers = record
    { to = Initial.map f ; from = λ x → proj₁ (covers x)
    ; to-≈ = Initial.resp f
    ; from-≈ = λ {x} {y} p → Initial.reflect-≈ f
        (𝒫.≈-trans Q (proj₂ (covers x))
          (𝒫.≈-trans Q p (𝒫.≈-sym Q (proj₂ (covers y)))))
    ; to-< = Initial.strict f
    ; from-< = λ {x} {y} p → Initial.reflect f
        (𝒫.<-respʳ-≈ Q (𝒫.≈-sym Q (proj₂ (covers y)))
          (𝒫.<-respˡ-≈ Q (𝒫.≈-sym Q (proj₂ (covers x))) p))
    ; from-to-≈ = λ x → Initial.reflect-≈ f
        (proj₂ (covers (Initial.map f x)))
    ; to-from-≈ = λ x → proj₂ (covers x)
    }

  onto-β : ∀ {ℓ} {P Q : 𝒫 ℓ} (f : Initial P Q)
    → (covers : (x : 𝒫.X Q)
        → Σ (𝒫.X P) (λ y → 𝒫._≈_ Q (Initial.map f y) x))
    → (x : 𝒫.X P)
    → 𝒫._≈_ Q (Presented._≃𝒫_.to (onto f covers) x) (Initial.map f x)
  onto-β {Q = Q} f covers x = 𝒫.≈-refl Q (Initial.map f x)

  isomorphism : ∀ {ℓ} {P Q : 𝒫 ℓ}
    → Initial P Q → Embedding Q P → P Presented.≃𝒫 Q
  isomorphism f g = onto f (surjective f g)

module Successor {ℓ : Level} (P : Presented.CountableOrdinal𝒫 ℓ) where

  private
    module P = Presented.CountableOrdinal𝒫 P
    module S = Presented.Diagonal.Successor (Adjoin.constant P) zero

  next : Presented.CountableOrdinal𝒫 ℓ
  next = Adjoin.successor P

  initial : Initial P next
  initial = record
    { map = S.point ; resp = S.point≈ ; strict = S.point<
    ; lower = λ { x (S.point y) (S.point< p) → y , S.point≈ (P.≈-refl y) }
    }

  strict : P Presented.≺𝒫 next
  strict = record
    { to = S.point ; to-≈ = S.point≈ ; to-< = S.point<
    ; reflects-< = λ { (S.point< p) → p }
    ; ceiling = S.top ; below = λ _ → S.point<top
    }

  module Into (Q : Presented.CountableOrdinal𝒫 ℓ) (e : P Presented.≺𝒫 Q)
    (covers : (y : Presented.CountableOrdinal𝒫.X Q)
      → Presented.CountableOrdinal𝒫._<_ Q y (Presented._≺𝒫_.ceiling e)
      → Σ P.X (λ x →
          Presented.CountableOrdinal𝒫._≈_ Q (Presented._≺𝒫_.to e x) y))
    where

    private
      module Q = Presented.CountableOrdinal𝒫 Q
      module E = Presented._≺𝒫_ e

    map : S.Entry → Q.X
    map (S.point x) = E.to x
    map S.top = E.ceiling

    closed : Initial next Q
    closed = record
      { map = map
      ; resp = λ where
          (S.point≈ p) → E.to-≈ p
          S.top≈ → Q.≈-refl E.ceiling
      ; strict = λ where
          (S.point< p) → E.to-< p
          S.point<top → E.below _
      ; lower = lower
      }
      where
        lower : (x : S.Entry) (y : Q.X) → y Q.< map x
          → Σ S.Entry (λ z → map z Q.≈ y)
        lower (S.point x) y p with covers y (Q.<-trans p (E.below x))
        ... | z , q = S.point z , q
        lower S.top y p with covers y p
        ... | z , q = S.point z , q

-- A principal strict bound covers the whole domain below its selected
-- ceiling. That extra coverage, absent from a bounded embedding alone,
-- extends its map to an initial map on the successor domain.
record Segment {ℓ : Level} (P Q : Presented.CountableOrdinal𝒫 ℓ) : Set ℓ where
  private
    module P = Presented.CountableOrdinal𝒫 P
    module Q = Presented.CountableOrdinal𝒫 Q
  field
    bound : P Presented.≺𝒫 Q

  private
    module B = Presented._≺𝒫_ bound
  field
    covers : (y : Q.X) → y Q.< B.ceiling → Σ P.X (λ x → B.to x Q.≈ y)

  closed : Initial (Successor.next P) Q
  closed = Successor.Into.closed P Q bound covers

inclusion : ∀ {ℓ} {P Q : 𝒫 ℓ} → Segment P Q → Initial P Q
inclusion {Q = Q} s = record
  { map = Presented._≺𝒫_.to (Segment.bound s)
  ; resp = Presented._≺𝒫_.to-≈ (Segment.bound s)
  ; strict = Presented._≺𝒫_.to-< (Segment.bound s)
  ; lower = λ x y p → Segment.covers s y
      (𝒫.<-trans Q p (Presented._≺𝒫_.below (Segment.bound s) x))
  }

successor : ∀ {ℓ} (P : Presented.CountableOrdinal𝒫 ℓ)
  → Segment P (Successor.next P)
successor P = record
  { bound = Successor.strict P
  ; covers = λ { (S.point x) S.point<top →
      x , S.point≈ (Presented.CountableOrdinal𝒫.≈-refl P x) }
  }
  where module S = Presented.Diagonal.Successor (Adjoin.constant P) zero

along : ∀ {ℓ} {P Q R : Presented.CountableOrdinal𝒫 ℓ}
  → Segment P Q → Initial Q R → Segment P R
along {Q = Q} {R = R} e f = record
  { bound = bounded E.bound f ; covers = cover }
  where
    module E = Segment e
    module B = Presented._≺𝒫_ E.bound
    module F = Initial f
    module Q = Presented.CountableOrdinal𝒫 Q
    module R = Presented.CountableOrdinal𝒫 R

    cover : (y : R.X) → y R.< F.map B.ceiling
      → Σ _ (λ x → F.map (B.to x) R.≈ y)
    cover y p with F.lower B.ceiling y p
    ... | z , q with E.covers z (F.reflect (R.<-respˡ-≈ (R.≈-sym q) p))
    ... | x , r = x , R.≈-trans (F.resp r) q
