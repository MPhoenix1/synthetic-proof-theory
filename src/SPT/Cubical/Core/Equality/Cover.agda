{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Core.Equality.Cover where

-- Predicative proposition-only existence: CoveredAt r A says that A is
-- inhabited as far as r-small propositions can tell.  Covers of maps,
-- descent of proposition-valued families along a cover, and the structural
-- laws of covers.

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Product using (Σ; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; subst; sym; trans)

open import SPT.Cubical.Core.Equality using (IsProposition; DependentΠExt)
open import SPT.Cubical.Core.Equality.Fiber using (HomotopyFiber)

private
  variable
    ℓa ℓb ℓc ℓx ℓr : Level
    A : Set ℓa
    B : Set ℓb
    C : Set ℓc
    X : Set ℓx

------------------------------------------------------------------------
-- Fibers

-- Fiber(q,x) = Σ(c : C). q(c) ≡ x, the homotopy fiber.
Fiber :
    ∀ {ℓc ℓx : Level}
      {C : Set ℓc}
      {X : Set ℓx}
  → (C → X)
  → X
  → Set (ℓc ⊔ ℓx)
Fiber = HomotopyFiber

------------------------------------------------------------------------
-- Proposition-only existence

-- The Church encoding of existence, restricted to r-small propositions:
--
--   CoveredAt(r,A) = Π(P : Set r). IsProposition(P) → (A → P) → P.
--
-- A is an arbitrary type.  A point of A gives an inhabitant
-- (`pointCovered`), and an inhabitant can be used only to prove an r-small
-- proposition; `extractProposition` returns a point when A is itself one.
-- CoveredAt is a proposition only under extensionality (WithΠExt).
CoveredAt :
    ∀ {ℓa : Level}
  → (ℓr : Level)
  → Set ℓa
  → Set (ℓa ⊔ lsuc ℓr)
CoveredAt ℓr A =
  (P : Set ℓr) →
  IsProposition P →
  (A → P) →
  P

-- Given extensionality for the three function spaces in its definition,
-- CoveredAt r A is a proposition, for every type A.
module WithΠExt
    {ℓr ℓa : Level}
    {A : Set ℓa}
    (types : DependentΠExt (Set ℓr)
      (λ R → IsProposition R → (A → R) → R))
    (proofs : (R : Set ℓr) → DependentΠExt (IsProposition R)
      (λ _ → (A → R) → R))
    (maps : (R : Set ℓr) → DependentΠExt (A → R) (λ _ → R))
  where

  unique : IsProposition (CoveredAt ℓr A)
  unique left right =
    types left right λ R →
      proofs R (left R) (right R) λ unique-R →
        maps R (left R unique-R) (right R unique-R) λ consequence →
          unique-R (left R unique-R consequence) (right R unique-R consequence)


pointCovered :
    ∀ {ℓa ℓr : Level} {A : Set ℓa}
  → A
  → CoveredAt ℓr A
pointCovered a P proposition consequence =
  consequence a

mapCovered :
    ∀ {ℓa ℓb ℓr : Level}
      {A : Set ℓa} {B : Set ℓb}
  → (A → B)
  → CoveredAt ℓr A
  → CoveredAt ℓr B
mapCovered map inhabitance P proposition consequence =
  inhabitance P proposition (λ a → consequence (map a))

bindCovered :
    ∀ {ℓa ℓb ℓr : Level}
      {A : Set ℓa} {B : Set ℓb}
  → CoveredAt ℓr A
  → (A → CoveredAt ℓr B)
  → CoveredAt ℓr B
bindCovered inhabitance next P proposition consequence =
  inhabitance P proposition
    (λ a → next a P proposition consequence)

extractProposition :
    ∀ {ℓr : Level} {P : Set ℓr}
  → CoveredAt ℓr P
  → IsProposition P
  → P
extractProposition {P = P} inhabitance proposition =
  inhabitance P proposition (λ p → p)

covered-agrees :
    ∀ {ℓa ℓr : Level} {A : Set ℓa}
  → (inhabitance : CoveredAt ℓr A)
  → (a : A)
  → (P : Set ℓr)
  → (proposition : IsProposition P)
  → (consequence : A → P)
  → inhabitance P proposition consequence ≡ consequence a
covered-agrees inhabitance a P proposition consequence =
  proposition (inhabitance P proposition consequence) (consequence a)

empty-isProposition :
    ∀ {ℓ : Level}
  → IsProposition (⊥ {ℓ})
empty-isProposition ()

covered-not-not :
    ∀ {ℓa ℓr : Level} {A : Set ℓa}
  → CoveredAt ℓr A
  → (A → ⊥ {ℓr})
  → ⊥ {ℓr}
covered-not-not inhabitance refute =
  inhabitance ⊥ empty-isProposition refute

------------------------------------------------------------------------
-- Covers

-- A cover of q: every fiber of q is covered.
--
--   CoverAt(r,q) = Π(x : X). CoveredAt(r,Fiber(q,x)).
--
-- A cover does not say which fiber point covers x.  It is eliminated by
-- `descend` into proposition-valued families; a fiber point is recovered
-- only when the fibers are propositions (`propositionFibersSplit`).
CoverAt :
    ∀ {ℓc ℓx : Level}
  → (ℓr : Level)
  → {C : Set ℓc}
  → {X : Set ℓx}
  → (C → X)
  → Set (ℓc ⊔ ℓx ⊔ lsuc ℓr)
CoverAt ℓr {X = X} q =
  (x : X) → CoveredAt ℓr (Fiber q x)

-- A split cover chooses a point in every fiber:
--
--   SplitCover(q) = Π(x : X). Fiber(q,x).
--
-- `splitToCover` forgets the choices.  The converse is proved only for
-- proposition-valued fibers.
SplitCover :
    ∀ {ℓc ℓx : Level}
      {C : Set ℓc}
      {X : Set ℓx}
  → (C → X)
  → Set (ℓc ⊔ ℓx)
SplitCover {X = X} q =
  (x : X) → Fiber q x

splitToCover :
    ∀ {ℓc ℓx ℓr : Level}
      {C : Set ℓc} {X : Set ℓx}
      {q : C → X}
  → SplitCover q
  → CoverAt ℓr q
splitToCover split x P proposition consequence =
  consequence (split x)

propositionFibersSplit :
    ∀ {ℓc ℓx : Level}
      {C : Set ℓc} {X : Set ℓx}
      {q : C → X}
  → CoverAt (ℓc ⊔ ℓx) q
  → ((x : X) → IsProposition (Fiber q x))
  → SplitCover q
propositionFibersSplit cover fibers-proposition x =
  extractProposition (cover x) (fibers-proposition x)

fiber-not-not :
    ∀ {ℓc ℓx ℓr : Level}
      {C : Set ℓc} {X : Set ℓx}
      {q : C → X}
  → CoverAt ℓr q
  → (x : X)
  → (Fiber q x → ⊥ {ℓr})
  → ⊥ {ℓr}
fiber-not-not cover x =
  covered-not-not (cover x)

------------------------------------------------------------------------
-- Proposition-valued descent

-- Descent of a proposition-valued family along a cover:
--
--   CoverAt(r,q)    Π x. IsProposition(P(x))    Π(c : C). P(q(c))
--   ---------------------------------------------------------------
--                          Π(x : X). P(x)
--
-- Each fiber point transports its value along its path to x.  The two
-- comparisons with precomposition below are pointwise.
descend :
    ∀ {ℓc ℓx ℓr : Level}
      {C : Set ℓc} {X : Set ℓx}
      {q : C → X}
  → CoverAt ℓr q
  → (P : X → Set ℓr)
  → ((x : X) → IsProposition (P x))
  → ((c : C) → P (q c))
  → (x : X) → P x
descend cover P proposition section x =
  cover x (P x) (proposition x)
    (λ where
      (c , path) → subst P path (section c))

descend-on-occurrence :
    ∀ {ℓc ℓx ℓr : Level}
      {C : Set ℓc} {X : Set ℓx}
      {q : C → X}
  → (cover : CoverAt ℓr q)
  → (P : X → Set ℓr)
  → (proposition : (x : X) → IsProposition (P x))
  → (section : (c : C) → P (q c))
  → (c : C)
  → descend cover P proposition section (q c) ≡ section c
descend-on-occurrence {q = q} cover P proposition section c =
  proposition (q c)
    (descend cover P proposition section (q c))
    (section c)

descend-precomposed-pointwise :
    ∀ {ℓc ℓx ℓr : Level}
      {C : Set ℓc} {X : Set ℓx}
      {q : C → X}
  → (cover : CoverAt ℓr q)
  → (P : X → Set ℓr)
  → (proposition : (x : X) → IsProposition (P x))
  → (base : (x : X) → P x)
  → (x : X)
  → descend cover P proposition (λ c → base (q c)) x ≡ base x
descend-precomposed-pointwise {q = q} cover P proposition base x =
  proposition x
    (descend cover P proposition (λ c → base (q c)) x)
    (base x)

------------------------------------------------------------------------
-- Structural laws

identityCover :
    ∀ {ℓx ℓr : Level} {X : Set ℓx}
  → CoverAt ℓr (λ (x : X) → x)
identityCover x P proposition consequence =
  consequence (x , refl)

composeCover :
    ∀ {ℓa ℓb ℓc ℓr : Level}
      {A : Set ℓa} {B : Set ℓb} {C : Set ℓc}
      {f : A → B} {g : B → C}
  → CoverAt ℓr f
  → CoverAt ℓr g
  → CoverAt ℓr (λ a → g (f a))
composeCover {g = g} first second c P proposition consequence =
  second c P proposition
    (λ where
      (b , path) →
        first b P proposition
          (λ where
            (a , first-path) →
              consequence
                (a , trans (cong g first-path) path)))

-- The pullback of q along f, Pullback(q,f) = Σ(b : B). Fiber(q,f(b)).
-- The projection to B is covered whenever q is (`pullbackCover`).
Pullback :
    ∀ {ℓa ℓb ℓc : Level}
      {A : Set ℓa} {B : Set ℓb} {C : Set ℓc}
  → (A → C)
  → (B → C)
  → Set (ℓa ⊔ ℓb ⊔ ℓc)
Pullback {A = A} {B = B} q f =
  Σ B (λ b → Fiber q (f b))

pullbackBase :
    ∀ {ℓa ℓb ℓc : Level}
      {A : Set ℓa} {B : Set ℓb} {C : Set ℓc}
  → (q : A → C)
  → (f : B → C)
  → Pullback q f
  → B
pullbackBase q f =
  proj₁

pullbackCover :
    ∀ {ℓa ℓb ℓc ℓr : Level}
      {A : Set ℓa} {B : Set ℓb} {C : Set ℓc}
      {q : A → C}
  → CoverAt ℓr q
  → (f : B → C)
  → CoverAt ℓr (pullbackBase q f)
pullbackCover cover f b P proposition consequence =
  cover (f b) P proposition
    (λ where
      (a , path) → consequence ((b , (a , path)) , refl))

respectCover :
    ∀ {ℓa ℓb ℓr : Level}
      {A : Set ℓa} {B : Set ℓb}
      {f g : A → B}
  → ((a : A) → f a ≡ g a)
  → CoverAt ℓr f
  → CoverAt ℓr g
respectCover pointwise cover b P proposition consequence =
  cover b P proposition
    (λ where
      (a , path) →
        consequence (a , trans (sym (pointwise a)) path))
