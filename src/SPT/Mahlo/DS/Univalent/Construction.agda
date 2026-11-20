{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Univalent.Construction where

-- Shulman's univalent universe of a type-valued description γ from an
-- algebra M of γ with codes at level κ, its law, unique names (each
-- Name value X a proposition) and a generation G, a closed family of
-- propositions at level κ (`universe`). The codes are the generated
-- points, decoded by value. Introduction is the
-- operation at the heads of an argument (`introduce`, `introduce-β`). An
-- identification of decodings is one of names, which unique names make
-- one of points (`names`, `names-β`, `identify`, `identify-β`). With G
-- least at κ ⊔ ν, elimination into level ν (`elimination`): the motive is
-- a family of propositions (Universe.forced), and induction runs through
-- leastness at the generated points where it holds (`holds`, `holding`,
-- `induction`).

open import SPT.Base
open import SPT.Foundation.Propositions using
  (is-proposition; propositions-are-sets; Σ-is-proposition)
import SPT.Mahlo.Specification as Specification

open import SPT.IR.Algebra using (Algebra; Law)
open import SPT.IR.Description using
  (Desc; indexed; Shape; Mark)
open import SPT.IR.Univalent.Generation using
  (Closed; Closed-Family; Least)
open import SPT.IR.Restriction using
  ( Position; input; heads; children; heads-β; join; heads-join
  ; position-join; input-join )
open import SPT.IR.Univalent.Universe using
  (Universe; Elimination; Method; Path-method; forced)

------------------------------------------------------------------------
-- Names

-- Two points with identified decodings are two names of one type; unique
-- names identify them, and the decoding carries that identification back
-- to the given one.

module _
  {ℓ κ : Level} {γ : Desc {s = ℓ} (Set ℓ)} (M : Algebra κ γ)
  (unique :
    (X : Set ℓ) → is-proposition (Specification.Name (Algebra.value M) X))
  where

  open Algebra M using (K; value)

  names : (k k′ : K) → value k ＝ value k′ → k ＝ k′
  names k k′ p = ap pr₁ (unique (value k′) (k , p) (k′ , refl))

  names-β :
    (k k′ : K) (p : value k ＝ value k′) → ap value (names k k′ p) ＝ p
  names-β k k′ p =
    trivial-difference (ap value (names k k′ p)) p
      ( transport-fiber value (names k k′ p) p ⁻¹
      ∙ from-Σ-＝-pr₂ (unique (value k′) (k , p) (k′ , refl)))

------------------------------------------------------------------------
-- The universe

-- The generated points, decoded through K. Their identifications are
-- those of K, the generation being a family of propositions.

module _
  {ℓ κ : Level} {γ : Desc {s = ℓ} (Set ℓ)} (M : Algebra κ γ) (law : Law M)
  (unique :
    (X : Set ℓ) → is-proposition (Specification.Name (Algebra.value M) X))
  (G : Closed-Family M κ)
  where

  open Algebra M using (K; value; operation)
  open Closed-Family G using (family; proposition; closed)

  introduce :
    Shape γ (indexed (Σ K family) (λ w → value (pr₁ w))) → Σ K family
  introduce z =
    operation (heads value family γ z) ,
    closed (heads value family γ z) (children value family γ z)

  introduce-β :
    (z : Shape γ (indexed (Σ K family) (λ w → value (pr₁ w))))
    → value (pr₁ (introduce z))
      ＝ Mark γ (indexed (Σ K family) (λ w → value (pr₁ w))) z
  introduce-β z =
    law (heads value family γ z) ∙ heads-β value family γ z

  identify :
    (a b : Σ K family) → value (pr₁ a) ＝ value (pr₁ b) → a ＝ b
  identify a b p =
    to-Σ-＝ (names M unique (pr₁ a) (pr₁ b) p)
      (proposition (pr₁ b)
        (transport family (names M unique (pr₁ a) (pr₁ b) p) (pr₂ a))
        (pr₂ b))

  identify-β :
    (a b : Σ K family) (p : value (pr₁ a) ＝ value (pr₁ b))
    → ap (λ w → value (pr₁ w)) (identify a b p) ＝ p
  identify-β a b p =
    ap-∘ pr₁ value (identify a b p)
    ∙ ap (ap value)
        (ap-pr₁-to-Σ-＝ (names M unique (pr₁ a) (pr₁ b) p)
          (proposition (pr₁ b)
            (transport family (names M unique (pr₁ a) (pr₁ b) p)
              (pr₂ a))
            (pr₂ b)))
    ∙ names-β M unique (pr₁ a) (pr₁ b) p

  universe : Universe κ γ
  universe = record
    { Code = Σ K family
    ; El = λ w → value (pr₁ w)
    ; intro = introduce
    ; intro-β = introduce-β
    ; ua = identify
    ; ua-β = identify-β
    }

------------------------------------------------------------------------
-- Elimination

-- For a family P of propositions over the codes, the points of K that
-- are generated with P holding there form a closed family of
-- propositions: at an operation, join the generated inputs into an
-- argument over the codes, apply the method, and move along the heads of
-- the join. Leastness puts every generated point in it.

  holds : {ν : Level} → (Σ K family → Set ν) → K → Set (κ ⊔ ν)
  holds P k = Σ (family k) (λ g → P (k , g))

  holds-proposition :
    {ν : Level} (P : Σ K family → Set ν)
    → ((w : Σ K family) → is-proposition (P w))
    → (k : K) → is-proposition (holds P k)
  holds-proposition P h k =
    Σ-is-proposition (proposition k) (λ g → h (k , g))

  holds-closed :
    {ν : Level} (P : Σ K family → Set ν)
    → ((w : Σ K family) → is-proposition (P w)) → Method universe P
    → Closed M (holds P)
  holds-closed P h m a hs =
    closed a (λ p → pr₁ (hs p)) ,
    transport P
      (to-Σ-＝ {B = family}
        (ap operation
          (heads-join value family γ (a , (λ p → pr₁ (hs p)))))
        (proposition (operation a)
          (transport family
            (ap operation
              (heads-join value family γ (a , (λ p → pr₁ (hs p)))))
            (closed
              (heads value family γ
                (join value family γ (a , (λ p → pr₁ (hs p)))))
              (children value family γ
                (join value family γ (a , (λ p → pr₁ (hs p)))))))
          (closed a (λ p → pr₁ (hs p)))))
      (m (join value family γ (a , (λ p → pr₁ (hs p))))
        (λ p →
          transport P
            (input-join value family γ (a , (λ p′ → pr₁ (hs p′))) p ⁻¹)
            (pr₂
              (hs
                (position-join value family γ (a , (λ p′ → pr₁ (hs p′)))
                  p)))))

  holding :
    {ν : Level} (P : Σ K family → Set ν)
    → ((w : Σ K family) → is-proposition (P w)) → Method universe P
    → Closed-Family M (κ ⊔ ν)
  holding P h m = record
    { family = holds P
    ; proposition = holds-proposition P h
    ; closed = holds-closed P h m
    }

  induction :
    {ν : Level} → Least M G (κ ⊔ ν) → (P : Σ K family → Set ν)
    → ((w : Σ K family) → is-proposition (P w)) → Method universe P
    → (w : Σ K family) → P w
  induction least P h m (k , g) =
    let w = least (holding P h m) k g
    in transport (λ g′ → P (k , g′)) (proposition k (pr₁ w) g) (pr₂ w)

  -- The eliminator: induction, the motive being forced propositional.
  eliminate :
    {ν : Level} → Least M G (κ ⊔ ν) → (P : Σ K family → Set ν)
    → Method universe P → Path-method universe P
    → (w : Σ K family) → P w
  eliminate least P m n = induction least P (forced universe P n) m

  elimination : {ν : Level} → Least M G (κ ⊔ ν) → Elimination universe ν
  elimination least = record
    { elim = eliminate least
    ; elim-intro = λ P m n z →
        forced universe P n (introduce z)
          (eliminate least P m n (introduce z))
          (m z
            (λ p →
              eliminate least P m n
                (input γ (indexed (Σ K family) (λ w → value (pr₁ w)))
                  z p)))
    ; elim-ua = λ P m n a b p →
        propositions-are-sets (forced universe P n b)
          (transport P (identify a b p) (eliminate least P m n a))
          (eliminate least P m n b)
          (apd (eliminate least P m n) (identify a b p))
          (n a b p (eliminate least P m n a) (eliminate least P m n b))
    }
