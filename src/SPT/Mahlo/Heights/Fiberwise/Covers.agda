{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Heights.Fiberwise.Covers where

-- Weakly initial covers (Foundation.Covers.WeaklyInitial) bound merely
-- named families at the regular nodes of the fiberwise stages
-- (Heights.Fiberwise) that name them. A node names the covers
-- (`Names-Covers`) when the domain of each weakly initial cover of the
-- decoding of each of its codes is the decoding of a code. At a regular
-- node that names them every family whose members are each merely named
-- at some child is merely named at one child (`covers-bound-named-families`):
--
--   Global-Weakly-Initial-Covers ℓ → Regular → Names-Covers → Named-Regular.
--
-- The covers give, merely, a cover and a child for each point of its
-- domain naming the member over its image; the domain is the decoding of
-- a code, so these children lie below one child (`cover-bound`), which
-- names every member, each member lying merely over a point of the domain
-- (`cover-bound-names`). The stage of a regular node of an operator joined
-- with the covering one (Univalent.Types' `type-covering`) names the
-- covers, as members of the covering family at the constant family over a
-- code (`covering-stages-name-covers`). So the fans of the closures of the
-- completed codes of these operators bound merely named families
-- (`covering-fans-are-named-regular`). They are the operators of
-- Univalent.Types' `type-names-passage`, where the same covers give
-- closures that collect names.

open import SPT.Base
open import SPT.Foundation.Covers using (map-covered; extract-proposition)
open import SPT.Foundation.Covers.WeaklyInitial using
  (Weakly-Initial-Covers; Global-Weakly-Initial-Covers)
import SPT.Foundation.Tree as Tree
import SPT.Mahlo.Ambient as Ambient
open import SPT.Mahlo.DS.Naming using (recast)
open import SPT.Mahlo.DS.Realization.Family using (cast)
import SPT.Mahlo.Specification as Specification
open import SPT.Mahlo.DS.Univalent.Completion using (Completions)
open import SPT.Mahlo.DS.Univalent.Types using
  (Type-Hypotheses; _⊎ᵒ_; type-covering; second-type-members-are-named)
open import SPT.Mahlo.Heights.Stages using (Stage; decoding)
open import SPT.Mahlo.Heights.Regular using
  (Regular; closure; embed; trees-regular; stage-name; stage-name-β)
open import SPT.Mahlo.Heights.Fiberwise using
  ( completed-codes; completed-codes-have-codes
  ; completed-codes-are-functorial; Named-At; Named-Regular
  ; named-at-is-proposition; moved-at )
open import SPT.OrdinalGeometry.Height.Ordinals using (Height)
open import SPT.OrdinalGeometry.Height.Simulation using (⊏→⊑)

------------------------------------------------------------------------
-- Nodes that name the weakly initial covers of their decodings

module _ {ℓ : Level} (completions : Completions ℓ (Set ℓ))
  (Φ : Ambient.Operator ℓ) (covers : Global-Weakly-Initial-Covers ℓ)
  {X : Set ℓ} (f : X → Height ℓ) where

  -- The domain of every weakly initial cover of the decoding of a code is
  -- the decoding of a code.
  Names-Covers : Set (lsuc ℓ)
  Names-Covers =
    (a : Stage (completed-codes completions Φ) (Tree.node X f))
    (i :
      Weakly-Initial-Covers.index
        (covers
          (decoding (completed-codes completions Φ) (Tree.node X f) a)))
    → Specification.Name
        (decoding (completed-codes completions Φ) (Tree.node X f))
        (Weakly-Initial-Covers.domain
          (covers
            (decoding (completed-codes completions Φ) (Tree.node X f) a))
          i)

------------------------------------------------------------------------
-- The bound of a section over a named cover

module _ {ℓ : Level} (completions : Completions ℓ (Set ℓ))
  (Φ : Ambient.Operator ℓ) (H : Type-Hypotheses ℓ)
  (covers : Global-Weakly-Initial-Covers ℓ)
  {X : Set ℓ} {f : X → Height ℓ}
  (regular : Regular (completed-codes completions Φ) X f)
  (named : Names-Covers completions Φ covers f)
  (a : Stage (completed-codes completions Φ) (Tree.node X f))
  (B : decoding (completed-codes completions Φ) (Tree.node X f) a → Set ℓ)
  (i :
    Weakly-Initial-Covers.index
      (covers (decoding (completed-codes completions Φ) (Tree.node X f) a)))
  (s :
    (d :
      Weakly-Initial-Covers.domain
        (covers
          (decoding (completed-codes completions Φ) (Tree.node X f) a))
        i)
    → Σ X
        (λ z →
          Named-At completions Φ f z
            (B
              (Weakly-Initial-Covers.projection
                (covers
                  (decoding (completed-codes completions Φ)
                    (Tree.node X f) a))
                i d))))
  where

  -- The children of the section, as a family of the node's codes over the
  -- code of the domain.
  section-codes :
    decoding (completed-codes completions Φ) (Tree.node X f)
      (pr₁ (named a i))
    → Stage (completed-codes completions Φ) (Tree.node X f)
  section-codes y =
    pr₁ (s (cast (pr₂ (named a i)) y))
    , pr₁ (pr₂ (s (cast (pr₂ (named a i)) y)))

  -- One child above them.
  cover-bound : X
  cover-bound = pr₁ (Regular.bound regular (pr₁ (named a i)) section-codes)

  -- Every member is named at that child: it lies merely over a point of
  -- the domain, whose name moves up, and names at one child are unique.
  cover-bound-names :
    (y : decoding (completed-codes completions Φ) (Tree.node X f) a) →
    Named-At completions Φ f cover-bound (B y)
  cover-bound-names y =
    extract-proposition
      (map-covered
        (λ w →
          transport (λ v → Named-At completions Φ f cover-bound (B v))
            (ap
              (Weakly-Initial-Covers.projection
                (covers
                  (decoding (completed-codes completions Φ)
                    (Tree.node X f) a))
                i)
              (recast (pr₂ (named a i)) (pr₁ w))
            ∙ pr₂ w)
            (moved-at completions Φ H f
              (pr₁
                (s
                  (cast (pr₂ (named a i))
                    (cast (pr₂ (named a i) ⁻¹) (pr₁ w)))))
              cover-bound
              (⊏→⊑
                (pr₂
                  (pr₂
                    (Regular.bound regular (pr₁ (named a i)) section-codes))
                  (cast (pr₂ (named a i) ⁻¹) (pr₁ w))))
              (B
                (Weakly-Initial-Covers.projection
                  (covers
                    (decoding (completed-codes completions Φ)
                      (Tree.node X f) a))
                  i
                  (cast (pr₂ (named a i))
                    (cast (pr₂ (named a i) ⁻¹) (pr₁ w)))))
              (pr₂
                (s
                  (cast (pr₂ (named a i))
                    (cast (pr₂ (named a i) ⁻¹) (pr₁ w)))))))
        (Weakly-Initial-Covers.projections-cover
          (covers
            (decoding (completed-codes completions Φ) (Tree.node X f) a))
          i y))
      (named-at-is-proposition completions Φ H f cover-bound (B y))

------------------------------------------------------------------------
-- Weakly initial covers bound merely named families

covers-bound-named-families :
  {ℓ : Level} (completions : Completions ℓ (Set ℓ))
  (Φ : Ambient.Operator ℓ) (H : Type-Hypotheses ℓ)
  (covers : Global-Weakly-Initial-Covers ℓ)
  {X : Set ℓ} {f : X → Height ℓ}
  → Regular (completed-codes completions Φ) X f
  → Names-Covers completions Φ covers f
  → Named-Regular completions Φ f
covers-bound-named-families completions Φ H covers {X} {f} regular named
  a B at =
  map-covered
    (λ w →
      cover-bound completions Φ H covers regular named a B (pr₁ w) (pr₂ w)
      , cover-bound-names completions Φ H covers regular named a B (pr₁ w)
          (pr₂ w))
    (Weakly-Initial-Covers.sections
      (covers (decoding (completed-codes completions Φ) (Tree.node X f) a))
      (λ y → Σ X (λ z → Named-At completions Φ f z (B y)))
      at)

-- At a regular node of an operator joined with the covering one, the
-- closure of the stage names the domains of the covers: they are the
-- covering family's members at the constant family over a code.
covering-stages-name-covers :
  {ℓ : Level} (completions : Completions ℓ (Set ℓ)) (H : Type-Hypotheses ℓ)
  (covers : Global-Weakly-Initial-Covers ℓ) (Ψ : Ambient.Operator ℓ)
  {X : Set ℓ} {f : X → Height ℓ}
  → Regular (completed-codes completions (Ψ ⊎ᵒ type-covering covers)) X f
  → Names-Covers completions (Ψ ⊎ᵒ type-covering covers) covers f
covering-stages-name-covers completions H covers Ψ regular a i =
  second-type-members-are-named (Type-Hypotheses.families H) Ψ
    (type-covering covers)
    (closure (Type-Hypotheses.families H)
      (completed-codes-have-codes completions (Ψ ⊎ᵒ type-covering covers))
      (completed-codes-are-functorial completions
        (Ψ ⊎ᵒ type-covering covers) H)
      regular)
    (a , (λ x → a)) i

-- So the fans of the closures of the completed codes of these operators
-- bound merely named families.
covering-fans-are-named-regular :
  {ℓ : Level} (completions : Completions ℓ (Set ℓ)) (H : Type-Hypotheses ℓ)
  (covers : Global-Weakly-Initial-Covers ℓ) (Ψ : Ambient.Operator ℓ)
  {K : Set ℓ}
  (L :
    Specification.Closure (Ambient.formers ℓ)
      (completed-codes completions (Ψ ⊎ᵒ type-covering covers)) K)
  → Named-Regular completions (Ψ ⊎ᵒ type-covering covers) (embed L)
covering-fans-are-named-regular completions H covers Ψ L =
  covers-bound-named-families completions (Ψ ⊎ᵒ type-covering covers) H
    covers
    (trees-regular L (completed-codes completions (Ψ ⊎ᵒ type-covering covers))
      (stage-name L (Type-Hypotheses.families H))
      (stage-name-β L (Type-Hypotheses.families H)))
    (covering-stages-name-covers completions H covers Ψ
      (trees-regular L
        (completed-codes completions (Ψ ⊎ᵒ type-covering covers))
        (stage-name L (Type-Hypotheses.families H))
        (stage-name-β L (Type-Hypotheses.families H))))
