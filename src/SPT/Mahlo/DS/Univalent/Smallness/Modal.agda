{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Univalent.Smallness.Modal where

-- The smallness principle with unique names from its form under a
-- modality, as DS.Smallness.Modal gives the plain principle. The canonical
-- object is the generated univalent subuniverse of a description γ: the
-- types lying in every closed family of propositions of level ℓ on the
-- identity algebra, the codes of Univalent.Discriminator's `large`,
-- defined from γ alone.
--
-- * Closedness passes between lawful algebras: a family whose points are
--   read as points of a restriction of another algebra is closed when the
--   restriction's family is (`transferred`, through IR.Action's `assemble`
--   and the restriction's heads and children). So closed families of the
--   identity algebra pull back along a decoding (`pulled-back`), and the
--   generated points of M over a type, read through equivalences, form a
--   closed family there (`named-points`).
-- * A lawful algebra M with unique names and a generation G least at ℓ
--   presents the subuniverse on its generated points
--   (`generated-type`, `generated-point`, `point-of-type`,
--   `type-of-point`, `generated-points-are-the-subuniverse`), so the
--   subuniverse is essentially small (`generated-subuniverse-is-small`).
-- * Conversely `large`'s introductions, carried down to a small
--   presentation, keep their law and unique names (`carried`,
--   `lowered-algebra`, `lowered-law`, `lowered-names-are-unique`).
--
-- Essential smallness is a proposition under univalence, so where it is
-- stable under a modality ○, lawful algebras with unique names under ○
-- give the principle, given least generations at ℓ
-- (`univalent-smallness-of-modal-algebras`). At propositional truncation
-- (`univalent-smallness-of-mere-algebras`), and with the generations of an
-- exact classifier at ℓ (`classified-generations`,
-- `univalent-smallness-of-classified-mere-algebras`):
--
--   (Π γ. ∥ Σ M. Law M × unique names ∥) → Univalent-Smallness ℓ,
--
-- so the passage from Smallness needs such algebras only merely
-- (`mere-names-passage`).
--
-- Hence the covers of Univalent.Types' `type-names-passage` are needed only
-- merely too, for all small types at once: under one truncation of the
-- global family of weakly initial covers the chosen passage gives, at every
-- description, merely its lawful algebra with unique names
-- (`algebra-with-unique-names`), so with least generations at ℓ
-- (`mere-covers-passage`, and from an exact classifier
-- `classified-mere-covers-passage`):
--
--   ∥ Global-Weakly-Initial-Covers ℓ ∥ → Names-Passage ℓ.
--
-- A truncation per type would not do: the covering operator returns the
-- covers of the index of every family, so it is a function of the types.

open import SPT.Base
open import SPT.Foundation.Covers.WeaklyInitial using
  (Global-Weakly-Initial-Covers)
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Extensionality.Levels using (funext-below)
open import SPT.Foundation.Fibers using (fiber)
open import SPT.Foundation.HalfAdjoint using (Σ-bicong)
open import SPT.Foundation.Impredicative.PropositionalResizing using
  (propositions-resize-to-their-level)
open import SPT.Foundation.Isomorphisms using
  (_≅_; forward; backward; forward-backward; ≅-refl; ≅-sym; Σ-cong)
open import SPT.Foundation.Modalities using
  (Modality; is-stable; ○-map; truncation-modality)
open import SPT.Foundation.Propositions using
  (is-proposition; Σ-is-proposition)
open import SPT.Foundation.Impredicative.PropositionalClassifier.Exact using
  (Exact-Classifier)
open import SPT.Foundation.Propositions.Closure using
  (isomorphic-to-a-proposition)
open import SPT.Foundation.Size using (is-small)
open import SPT.Foundation.Truncations using (Truncation; ∥∥-map)
open import SPT.Foundation.Univalence using
  ( Equivalence; is-univalent; idtoeq; isomorphism-to-equivalence
  ; equivalence-to-isomorphism )
import SPT.Mahlo.Specification as Specification

open import SPT.IR.Action using (assemble)
open import SPT.IR.Algebra using (Algebra; Law; identity; identity-β)
open import SPT.IR.Description using (Desc; indexed; Shape; Mark)
open import SPT.IR.Restriction using
  (input; heads; children; heads-β)
open import SPT.IR.Smallness using (Smallness)
open import SPT.Mahlo.DS.Smallness.Modal using
  (smallness-is-truncation-stable)
import SPT.IR.Univalent.Classifier as Classifier
open import SPT.Mahlo.DS.Univalent.Completion using (Completions)
open import SPT.Mahlo.DS.Univalent.Discriminator using (large)
open import SPT.IR.Univalent.Generation using
  (Closed; Closed-Family; Least)
open import SPT.IR.Univalent.Resizing using (generation)
open import SPT.Mahlo.DS.Univalent.Smallness using
  (Univalent-Smallness; Names-Passage)
open import SPT.Mahlo.DS.Univalent.Types using
  (Type-Hypotheses; type-names-passage)
open import SPT.IR.Univalent.Universe using (Universe; fibers)

------------------------------------------------------------------------
-- Closedness passes between lawful algebras

-- A shape of M whose inputs are read as points of N's restriction by Q is
-- assembled into a shape there, with the same output; N's operation at its
-- heads is in Q, and its decoding is M's output, by the two laws.

module _
  {ℓ κ κ′ μ ν : Level} {γ : Desc {s = ℓ} (Set ℓ)}
  (extensionality : (A : Set ℓ) → FunExt A (λ _ → Set ℓ))
  (M : Algebra κ γ) (law : Law M) (N : Algebra κ′ γ) (law′ : Law N)
  (Q : Algebra.K N → Set μ) (closed : Closed N Q)
  (P : Algebra.K M → Set ν)
  (lift : (k : Algebra.K M) → P k →
    fiber (λ (x : Σ (Algebra.K N) Q) → Algebra.value N (pr₁ x))
      (Algebra.value M k))
  (back : (k : Algebra.K M) →
    fiber (λ (x : Σ (Algebra.K N) Q) → Algebra.value N (pr₁ x))
      (Algebra.value M k) →
    P k)
  where

  transferred : Closed M P
  transferred a hs =
    let w = assemble extensionality
              (indexed (Algebra.K M) (Algebra.value M))
              (indexed (Σ (Algebra.K N) Q) (λ x → Algebra.value N (pr₁ x)))
              γ a
              (λ p →
                lift (input γ (indexed (Algebra.K M) (Algebra.value M)) a p)
                  (hs p))
    in back (Algebra.operation M a)
         ( ( Algebra.operation N (heads (Algebra.value N) Q γ (pr₁ w))
           , closed (heads (Algebra.value N) Q γ (pr₁ w))
               (children (Algebra.value N) Q γ (pr₁ w)) )
         , law′ (heads (Algebra.value N) Q γ (pr₁ w))
           ∙ heads-β (Algebra.value N) Q γ (pr₁ w)
           ∙ pr₂ w
           ∙ law a ⁻¹ )

------------------------------------------------------------------------
-- Closed families of the identity algebra pull back

-- A type of the family, read at the decoding of a point.

module _
  {ℓ : Level} {γ : Desc {s = ℓ} (Set ℓ)}
  (extensionality : (A : Set ℓ) → FunExt A (λ _ → Set ℓ))
  (M : Algebra ℓ γ) (law : Law M)
  where

  pulled-back : {ν : Level} → Closed-Family (identity γ) ν →
    Closed-Family M ν
  pulled-back C = record
    { family = λ k → Closed-Family.family C (Algebra.value M k)
    ; proposition = λ k → Closed-Family.proposition C (Algebra.value M k)
    ; closed =
        transferred extensionality M law (identity γ) (identity-β γ)
          (Closed-Family.family C) (Closed-Family.closed C)
          (λ k → Closed-Family.family C (Algebra.value M k))
          (λ k c → (Algebra.value M k , c) , refl)
          (λ k w →
            transport (Closed-Family.family C) (pr₂ w) (pr₂ (pr₁ w)))
    }

------------------------------------------------------------------------
-- The named points of a lawful algebra with unique names

-- The generated points of M over X, through equivalences of their
-- decodings with X: a proposition at level ℓ, by unique names under
-- univalence, closed on the identity algebra.

module _
  {ℓ : Level} {γ : Desc {s = ℓ} (Set ℓ)}
  (extensionality : (A : Set ℓ) → FunExt A (λ _ → Set ℓ))
  (univalence : is-univalent ℓ)
  (M : Algebra ℓ γ) (law : Law M)
  (unique :
    (X : Set ℓ) → is-proposition (Specification.Name (Algebra.value M) X))
  (G : Closed-Family M ℓ)
  where

  named-points : Closed-Family (identity γ) ℓ
  named-points = record
    { family = λ X →
        Σ (Σ (Algebra.K M) (λ k → Equivalence (Algebra.value M k) X))
          (λ w → Closed-Family.family G (pr₁ w))
    ; proposition = λ X →
        Σ-is-proposition
          (isomorphic-to-a-proposition
            (Σ-cong (λ k →
              equivalence-to-isomorphism
                ( idtoeq (Algebra.value M k) X
                , univalence (Algebra.value M k) X)))
            (unique X))
          (λ w → Closed-Family.proposition G (pr₁ w))
    ; closed =
        transferred extensionality (identity γ) (identity-β γ) M law
          (Closed-Family.family G) (Closed-Family.closed G)
          (λ X →
            Σ (Σ (Algebra.K M) (λ k → Equivalence (Algebra.value M k) X))
              (λ w → Closed-Family.family G (pr₁ w)))
          (λ X n →
            (pr₁ (pr₁ n) , pr₂ n) ,
            backward
              (equivalence-to-isomorphism
                ( idtoeq (Algebra.value M (pr₁ (pr₁ n))) X
                , univalence (Algebra.value M (pr₁ (pr₁ n))) X))
              (pr₂ (pr₁ n)))
          (λ X w →
            (pr₁ (pr₁ w) , idtoeq (Algebra.value M (pr₁ (pr₁ w))) X (pr₂ w)) ,
            pr₂ (pr₁ w))
    }

------------------------------------------------------------------------
-- The generated points present the subuniverse

-- A generated point decodes to a type in every closed family of level ℓ,
-- by leastness at its pullback; a type in the subuniverse is in the named
-- points, so a generated point decodes to it. Both round trips are
-- identities of propositions.

module _
  {ℓ : Level} {γ : Desc {s = ℓ} (Set ℓ)}
  (extensionality : (A : Set ℓ) → FunExt A (λ _ → Set ℓ))
  (families :
    (X : Set ℓ) →
    FunExt (Closed-Family (identity γ) ℓ) (λ C → Closed-Family.family C X))
  (univalence : is-univalent ℓ)
  (M : Algebra ℓ γ) (law : Law M)
  (unique :
    (X : Set ℓ) → is-proposition (Specification.Name (Algebra.value M) X))
  (G : Closed-Family M ℓ) (least : Least M G ℓ)
  where

  generated-type :
    Σ (Algebra.K M) (Closed-Family.family G) →
    Universe.Code (large γ families)
  generated-type w =
    Algebra.value M (pr₁ w) ,
    (λ C → least (pulled-back extensionality M law C) (pr₁ w) (pr₂ w))

  generated-point :
    Universe.Code (large γ families) →
    Σ (Algebra.K M) (Closed-Family.family G)
  generated-point c =
    pr₁ (pr₁ (pr₂ c (named-points extensionality univalence M law unique G)))
    , pr₂ (pr₂ c (named-points extensionality univalence M law unique G))

  point-of-type : (w : Σ (Algebra.K M) (Closed-Family.family G)) →
    generated-point (generated-type w) ＝ w
  point-of-type w =
    ap (λ n → pr₁ (pr₁ n) , pr₂ n)
      (Closed-Family.proposition
        (named-points extensionality univalence M law unique G)
        (Algebra.value M (pr₁ w))
        (least
          (pulled-back extensionality M law
            (named-points extensionality univalence M law unique G))
          (pr₁ w) (pr₂ w))
        ( ( pr₁ w
          , idtoeq (Algebra.value M (pr₁ w)) (Algebra.value M (pr₁ w)) refl)
        , pr₂ w))

  type-of-point : (c : Universe.Code (large γ families)) →
    generated-type (generated-point c) ＝ c
  type-of-point c =
    let n = pr₂ c (named-points extensionality univalence M law unique G)
        e = backward
              (equivalence-to-isomorphism
                ( idtoeq (Algebra.value M (pr₁ (pr₁ n))) (pr₁ c)
                , univalence (Algebra.value M (pr₁ (pr₁ n))) (pr₁ c)))
              (pr₂ (pr₁ n))
    in to-Σ-＝ e
         (Closed-Family.proposition
           ( generation (identity γ) ℓ
               (propositions-resize-to-their-level (lsuc ℓ)) families)
           (pr₁ c)
           (transport
             (Closed-Family.family
               ( generation (identity γ) ℓ
                   (propositions-resize-to-their-level (lsuc ℓ)) families))
             e (pr₂ (generated-type (generated-point c))))
           (pr₂ c))

  generated-points-are-the-subuniverse :
    Σ (Algebra.K M) (Closed-Family.family G) ≅
    Universe.Code (large γ families)
  generated-points-are-the-subuniverse = record
    { forward = generated-type
    ; backward = generated-point
    ; backward-forward = point-of-type
    ; forward-backward = type-of-point
    }

  generated-subuniverse-is-small :
    is-small ℓ (Universe.Code (large γ families))
  generated-subuniverse-is-small =
    Σ (Algebra.K M) (Closed-Family.family G) ,
    isomorphism-to-equivalence generated-points-are-the-subuniverse

------------------------------------------------------------------------
-- The subuniverse's algebra on a small presentation

-- A small shape is carried to the subuniverse along the presentation,
-- introduced there, and brought back. Its decodings are those of the
-- subuniverse, so its names are theirs.

module _
  {ℓ : Level} {γ : Desc {s = ℓ} (Set ℓ)}
  (extensionality : (A : Set ℓ) → FunExt A (λ _ → Set ℓ))
  (families :
    (X : Set ℓ) →
    FunExt (Closed-Family (identity γ) ℓ) (λ C → Closed-Family.family C X))
  {S : Set ℓ} (E : S ≅ Universe.Code (large γ families))
  where

  carried :
    (z : Shape γ
      (indexed S (λ s → Universe.El (large γ families) (forward E s)))) →
    Σ (Shape γ
        (indexed (Universe.Code (large γ families))
          (Universe.El (large γ families))))
      (λ w →
        Mark γ
          (indexed (Universe.Code (large γ families))
            (Universe.El (large γ families)))
          w
        ＝ Mark γ
            (indexed S (λ s → Universe.El (large γ families) (forward E s)))
            z)
  carried z =
    assemble extensionality
      (indexed S (λ s → Universe.El (large γ families) (forward E s)))
      (indexed (Universe.Code (large γ families))
        (Universe.El (large γ families)))
      γ z
      (λ p →
        forward E
          (input γ
            (indexed S (λ s → Universe.El (large γ families) (forward E s)))
            z p)
        , refl)

  lowered-algebra : Algebra ℓ γ
  lowered-algebra = record
    { K = S
    ; value = λ s → Universe.El (large γ families) (forward E s)
    ; operation = λ z →
        backward E (Universe.intro (large γ families) (pr₁ (carried z)))
    }

  lowered-law : Law lowered-algebra
  lowered-law z =
    ap (Universe.El (large γ families))
      (forward-backward E
        (Universe.intro (large γ families) (pr₁ (carried z))))
    ∙ Universe.intro-β (large γ families) (pr₁ (carried z))
    ∙ pr₂ (carried z)

  lowered-names-are-unique : (X : Set ℓ) →
    is-proposition
      (Specification.Name (Algebra.value lowered-algebra) X)
  lowered-names-are-unique X =
    isomorphic-to-a-proposition
      (≅-sym
        (Σ-bicong
          (λ s → Universe.El (large γ families) (forward E s) ＝ X)
          (λ c → Universe.El (large γ families) c ＝ X)
          E (λ s → ≅-refl)))
      (fibers (large γ families) X)

------------------------------------------------------------------------
-- The principle from its modal form

-- Extensionality at ℓ + 1 gives the extensionality the steps use.

module _ {ℓ : Level}
  (funext : (A : Set (lsuc ℓ)) (B : A → Set (lsuc ℓ)) → FunExt A B)
  where

  index-families : (A : Set ℓ) → FunExt A (λ _ → Set ℓ)
  index-families A = funext-below (lsuc ℓ) funext A (λ _ → Set ℓ)

  closed-families : (γ : Desc {s = ℓ} (Set ℓ)) (X : Set ℓ) →
    FunExt (Closed-Family (identity γ) ℓ) (λ C → Closed-Family.family C X)
  closed-families γ X =
    funext-below (lsuc ℓ) funext (Closed-Family (identity γ) ℓ)
      (λ C → Closed-Family.family C X)

-- Mathematical shape: Π γ. ○ (Σ M. Law M × unique names) →
-- Univalent-Smallness ℓ, when ○ is stable at essential smallness, given a
-- generation least at ℓ of every algebra.

module _ {ℓ : Level}
  (funext : (A : Set (lsuc ℓ)) (B : A → Set (lsuc ℓ)) → FunExt A B)
  (univalence : is-univalent ℓ)
  (generations :
    (γ : Desc {s = ℓ} (Set ℓ)) (M : Algebra ℓ γ) →
    Σ (Closed-Family M ℓ) (λ G → Least M G ℓ))
  where

  subuniverse-smallness : (T : Modality (lsuc ℓ)) →
    ((X : Set (lsuc ℓ)) → is-stable T (is-small ℓ X)) →
    (γ : Desc {s = ℓ} (Set ℓ)) →
    Modality.○_ T
      (Σ (Algebra ℓ γ) (λ M →
        Law M ×
        ((X : Set ℓ) →
          is-proposition (Specification.Name (Algebra.value M) X)))) →
    is-small ℓ (Universe.Code (large γ (closed-families funext γ)))
  subuniverse-smallness T stable γ h =
    stable (Universe.Code (large γ (closed-families funext γ)))
      (○-map T
        (λ w →
          generated-subuniverse-is-small (index-families funext)
            (closed-families funext γ) univalence (pr₁ w) (pr₁ (pr₂ w))
            (pr₂ (pr₂ w)) (pr₁ (generations γ (pr₁ w)))
            (pr₂ (generations γ (pr₁ w))))
        h)

  univalent-smallness-of-modal-algebras : (T : Modality (lsuc ℓ)) →
    ((X : Set (lsuc ℓ)) → is-stable T (is-small ℓ X)) →
    ((γ : Desc {s = ℓ} (Set ℓ)) →
      Modality.○_ T
        (Σ (Algebra ℓ γ) (λ M →
          Law M ×
          ((X : Set ℓ) →
            is-proposition (Specification.Name (Algebra.value M) X))))) →
    Univalent-Smallness ℓ
  univalent-smallness-of-modal-algebras T stable h = record
    { algebra = λ γ →
        lowered-algebra (index-families funext) (closed-families funext γ)
          (equivalence-to-isomorphism
            (pr₂ (subuniverse-smallness T stable γ (h γ))))
    ; law = λ γ →
        lowered-law (index-families funext) (closed-families funext γ)
          (equivalence-to-isomorphism
            (pr₂ (subuniverse-smallness T stable γ (h γ))))
    ; unique = λ γ →
        lowered-names-are-unique (index-families funext)
          (closed-families funext γ)
          (equivalence-to-isomorphism
            (pr₂ (subuniverse-smallness T stable γ (h γ))))
    }

  -- At propositional truncation.
  univalent-smallness-of-mere-algebras : (t : Truncation (lsuc ℓ)) →
    ((γ : Desc {s = ℓ} (Set ℓ)) →
      Truncation.∥_∥ t
        (Σ (Algebra ℓ γ) (λ M →
          Law M ×
          ((X : Set ℓ) →
            is-proposition (Specification.Name (Algebra.value M) X))))) →
    Univalent-Smallness ℓ
  univalent-smallness-of-mere-algebras t =
    univalent-smallness-of-modal-algebras (truncation-modality t)
      (smallness-is-truncation-stable funext t univalence)

------------------------------------------------------------------------
-- With an exact classifier

-- Its intersections of closed families of proxies are generations least
-- at ℓ (IR.Univalent.Classifier).

classified-generations : {ℓ : Level} →
  ((A : Set ℓ) (B : A → Set ℓ) → FunExt A B) → Exact-Classifier ℓ →
  (γ : Desc {s = ℓ} (Set ℓ)) (M : Algebra ℓ γ) →
  Σ (Closed-Family M ℓ) (λ G → Least M G ℓ)
classified-generations fe C γ M =
  Classifier.generation M C fe , Classifier.least M C fe

univalent-smallness-of-classified-mere-algebras : {ℓ : Level} →
  ((A : Set (lsuc ℓ)) (B : A → Set (lsuc ℓ)) → FunExt A B) →
  is-univalent ℓ → Exact-Classifier ℓ → (t : Truncation (lsuc ℓ)) →
  ((γ : Desc {s = ℓ} (Set ℓ)) →
    Truncation.∥_∥ t
      (Σ (Algebra ℓ γ) (λ M →
        Law M ×
        ((X : Set ℓ) →
          is-proposition (Specification.Name (Algebra.value M) X))))) →
  Univalent-Smallness ℓ
univalent-smallness-of-classified-mere-algebras {ℓ} funext univalence C =
  univalent-smallness-of-mere-algebras funext univalence
    (classified-generations (λ A B → funext-below (lsuc ℓ) funext A B) C)

-- So the passage from Smallness asks lawful algebras with unique names
-- only merely.
mere-names-passage : {ℓ : Level} →
  ((A : Set (lsuc ℓ)) (B : A → Set (lsuc ℓ)) → FunExt A B) →
  is-univalent ℓ → Exact-Classifier ℓ → (t : Truncation (lsuc ℓ)) →
  (Smallness ℓ → (γ : Desc {s = ℓ} (Set ℓ)) →
    Truncation.∥_∥ t
      (Σ (Algebra ℓ γ) (λ M →
        Law M ×
        ((X : Set ℓ) →
          is-proposition (Specification.Name (Algebra.value M) X))))) →
  Names-Passage ℓ
mere-names-passage funext univalence C t mere small =
  univalent-smallness-of-classified-mere-algebras funext univalence C t
    (mere small)

------------------------------------------------------------------------
-- From merely existing covers

-- The principle with unique names gives, at every description, its lawful
-- algebra with unique names.
algebra-with-unique-names : {ℓ : Level} → Univalent-Smallness ℓ →
  (γ : Desc {s = ℓ} (Set ℓ)) →
  Σ (Algebra ℓ γ) (λ M →
    Law M ×
    ((X : Set ℓ) →
      is-proposition (Specification.Name (Algebra.value M) X)))
algebra-with-unique-names U γ =
  Univalent-Smallness.algebra U γ ,
  (Univalent-Smallness.law U γ , Univalent-Smallness.unique U γ)

-- Mathematical shape: least generations at ℓ, a truncation at ℓ + 1 and
-- completions ⊢ ∥ Global-Weakly-Initial-Covers ℓ ∥ → Names-Passage ℓ.
mere-covers-passage : {ℓ : Level} →
  ((A : Set (lsuc ℓ)) (B : A → Set (lsuc ℓ)) → FunExt A B) →
  (H : Type-Hypotheses ℓ) →
  ((γ : Desc {s = ℓ} (Set ℓ)) (M : Algebra ℓ γ) →
    Σ (Closed-Family M ℓ) (λ G → Least M G ℓ)) →
  (t : Truncation (lsuc ℓ)) → Completions ℓ (Set ℓ) →
  Truncation.∥_∥ t (Global-Weakly-Initial-Covers ℓ) → Names-Passage ℓ
mere-covers-passage funext H generations t completions covers small =
  univalent-smallness-of-mere-algebras funext
    (Type-Hypotheses.univalence H) generations t
    (λ γ →
      ∥∥-map t
        (λ W →
          algebra-with-unique-names
            (type-names-passage H completions W small) γ)
        covers)

-- With an exact classifier at ℓ, whose intersections of closed families of
-- proxies are least generations (`classified-generations`).
classified-mere-covers-passage : {ℓ : Level} →
  ((A : Set (lsuc ℓ)) (B : A → Set (lsuc ℓ)) → FunExt A B) →
  (H : Type-Hypotheses ℓ) → Exact-Classifier ℓ →
  (t : Truncation (lsuc ℓ)) → Completions ℓ (Set ℓ) →
  Truncation.∥_∥ t (Global-Weakly-Initial-Covers ℓ) → Names-Passage ℓ
classified-mere-covers-passage funext H C =
  mere-covers-passage funext H
    (classified-generations (Type-Hypotheses.functions H) C)
