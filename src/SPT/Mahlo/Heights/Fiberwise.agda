{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Heights.Fiberwise where

-- Fiberwise univalent stages: the stages (Heights.Stages) of the layer
-- whose codes over a universe are the completion of Φ's codes over it
-- (`completed-codes`, Univalent.Completion), so each completed code keeps
-- its child:
--
--   Stage (completed-codes Φ) (node X f)
--     = Σ x : X. completed (completion of Φ's codes over the stage of f x).
--
-- The layer has Φ's codes (`completed-codes-have-codes`), and under
-- univalence (Univalent.Types' Type-Hypotheses) it is functorial, a
-- completed code being merely the image of a code and so named in the
-- target completion (`completed-codes-are-functorial`). So the Mahlo rule
-- gives heights regular for these stages (Heights.Regular's
-- `reflection-regular`), and the stage of a regular node is a closure of
-- the formers and Φ (Heights.Regular's `closure`).
--
-- A type is named at a child (`Named-At`) when it is equivalent to the
-- decoding of a completed code over the child's stage. Such names are
-- unique (`named-at-is-proposition`) and move up the children
-- (`moved-at`). A node bounds merely named families (`Named-Regular`)
-- when, for a code a and a family B whose members are each merely named at
-- some child, all are merely named at one child. At a regular node:
--
--   sums named in the global stage ⇔ the closure collects names
--     ⇔ Named-Regular ⇔ Children-Choice,
--
-- the global stage being the completion of the node's codes
-- (`global-collection`, `global-sums`; `named-regular-collection`,
-- `collection-named-regular`; `named-regular-choice`,
-- `choice-named-regular`). With its sums named the global stage is a
-- closure of Φ with unique names (`global-closure`,
-- `global-closure-has-unique-names`). So when the fans of the reflections
-- of the completed codes of every operator bound merely named families,
-- every operator has a closure with unique names
-- (`unique-names-from-named-regular-fans`), and smallness gives its form
-- with unique names (`named-regular-passage`). Whether the fans bound
-- merely named families is open; weakly initial covers give it at the
-- operators joined with the covering one (Heights.Fiberwise.Covers).

open import SPT.Base
open import SPT.Foundation.Covers using
  (Covered; map-covered; extract-proposition; identity-is-cover)
open import SPT.Foundation.Isomorphisms using
  (≅-trans; transport-is-isomorphism)
open import SPT.Foundation.Propositions using (is-proposition)
open import SPT.Foundation.Univalence using
  (Equivalence; isomorphism-to-equivalence; equivalence-to-isomorphism)
import SPT.Foundation.Tree as Tree
import SPT.Mahlo.Ambient as Ambient
open import SPT.Foundation.Tree.W using (W)
import SPT.Mahlo.Specification as Specification
open import SPT.Mahlo.DS.Ambient using (mahlo)
open import SPT.IR.Smallness using (Smallness)
open import SPT.Mahlo.DS.Univalent.Completion using
  ( Completion; Completions; Collects-Names; Has-Unique-Names
  ; completed-closure; completed-closure-has-unique-names
  ; equivalence-names-are-propositions; Small-Closure )
open import SPT.Mahlo.DS.Univalent.Completion.Map using (transfer)
open import SPT.Mahlo.DS.Univalent.Gluing using (Named-Cover)
open import SPT.Mahlo.DS.Univalent.Smallness using
  (Names-Passage; smallness-of-reflector)
open import SPT.Mahlo.DS.Univalent.Sums using
  (Completed-Sums; collection-from-completed-sums; sums-from-collection)
open import SPT.Mahlo.DS.Univalent.Types using
  (Type-Hypotheses; type-parent; reflector-of-unique-names)
open import SPT.Mahlo.Heights.Stages using
  ( Code; decode; Has-Codes; Functorial; Stage; decoding; include
  ; included )
open import SPT.Mahlo.Heights.Stages.Map using (code-map; code-map-β)
open import SPT.Mahlo.Heights.Regular using
  (Regular; closure; embed; trees-regular; stage-name; stage-name-β)
open import SPT.OrdinalGeometry.Height.Ordinals using (Height)
open import SPT.OrdinalGeometry.Height.Simulation using (_⊑_; ⊏→⊑)

------------------------------------------------------------------------
-- The completed codes

module _ {ℓ : Level} (completions : Completions ℓ (Set ℓ))
  (Φ : Ambient.Operator ℓ) where

  -- The completion of Φ's codes over a universe.
  codes-completion :
    (F : Specification.Family (λ (A : Set ℓ) → A)) →
    Completion (decode {ℓ} {Φ} {pr₁ F} {pr₂ F})
  codes-completion F = completions (Code Φ (pr₁ F) (pr₂ F)) decode

  -- Its completed codes with their decodings: a layer.
  completed-codes : Ambient.Operator ℓ
  completed-codes F =
    Completion.completed (codes-completion F)
    , Completion.decode (codes-completion F)

  -- Φ's codes are completed codes, through the inclusion.
  completed-codes-have-codes : Has-Codes Φ completed-codes
  completed-codes-have-codes = record
    { code = λ {U} {T} c → Completion.include (codes-completion (U , T)) c
    ; code-β = λ {U} {T} c →
        Completion.include-decodes (codes-completion (U , T)) c
    }

  -- Under univalence the completed codes move along a map of universes
  -- that keeps decodings: a completed code is merely the image of a code,
  -- whose image is named in the target completion.
  completed-codes-are-functorial :
    Type-Hypotheses ℓ → Functorial completed-codes
  completed-codes-are-functorial H = record
    { move = λ {U} {U′} T T′ h h-β u →
        pr₁
          (transfer H (codes-completion (U , T)) (codes-completion (U′ , T′))
            (code-map (Type-Hypotheses.families H) T T′ h h-β Φ)
            (code-map-β (Type-Hypotheses.families H) T T′ h h-β Φ) u)
    ; move-β = λ {U} {U′} T T′ h h-β u →
        pr₂
          (transfer H (codes-completion (U , T)) (codes-completion (U′ , T′))
            (code-map (Type-Hypotheses.families H) T T′ h h-β Φ)
            (code-map-β (Type-Hypotheses.families H) T T′ h h-β Φ) u)
    }

------------------------------------------------------------------------
-- Names at a child, and nodes that bound merely named families

module _ {ℓ : Level} (completions : Completions ℓ (Set ℓ))
  (Φ : Ambient.Operator ℓ) {X : Set ℓ} (f : X → Height ℓ) where

  -- A type named at the child z: an equivalence with a completed code
  -- over the child's stage.
  Named-At : X → Set ℓ → Set ℓ
  Named-At z B =
    Σ
      (pr₁
        (completed-codes completions Φ
          ( Stage (completed-codes completions Φ) (f z)
          , decoding (completed-codes completions Φ) (f z))))
      (λ u →
        Equivalence
          (pr₂
            (completed-codes completions Φ
              ( Stage (completed-codes completions Φ) (f z)
              , decoding (completed-codes completions Φ) (f z)))
            u)
          B)

  -- The node bounds merely named families: when each member is merely
  -- named at some child, all are merely named at one child.
  Named-Regular : Set (lsuc ℓ)
  Named-Regular =
    (a : Stage (completed-codes completions Φ) (Tree.node X f))
    (B : decoding (completed-codes completions Φ) (Tree.node X f) a → Set ℓ)
    → ((y : decoding (completed-codes completions Φ) (Tree.node X f) a) →
        Covered ℓ (Σ X (λ z → Named-At z (B y))))
    → Covered ℓ
        (Σ X
          (λ z →
            (y : decoding (completed-codes completions Φ) (Tree.node X f) a)
            → Named-At z (B y)))

  -- A choice of children for merely named families.
  Children-Choice : Set (lsuc ℓ)
  Children-Choice =
    (a : Stage (completed-codes completions Φ) (Tree.node X f))
    (B : decoding (completed-codes completions Φ) (Tree.node X f) a → Set ℓ)
    → ((y : decoding (completed-codes completions Φ) (Tree.node X f) a) →
        Covered ℓ (Σ X (λ z → Named-At z (B y))))
    → Covered ℓ
        ((y : decoding (completed-codes completions Φ) (Tree.node X f) a)
          → Σ X (λ z → Named-At z (B y)))

  -- One child naming every member is a choice: the constant one.
  named-regular-choice : Named-Regular → Children-Choice
  named-regular-choice named a B at =
    map-covered (λ w y → pr₁ w , pr₂ w y) (named a B at)

------------------------------------------------------------------------
-- Names at a child are unique, and move up

module _ {ℓ : Level} (completions : Completions ℓ (Set ℓ))
  (Φ : Ambient.Operator ℓ) (H : Type-Hypotheses ℓ) where

  named-at-is-proposition : {X : Set ℓ} (f : X → Height ℓ) (z : X)
    (B : Set ℓ) → is-proposition (Named-At completions Φ f z B)
  named-at-is-proposition f z B =
    equivalence-names-are-propositions (type-parent H)
      (codes-completion completions Φ
        ( Stage (completed-codes completions Φ) (f z)
        , decoding (completed-codes completions Φ) (f z)))
      B

  -- The completed code moves along the inclusion of the stages, its
  -- decoding kept.
  moved-at : {X : Set ℓ} (f : X → Height ℓ) (z′ z : X) → f z′ ⊑ f z →
    (B : Set ℓ) → Named-At completions Φ f z′ B →
    Named-At completions Φ f z B
  moved-at f z′ z q B n =
    Functorial.move (completed-codes-are-functorial completions Φ H)
      (decoding (completed-codes completions Φ) (f z′))
      (decoding (completed-codes completions Φ) (f z))
      (include (completed-codes-are-functorial completions Φ H) q)
      (included (completed-codes-are-functorial completions Φ H) q)
      (pr₁ n)
    , isomorphism-to-equivalence
        (≅-trans
          (transport-is-isomorphism id
            (Functorial.move-β
              (completed-codes-are-functorial completions Φ H)
              (decoding (completed-codes completions Φ) (f z′))
              (decoding (completed-codes completions Φ) (f z))
              (include (completed-codes-are-functorial completions Φ H) q)
              (included (completed-codes-are-functorial completions Φ H) q)
              (pr₁ n)))
          (equivalence-to-isomorphism (pr₂ n)))

------------------------------------------------------------------------
-- The global stage of a regular node

module _ {ℓ : Level} (completions : Completions ℓ (Set ℓ))
  (Φ : Ambient.Operator ℓ) (H : Type-Hypotheses ℓ)
  {X : Set ℓ} {f : X → Height ℓ}
  (regular : Regular (completed-codes completions Φ) X f)
  where

  -- Sums named in the global stage give collection.
  global-collection :
    Completed-Sums
      (completions (Stage (completed-codes completions Φ) (Tree.node X f))
        (decoding (completed-codes completions Φ) (Tree.node X f)))
    → Collects-Names (type-parent H)
        (closure (Type-Hypotheses.families H)
          (completed-codes-have-codes completions Φ)
          (completed-codes-are-functorial completions Φ H) regular)
  global-collection =
    collection-from-completed-sums H
      (closure (Type-Hypotheses.families H)
        (completed-codes-have-codes completions Φ)
        (completed-codes-are-functorial completions Φ H) regular)
      (completions (Stage (completed-codes completions Φ) (Tree.node X f))
        (decoding (completed-codes completions Φ) (Tree.node X f)))

  -- Collection gives them back, through the completed closure.
  global-sums :
    Collects-Names (type-parent H)
      (closure (Type-Hypotheses.families H)
        (completed-codes-have-codes completions Φ)
        (completed-codes-are-functorial completions Φ H) regular)
    → Completed-Sums
        (completions (Stage (completed-codes completions Φ) (Tree.node X f))
          (decoding (completed-codes completions Φ) (Tree.node X f)))
  global-sums =
    sums-from-collection H
      (closure (Type-Hypotheses.families H)
        (completed-codes-have-codes completions Φ)
        (completed-codes-are-functorial completions Φ H) regular)
      (completions (Stage (completed-codes completions Φ) (Tree.node X f))
        (decoding (completed-codes completions Φ) (Tree.node X f)))

  -- With its sums named, the global stage is a closure of Φ with unique
  -- names.
  global-closure :
    Completed-Sums
      (completions (Stage (completed-codes completions Φ) (Tree.node X f))
        (decoding (completed-codes completions Φ) (Tree.node X f)))
    → Specification.Closure (Ambient.formers ℓ) Φ
        (Completion.completed
          (completions
            (Stage (completed-codes completions Φ) (Tree.node X f))
            (decoding (completed-codes completions Φ) (Tree.node X f))))
  global-closure sums =
    completed-closure (type-parent H)
      (closure (Type-Hypotheses.families H)
        (completed-codes-have-codes completions Φ)
        (completed-codes-are-functorial completions Φ H) regular)
      (global-collection sums)
      (completions (Stage (completed-codes completions Φ) (Tree.node X f))
        (decoding (completed-codes completions Φ) (Tree.node X f)))

  global-closure-has-unique-names :
    (sums :
      Completed-Sums
        (completions (Stage (completed-codes completions Φ) (Tree.node X f))
          (decoding (completed-codes completions Φ) (Tree.node X f))))
    → Has-Unique-Names (type-parent H) (global-closure sums)
  global-closure-has-unique-names sums =
    completed-closure-has-unique-names (type-parent H)
      (closure (Type-Hypotheses.families H)
        (completed-codes-have-codes completions Φ)
        (completed-codes-are-functorial completions Φ H) regular)
      (global-collection sums)
      (completions (Stage (completed-codes completions Φ) (Tree.node X f))
        (decoding (completed-codes completions Φ) (Tree.node X f)))

  ----------------------------------------------------------------------
  -- Collection is a bound for merely named families

  -- A bound for merely named families gives collection, over the arity
  -- itself.
  named-regular-collection :
    Named-Regular completions Φ f
    → Collects-Names (type-parent H)
        (closure (Type-Hypotheses.families H)
          (completed-codes-have-codes completions Φ)
          (completed-codes-are-functorial completions Φ H) regular)
  named-regular-collection named a B merely =
    map-covered
      (λ w → record
        { domain = a
        ; owner = id
        ; names = λ y → pr₁ w , pr₁ (pr₂ w y)
        ; named = λ y → equivalence-to-isomorphism (pr₂ (pr₂ w y))
        ; covers = identity-is-cover
        })
      (named a B
        (λ y →
          map-covered
            (λ n →
              pr₁ (pr₁ n) ,
              (pr₂ (pr₁ n) , isomorphism-to-equivalence (pr₂ n)))
            (merely y)))

  -- The child above the names of a named cover.
  cover-child :
    (a : Stage (completed-codes completions Φ) (Tree.node X f))
    (B : decoding (completed-codes completions Φ) (Tree.node X f) a → Set ℓ)
    → Named-Cover
        (Specification.Decode (λ (A : Set ℓ) → A)
          (decoding (completed-codes completions Φ) (Tree.node X f)))
        a B
    → X
  cover-child a B N =
    pr₁ (Regular.bound regular (Named-Cover.domain N) (Named-Cover.names N))

  -- Every member is named at that child: merely through an owner, whose
  -- name moves up there, and names at one child are unique.
  cover-named :
    (a : Stage (completed-codes completions Φ) (Tree.node X f))
    (B : decoding (completed-codes completions Φ) (Tree.node X f) a → Set ℓ)
    (N :
      Named-Cover
        (Specification.Decode (λ (A : Set ℓ) → A)
          (decoding (completed-codes completions Φ) (Tree.node X f)))
        a B)
    (y : decoding (completed-codes completions Φ) (Tree.node X f) a)
    → Named-At completions Φ f (cover-child a B N) (B y)
  cover-named a B N y =
    extract-proposition
      (map-covered
        (λ e →
          moved-at completions Φ H f (pr₁ (Named-Cover.names N (pr₁ e)))
            (cover-child a B N)
            (⊏→⊑
              (pr₂
                (pr₂
                  (Regular.bound regular (Named-Cover.domain N)
                    (Named-Cover.names N)))
                (pr₁ e)))
            (B y)
            ( pr₂ (Named-Cover.names N (pr₁ e))
            , isomorphism-to-equivalence
                (≅-trans (Named-Cover.named N (pr₁ e))
                  (transport-is-isomorphism B (pr₂ e)))))
        (Named-Cover.covers N y))
      (named-at-is-proposition completions Φ H f (cover-child a B N) (B y))

  -- Collection gives the bound.
  collection-named-regular :
    Collects-Names (type-parent H)
      (closure (Type-Hypotheses.families H)
        (completed-codes-have-codes completions Φ)
        (completed-codes-are-functorial completions Φ H) regular)
    → Named-Regular completions Φ f
  collection-named-regular collection a B at =
    map-covered (λ N → cover-child a B N , cover-named a B N)
      (collection a B
        (λ y →
          map-covered
            (λ n →
              (pr₁ n , pr₁ (pr₂ n)) ,
              equivalence-to-isomorphism (pr₂ (pr₂ n)))
            (at y)))

  -- So sums in the global stage are exactly a bound for merely named
  -- families.
  sums-named-regular :
    Completed-Sums
      (completions (Stage (completed-codes completions Φ) (Tree.node X f))
        (decoding (completed-codes completions Φ) (Tree.node X f)))
    → Named-Regular completions Φ f
  sums-named-regular sums =
    collection-named-regular (global-collection sums)

  named-regular-sums :
    Named-Regular completions Φ f
    → Completed-Sums
        (completions (Stage (completed-codes completions Φ) (Tree.node X f))
          (decoding (completed-codes completions Φ) (Tree.node X f)))
  named-regular-sums named = global-sums (named-regular-collection named)

  -- A choice is bounded: the chosen children lie below one child, to
  -- which each name moves up.
  choice-named-regular :
    Children-Choice completions Φ f → Named-Regular completions Φ f
  choice-named-regular choice a B at =
    map-covered
      (λ g →
        pr₁
          (Regular.bound regular a
            (λ y′ → pr₁ (g y′) , pr₁ (pr₂ (g y′)))) ,
        (λ y →
          moved-at completions Φ H f (pr₁ (g y))
            (pr₁
              (Regular.bound regular a
                (λ y′ → pr₁ (g y′) , pr₁ (pr₂ (g y′)))))
            (⊏→⊑
              (pr₂
                (pr₂
                  (Regular.bound regular a
                    (λ y′ → pr₁ (g y′) , pr₁ (pr₂ (g y′)))))
                y))
            (B y) (pr₂ (g y))))
      (choice a B at)

------------------------------------------------------------------------
-- The rule with unique names from fans that bound merely named families

module _ {ℓ : Level} (H : Type-Hypotheses ℓ)
  (completions : Completions ℓ (Set ℓ))
  (M : Specification.Mahlo (Ambient.formers ℓ))
  where

  -- When the fan of the reflection of each operator's completed codes
  -- bounds merely named families, its global stage is a closure of the
  -- operator on a small type with unique names.
  unique-names-from-named-regular-fans :
    ((Φ : Ambient.Operator ℓ) →
      Named-Regular completions Φ
        (embed
          (Specification.Reflection.closure
            (Specification.Mahlo.reflect M (completed-codes completions Φ)))))
    → (Φ : Ambient.Operator ℓ)
    → Σ (Small-Closure (type-parent H) Φ)
        (λ L → Has-Unique-Names (type-parent H) (pr₂ L))
  unique-names-from-named-regular-fans named Φ =
    let L = Specification.Reflection.closure
              (Specification.Mahlo.reflect M (completed-codes completions Φ))
        t = Tree.node
              (W
                (Specification.Reflection.carrier
                  (Specification.Mahlo.reflect M
                    (completed-codes completions Φ)))
                (Specification.Closure.interpret L))
              (embed L)
        regular =
          trees-regular L (completed-codes completions Φ)
            (stage-name L (Type-Hypotheses.families H))
            (stage-name-β L (Type-Hypotheses.families H))
        sums = named-regular-sums completions Φ H regular (named Φ)
    in
    ( Completion.completed
        (completions (Stage (completed-codes completions Φ) t)
          (decoding (completed-codes completions Φ) t))
    , global-closure completions Φ H regular sums )
    , global-closure-has-unique-names completions Φ H regular sums

-- The passage from smallness to its form with unique names, when the fans
-- of the reflections of completed codes bound merely named families.
named-regular-passage : {ℓ : Level} (H : Type-Hypotheses ℓ)
  (completions : Completions ℓ (Set ℓ)) →
  ((small : Smallness ℓ) (Φ : Ambient.Operator ℓ) →
    Named-Regular completions Φ
      (embed
        (Specification.Reflection.closure
          (Specification.Mahlo.reflect
            (mahlo (Type-Hypotheses.families H) small)
            (completed-codes completions Φ))))) →
  Names-Passage ℓ
named-regular-passage H completions named small =
  smallness-of-reflector
    (reflector-of-unique-names H
      (unique-names-from-named-regular-fans H completions
        (mahlo (Type-Hypotheses.families H) small) (named small)))
