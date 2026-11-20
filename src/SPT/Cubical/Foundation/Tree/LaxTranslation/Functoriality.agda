{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Tree.LaxTranslation.Functoriality where

-- Identity, composition and substitution laws for the actions of lax
-- translations on open trees: structural cells `TreeRel _＝_`, and
-- identifications under extensionality for the children of nodes.
--
-- * Transport along a judgment path preserves `TreeRel _＝_`, and
--   substitution and the tree action commute with transport
--   (`tree-rel-equality-transport`, `bind-transport`,
--   `map-lax-tree-transport`):
--
--     map-lax-tree τ h (transport e t)
--       ＝ transport (ap f e) (map-lax-tree τ h t).
--
-- * The identity translation acts trivially, and a composite acts as the
--   composite of the actions (`map-lax-tree-identity-rel`,
--   `map-lax-tree-composition-rel`):
--
--     map-lax-tree id (λ i x → x) t ∼ t,
--     map-lax-tree (υ ∘ τ) (h₂ ∘ h₁) t
--       ∼ map-lax-tree υ h₂ (map-lax-tree τ h₁ t).
--
--   At every target position the cell of the children is transported
--   along the composite boundary path ap g d ∙ e, and the two transports
--   on the right are aligned pointwise.
-- * A substitution k of source trees gives one of reindexed trees: the
--   source judgment and payload retained by a reindexed hole select their
--   replacement, and its path places the reindexed replacement
--   (`reindexed-replacement`). Reindexing commutes with substitution
--   (`reindex-tree-bind-rel`):
--
--     reindex-tree τ (bind k t)
--       ∼ bind (reindexed-replacement τ k) (reindex-tree τ t).
--
-- * Under `ChildΠExt` of the target, passed explicitly, the three cells
--   are identifications (`map-lax-tree-identity`,
--   `map-lax-tree-composition`, `reindex-tree-bind`).
--
-- No identification of translations, boundary paths or child functions is
-- supplied, nor a target substitution law for a hole action that has
-- forgotten its source payload.
--
-- Along an identification of judgments, transport keeps the structural
-- relation (`tree-rel-equality-transport`) and commutes with bind
-- (`bind-transport`), over any signature, and with lax translation along
-- the image of the identification (`map-lax-tree-transport`). The target
-- hole families are explicit, as in `map-lax-tree`.

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Signature using (Signature; Judgment)
open import SPT.Cubical.Foundation.Signature.Sum
  using (Signature-Over; to-signature)
open import SPT.Cubical.Foundation.Signature.LaxTranslation using
  ( Lax-Signature-Translation; map-lax-operation; project-lax-position
  ; lax-boundary-coherence; identity-lax-signature-translation
  ; compose-lax-signature-translation )
open import SPT.Cubical.Foundation.Tree using (Tree; hole; node)
open import SPT.Cubical.Foundation.Tree.Relation using
  (TreeRel; hole-rel; node-rel; rel-refl; ChildΠExt; module Extensional)
open import SPT.Cubical.Foundation.Tree.Substitution using (bind)
open import SPT.Cubical.Foundation.Tree.LaxTranslation using
  (Reindexed-Hole; reindex-tree; map-lax-tree)

------------------------------------------------------------------------
-- Transport along judgment paths

module _ {ℓj ℓo ℓp ℓx : Level} {S : Signature ℓj ℓo ℓp}
  {X : Judgment S → Set ℓx} where

  tree-rel-equality-transport : {left-judgment right-judgment : Judgment S}
    (judgment-path : left-judgment ＝ right-judgment)
    {left right : Tree S X left-judgment} →
    TreeRel _＝_ left right →
    TreeRel _＝_ (transport (Tree S X) judgment-path left)
      (transport (Tree S X) judgment-path right)
  tree-rel-equality-transport refl related = related

module _ {ℓj ℓo ℓp ℓx ℓy : Level} {S : Signature ℓj ℓo ℓp}
  {X : Judgment S → Set ℓx} {Y : Judgment S → Set ℓy} where

  bind-transport :
    (replacement : (judgment : Judgment S) → X judgment →
      Tree S Y judgment)
    {left-judgment right-judgment : Judgment S}
    (judgment-path : left-judgment ＝ right-judgment)
    (tree : Tree S X left-judgment) →
    bind replacement (transport (Tree S X) judgment-path tree)
      ＝ transport (Tree S Y) judgment-path (bind replacement tree)
  bind-transport replacement refl tree = refl

module _ {ℓj₁ ℓo₁ ℓp₁ ℓj₂ ℓo₂ ℓp₂ : Level} {Source-Judgment : Set ℓj₁}
  {Target-Judgment : Set ℓj₂}
  {on-judgment : Source-Judgment → Target-Judgment}
  {source : Signature-Over Source-Judgment ℓo₁ ℓp₁}
  {target : Signature-Over Target-Judgment ℓo₂ ℓp₂}
  (translation : Lax-Signature-Translation on-judgment source target) where

  map-lax-tree-transport : {ℓx ℓy : Level} {X : Source-Judgment → Set ℓx}
    (Y : Target-Judgment → Set ℓy)
    (on-hole : (source-judgment : Source-Judgment) → X source-judgment →
      Y (on-judgment source-judgment))
    {left-judgment right-judgment : Source-Judgment}
    (judgment-path : left-judgment ＝ right-judgment)
    (tree : Tree (to-signature source) X left-judgment) →
    map-lax-tree translation Y on-hole
      (transport (Tree (to-signature source) X) judgment-path tree)
      ＝ transport (Tree (to-signature target) Y)
        (ap on-judgment judgment-path)
        (map-lax-tree translation Y on-hole tree)
  map-lax-tree-transport Y on-hole refl tree = refl

------------------------------------------------------------------------
-- The identity translation

module _ {ℓj ℓo ℓp ℓx : Level} {J : Set ℓj}
  (signature : Signature-Over J ℓo ℓp) {X : J → Set ℓx} where

  map-lax-tree-identity-rel : {judgment : J}
    (tree : Tree (to-signature signature) X judgment) →
    TreeRel _＝_
      (map-lax-tree (identity-lax-signature-translation signature) X
        (λ source-judgment source-hole → source-hole) tree)
      tree
  map-lax-tree-identity-rel (hole source-hole) = hole-rel refl
  map-lax-tree-identity-rel (node source-operation source-child) =
    node-rel (λ source-position →
      map-lax-tree-identity-rel (source-child source-position))

  map-lax-tree-identity : ChildΠExt (to-signature signature) X →
    {judgment : J} (tree : Tree (to-signature signature) X judgment) →
    map-lax-tree (identity-lax-signature-translation signature) X
      (λ source-judgment source-hole → source-hole) tree
      ＝ tree
  map-lax-tree-identity πext tree =
    Extensional.equality πext
      (map-lax-tree (identity-lax-signature-translation signature) X
        (λ source-judgment source-hole → source-hole) tree)
      tree (map-lax-tree-identity-rel tree)

------------------------------------------------------------------------
-- Composite translations

module _ {ℓj₁ ℓo₁ ℓp₁ ℓj₂ ℓo₂ ℓp₂ ℓj₃ ℓo₃ ℓp₃ ℓx ℓy ℓz : Level}
  {Judgment₁ : Set ℓj₁} {Judgment₂ : Set ℓj₂} {Judgment₃ : Set ℓj₃}
  {on-judgment₁ : Judgment₁ → Judgment₂}
  {on-judgment₂ : Judgment₂ → Judgment₃}
  {source : Signature-Over Judgment₁ ℓo₁ ℓp₁}
  {middle : Signature-Over Judgment₂ ℓo₂ ℓp₂}
  {target : Signature-Over Judgment₃ ℓo₃ ℓp₃}
  (first : Lax-Signature-Translation on-judgment₁ source middle)
  (second : Lax-Signature-Translation on-judgment₂ middle target)
  {X : Judgment₁ → Set ℓx} (Y : Judgment₂ → Set ℓy)
  (Z : Judgment₃ → Set ℓz)
  (first-hole : (judgment : Judgment₁) → X judgment →
    Y (on-judgment₁ judgment))
  (second-hole : (judgment : Judgment₂) → Y judgment →
    Z (on-judgment₂ judgment)) where

  -- At every target position the cell of the children is transported
  -- along the composite boundary path; on the right, transport along it
  -- splits, and the second action moves the first transport inside.

  map-lax-tree-composition-rel : {source-judgment : Judgment₁}
    (tree : Tree (to-signature source) X source-judgment) →
    TreeRel _＝_
      (map-lax-tree (compose-lax-signature-translation first second) Z
        (λ judgment source-hole →
          second-hole (on-judgment₁ judgment)
            (first-hole judgment source-hole))
        tree)
      (map-lax-tree second Z second-hole
        (map-lax-tree first Y first-hole tree))
  map-lax-tree-composition-rel (hole source-hole) = hole-rel refl
  map-lax-tree-composition-rel (node source-operation source-child) =
    node-rel (λ target-position →
      let
        middle-position =
          project-lax-position second
            (map-lax-operation first source-operation) target-position
        source-position =
          project-lax-position first source-operation middle-position
        first-path =
          lax-boundary-coherence first source-operation middle-position
        second-path =
          lax-boundary-coherence second
            (map-lax-operation first source-operation) target-position
        first-child =
          map-lax-tree first Y first-hole (source-child source-position)
      in
      transport
        (TreeRel _＝_
          (transport (Tree (to-signature target) Z)
            (ap on-judgment₂ first-path ∙ second-path)
            (map-lax-tree (compose-lax-signature-translation first second) Z
              (λ judgment source-hole →
                second-hole (on-judgment₁ judgment)
                  (first-hole judgment source-hole))
              (source-child source-position))))
        (transport-∙ (Tree (to-signature target) Z)
          (ap on-judgment₂ first-path) second-path
          (map-lax-tree second Z second-hole first-child)
          ∙ ap (transport (Tree (to-signature target) Z) second-path)
            (map-lax-tree-transport second Z second-hole first-path
              first-child ⁻¹))
        (tree-rel-equality-transport
          (ap on-judgment₂ first-path ∙ second-path)
          (map-lax-tree-composition-rel (source-child source-position))))

  map-lax-tree-composition : ChildΠExt (to-signature target) Z →
    {source-judgment : Judgment₁}
    (tree : Tree (to-signature source) X source-judgment) →
    map-lax-tree (compose-lax-signature-translation first second) Z
      (λ judgment source-hole →
        second-hole (on-judgment₁ judgment)
          (first-hole judgment source-hole))
      tree
      ＝ map-lax-tree second Z second-hole
        (map-lax-tree first Y first-hole tree)
  map-lax-tree-composition πext tree =
    Extensional.equality πext
      (map-lax-tree (compose-lax-signature-translation first second) Z
        (λ judgment source-hole →
          second-hole (on-judgment₁ judgment)
            (first-hole judgment source-hole))
        tree)
      (map-lax-tree second Z second-hole
        (map-lax-tree first Y first-hole tree))
      (map-lax-tree-composition-rel tree)

------------------------------------------------------------------------
-- Substitution and reindexing

module _ {ℓj₁ ℓo₁ ℓp₁ ℓj₂ ℓo₂ ℓp₂ ℓx ℓy : Level}
  {Source-Judgment : Set ℓj₁} {Target-Judgment : Set ℓj₂}
  {on-judgment : Source-Judgment → Target-Judgment}
  {source : Signature-Over Source-Judgment ℓo₁ ℓp₁}
  {target : Signature-Over Target-Judgment ℓo₂ ℓp₂}
  (translation : Lax-Signature-Translation on-judgment source target)
  {X : Source-Judgment → Set ℓx} {Y : Source-Judgment → Set ℓy} where

  -- The retained source judgment and payload select the replacement; the
  -- retained path places its reindexed tree in the target fiber. No
  -- inverse of a hole action is used.

  reindexed-replacement :
    ((source-judgment : Source-Judgment) → X source-judgment →
      Tree (to-signature source) Y source-judgment) →
    (target-judgment : Target-Judgment) →
    Reindexed-Hole on-judgment X target-judgment →
    Tree (to-signature target) (Reindexed-Hole on-judgment Y)
      target-judgment
  reindexed-replacement replacement target-judgment
    (source-judgment , source-hole , judgment-path) =
    transport (Tree (to-signature target) (Reindexed-Hole on-judgment Y))
      judgment-path
      (reindex-tree translation (replacement source-judgment source-hole))

  -- Both routes keep the mapped operation at every node; at a hole the
  -- right route consumes the retained source judgment and payload, and at
  -- a node the cell of the children is transported along the boundary
  -- path both routes use.

  reindex-tree-bind-rel :
    (replacement : (source-judgment : Source-Judgment) →
      X source-judgment → Tree (to-signature source) Y source-judgment)
    {source-judgment : Source-Judgment}
    (tree : Tree (to-signature source) X source-judgment) →
    TreeRel _＝_ (reindex-tree translation (bind replacement tree))
      (bind (reindexed-replacement replacement)
        (reindex-tree translation tree))
  reindex-tree-bind-rel replacement (hole {source-judgment} source-hole) =
    rel-refl (λ target-hole → refl)
      (reindex-tree translation (replacement source-judgment source-hole))
  reindex-tree-bind-rel replacement (node source-operation source-child) =
    node-rel (λ target-position →
      let
        source-position =
          project-lax-position translation source-operation target-position
        boundary-path =
          lax-boundary-coherence translation source-operation target-position
      in
      transport
        (TreeRel _＝_
          (transport
            (Tree (to-signature target) (Reindexed-Hole on-judgment Y))
            boundary-path
            (reindex-tree translation
              (bind replacement (source-child source-position)))))
        (bind-transport (reindexed-replacement replacement) boundary-path
          (reindex-tree translation (source-child source-position)) ⁻¹)
        (tree-rel-equality-transport boundary-path
          (reindex-tree-bind-rel replacement
            (source-child source-position))))

  reindex-tree-bind :
    ChildΠExt (to-signature target) (Reindexed-Hole on-judgment Y) →
    (replacement : (source-judgment : Source-Judgment) →
      X source-judgment → Tree (to-signature source) Y source-judgment)
    {source-judgment : Source-Judgment}
    (tree : Tree (to-signature source) X source-judgment) →
    reindex-tree translation (bind replacement tree)
      ＝ bind (reindexed-replacement replacement)
        (reindex-tree translation tree)
  reindex-tree-bind πext replacement tree =
    Extensional.equality πext
      (reindex-tree translation (bind replacement tree))
      (bind (reindexed-replacement replacement)
        (reindex-tree translation tree))
      (reindex-tree-bind-rel replacement tree)
