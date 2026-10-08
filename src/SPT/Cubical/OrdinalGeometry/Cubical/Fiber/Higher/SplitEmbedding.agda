{-# OPTIONS --safe --cubical --guardedness #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.Cubical.Fiber.Higher.SplitEmbedding
  where

-- Split embeddings A ◁ B (an inclusion with a recovery map and a pointwise
-- recovery law) and their action on identity types.  No ordinal appears;
-- the module is separate so that each lifting computation is checked once.

open import Agda.Primitive using (Level; _⊔_)

import Cubical.Foundations.GroupoidLaws as Groupoid
import Cubical.Foundations.Prelude as Cubical
import Cubical.Foundations.Transport as Transport

private
  variable
    ℓ-A ℓ-B ℓ-C : Level
    A : Set ℓ-A
    B : Set ℓ-B
    C : Set ℓ-C

------------------------------------------------------------------------
-- Split embeddings

--   SplitEmbedding(A,B) = Σ(include : A → B). Σ(recover : B → A).
--                           Π a. recover(include(a)) = a.
--
-- It need not be an equivalence.

record SplitEmbedding
    (A : Set ℓ-A)
    (B : Set ℓ-B)
    : Set (ℓ-A ⊔ ℓ-B) where
  constructor split-embedding
  field
    include : A → B
    recover : B → A
    recover-include : (point : A) → recover (include point) Cubical.≡ point

open SplitEmbedding public

splitEmbedding-injective :
    (embedding : SplitEmbedding A B)
    (left right : A)
  → include embedding left Cubical.≡ include embedding right
  → left Cubical.≡ right
splitEmbedding-injective embedding left right image-path =
  Cubical.sym (recover-include embedding left)
  Cubical.∙
  Cubical.cong (recover embedding) image-path
  Cubical.∙
  recover-include embedding right

identitySplitEmbedding : SplitEmbedding A A
identitySplitEmbedding =
  split-embedding
    (λ point → point)
    (λ point → point)
    (λ point → Cubical.refl)

composeSplitEmbedding :
    SplitEmbedding A B
  → SplitEmbedding B C
  → SplitEmbedding A C
composeSplitEmbedding first second =
  split-embedding
    (λ point → include second (include first point))
    (λ point → recover first (recover second point))
    (λ point →
      Cubical.cong
        (recover first)
        (recover-include second (include first point))
      Cubical.∙
      recover-include first point)

------------------------------------------------------------------------
-- Path algebra for the identity lift

cong-compose :
    (first : A → B)
    (second : B → C)
    {left right : A}
    (path : left Cubical.≡ right)
  → Cubical.cong second (Cubical.cong first path)
      Cubical.≡
    Cubical.cong (λ point → second (first point)) path
cong-compose first second {left} =
  Cubical.J
    (λ right path →
      Cubical.cong second (Cubical.cong first path)
        Cubical.≡
      Cubical.cong (λ point → second (first point)) path)
    Cubical.refl

retraction-homotopy-naturality :
    (embedding : SplitEmbedding A B)
    {left right : A}
    (path : left Cubical.≡ right)
  → Cubical.cong
      (λ point → recover embedding (include embedding point))
      path
      Cubical.∙
      recover-include embedding right
      Cubical.≡
    recover-include embedding left Cubical.∙ path
retraction-homotopy-naturality embedding {left} =
  Cubical.J
    (λ right path →
      Cubical.cong
        (λ point → recover embedding (include embedding point))
        path
        Cubical.∙
        recover-include embedding right
        Cubical.≡
      recover-include embedding left Cubical.∙ path)
    (Cubical.sym
      (Groupoid.lUnit (recover-include embedding left))
    Cubical.∙
    Groupoid.rUnit (recover-include embedding left))

sym-left-cancel :
    {left middle right : A}
    (first : left Cubical.≡ middle)
    (second : middle Cubical.≡ right)
  → Cubical.sym first Cubical.∙ (first Cubical.∙ second)
      Cubical.≡ second
sym-left-cancel first second =
  Groupoid.assoc (Cubical.sym first) first second
  Cubical.∙
  Cubical.cong (λ path → path Cubical.∙ second)
    (Groupoid.lCancel first)
  Cubical.∙
  Cubical.sym (Groupoid.lUnit second)

liftPathInclude :
    (embedding : SplitEmbedding A B)
    {left right : A}
  → left Cubical.≡ right
  → include embedding left Cubical.≡ include embedding right
liftPathInclude embedding = Cubical.cong (include embedding)

liftPathRecover :
    (embedding : SplitEmbedding A B)
    {left right : A}
  → include embedding left Cubical.≡ include embedding right
  → left Cubical.≡ right
liftPathRecover embedding {left} {right} path =
  Cubical.sym (recover-include embedding left)
  Cubical.∙
  (Cubical.cong (recover embedding) path
  Cubical.∙
  recover-include embedding right)

liftPathRecover-include :
    (embedding : SplitEmbedding A B)
    {left right : A}
    (path : left Cubical.≡ right)
  → liftPathRecover embedding (liftPathInclude embedding path)
      Cubical.≡ path
liftPathRecover-include embedding {left} {right} path =
  Cubical.cong
    (λ reflected →
      Cubical.sym (recover-include embedding left)
      Cubical.∙
      (reflected Cubical.∙ recover-include embedding right))
    (cong-compose (include embedding) (recover embedding) path)
  Cubical.∙
  Cubical.cong
    (λ tail →
      Cubical.sym (recover-include embedding left) Cubical.∙ tail)
    (retraction-homotopy-naturality embedding path)
  Cubical.∙
  sym-left-cancel (recover-include embedding left) path

-- A split embedding of endpoints gives one of identity types,
--
--   (x = y) ◁ (include(x) = include(y)),
--
-- recovering through the recovery paths at both ends.

liftPathSplitEmbedding :
    (embedding : SplitEmbedding A B)
    (left right : A)
  → SplitEmbedding
      (left Cubical.≡ right)
      (include embedding left Cubical.≡ include embedding right)
liftPathSplitEmbedding embedding left right =
  split-embedding
    (liftPathInclude embedding)
    (liftPathRecover embedding)
    (liftPathRecover-include embedding)

------------------------------------------------------------------------
-- Rebase a loop space along one path

subst-back-forth :
    (family : A → Set ℓ-B)
    {left right : A}
    (path : left Cubical.≡ right)
    (point : family left)
  → Cubical.subst family (Cubical.sym path)
      (Cubical.subst family path point)
      Cubical.≡ point
subst-back-forth family {left} =
  λ path point →
    Cubical.sym
      (Transport.substComposite
        family path (Cubical.sym path) point)
    Cubical.∙
    Cubical.cong
      (λ loop → Cubical.subst family loop point)
      (Groupoid.rCancel path)
    Cubical.∙
    Cubical.substRefl {B = family} point

rebaseLoopSplitEmbedding :
    {left right : A}
  → left Cubical.≡ right
  → SplitEmbedding
      (left Cubical.≡ left)
      (right Cubical.≡ right)
rebaseLoopSplitEmbedding {A = A} {left} {right} path =
  split-embedding
    (Cubical.subst (λ point → point Cubical.≡ point) path)
    (Cubical.subst
      (λ point → point Cubical.≡ point)
      (Cubical.sym path))
    (subst-back-forth
      (λ point → point Cubical.≡ point)
      path)

rebaseLoopSplitEmbedding-refl :
    {left right : A}
    (path : left Cubical.≡ right)
  → include (rebaseLoopSplitEmbedding path) Cubical.refl
      Cubical.≡ Cubical.refl
rebaseLoopSplitEmbedding-refl {A = A} {left} =
  Cubical.J
    (λ right path →
      include (rebaseLoopSplitEmbedding path)
        (Cubical.refl {x = left})
        Cubical.≡
      Cubical.refl {x = right})
    (Cubical.substRefl
      {B = λ point → point Cubical.≡ point}
      Cubical.refl)
