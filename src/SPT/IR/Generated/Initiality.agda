{-# OPTIONS --safe --without-K #-}

module SPT.IR.Generated.Initiality where

-- Pointwise initiality of the elimination of the generated part of an
-- algebra (Generated), with no extensionality: a valuation
-- with the lax law is related to induction at every element (`Lax`,
-- `ind-unique-rel`). Instances: the fundamental theorem (`ind-rel`),
-- uniqueness for congruent methods, whose equations induction satisfies
-- by refl (`ind-unique`, `ind-homomorphic`), and fusion (`ind-fusion`).
-- Hypotheses are one function on the positions, so extensionality there
-- makes every method congruent (`congruent`).
--
-- The derivations are the closed trees of the generated part's signature,
-- and `ind` is induction on them, so each theorem here is the theorem of
-- Foundation.Tree.Fold.Initiality at that signature: a law stated at a shape
-- is the law at its operation, and closed trees have no holes.

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Tree using (node)
import SPT.Foundation.Tree.Fold.Initiality as Trees

open import SPT.IR.Algebra using (Algebra)
open import SPT.IR.Description using (Desc; indexed; Shape)
open import SPT.IR.Generated using
  (apply; Der; G; Method; ind; no-hole; step)
open import SPT.IR.Restriction using (Position; input)

------------------------------------------------------------------------
-- Relational uniqueness

-- The lax law of a valuation v for methods m: at every operation, the
-- methods at any hypotheses related to v at the positions are related to
-- v at the operation's element. No reflexivity, transitivity or
-- congruence is asked. The proof is induction at the motive relating v to
-- induction: its hypotheses at an operation are the relatedness the law
-- asks for, at induction's own values. It is
-- Foundation.Tree.Fold.Initiality's `induction-unique-rel` at the
-- derivations.

module _
  {s κ j μ ν ρ : Level} {E : Set j} {γ : Desc {s = s} E} (M : Algebra κ γ)
  (Q : G M → Set μ) (P : G M → Set ν)
  (C : (g : G M) → Q g → P g → Set ρ)
  where

  open Algebra M using (K; value; operation)

  Lax : ((g : G M) → Q g) → Method M P → Set (s ⊔ κ ⊔ ν ⊔ ρ)
  Lax v m =
    (a : Shape γ (indexed K value))
    (xs :
      (p : Position γ (indexed K value) a)
      → Der M (input γ (indexed K value) a p))
    (k :
      (p : Position γ (indexed K value) a)
      → P (input γ (indexed K value) a p , xs p))
    → ( (p : Position γ (indexed K value) a)
        → C (input γ (indexed K value) a p , xs p)
            (v (input γ (indexed K value) a p , xs p)) (k p))
    → C (operation a , node (apply a) xs)
        (v (operation a , node (apply a) xs)) (m a xs k)

module _
  {s κ j μ ν ρ : Level} {E : Set j} {γ : Desc {s = s} E} (M : Algebra κ γ)
  (Q : G M → Set μ) (P : G M → Set ν)
  (C : (g : G M) → Q g → P g → Set ρ)
  (v : (g : G M) → Q g) (m : Method M P) (law : Lax M Q P C v m)
  where

  open Algebra M using (K)

  ind-unique-rel : (g : G M) → C g (v g) (ind M P m g)
  ind-unique-rel g =
    Trees.induction-unique-rel
      (λ (c : K) (d : Der M c) → Q (c , d))
      (λ (c : K) (d : Der M c) → P (c , d))
      (λ (c : K) (d : Der M c) → C (c , d))
      (λ {c} d → v (c , d))
      (no-hole M P) (step M P m)
      (record
        { at-hole = λ ()
        ; at-node = λ { (apply a) xs k r → law a xs k r }
        })
      (pr₂ g)

------------------------------------------------------------------------
-- The fundamental theorem

-- Methods related at related hypotheses have related inductions; the
-- values of an induction at the positions are its hypotheses there.

module _
  {s κ j μ ν ρ : Level} {E : Set j} {γ : Desc {s = s} E} (M : Algebra κ γ)
  (Q : G M → Set μ) (P : G M → Set ν)
  (C : (g : G M) → Q g → P g → Set ρ)
  (n : Method M Q) (m : Method M P)
  where

  open Algebra M using (K; value; operation)

  Relational : Set (s ⊔ κ ⊔ μ ⊔ ν ⊔ ρ)
  Relational =
    (a : Shape γ (indexed K value))
    (xs :
      (p : Position γ (indexed K value) a)
      → Der M (input γ (indexed K value) a p))
    (h :
      (p : Position γ (indexed K value) a)
      → Q (input γ (indexed K value) a p , xs p))
    (k :
      (p : Position γ (indexed K value) a)
      → P (input γ (indexed K value) a p , xs p))
    → ( (p : Position γ (indexed K value) a)
        → C (input γ (indexed K value) a p , xs p) (h p) (k p))
    → C (operation a , node (apply a) xs) (n a xs h) (m a xs k)

  ind-rel : Relational → (g : G M) → C g (ind M Q n g) (ind M P m g)
  ind-rel related g =
    Trees.induction-rel
      (λ (c : K) (d : Der M c) → Q (c , d))
      (λ (c : K) (d : Der M c) → P (c , d))
      (λ (c : K) (d : Der M c) → C (c , d))
      (no-hole M Q) (step M Q n) (no-hole M P) (step M P m)
      (record
        { at-hole = λ ()
        ; at-node = λ { (apply a) xs h k r → related a xs h k r }
        })
      (pr₂ g)

------------------------------------------------------------------------
-- Uniqueness

-- Methods are congruent when hypotheses agreeing at every position give
-- the same value; the hypotheses are functions on the positions, so this
-- is a genuine hypothesis. A valuation satisfying the computation
-- equations of congruent methods is their induction at every element, and
-- induction satisfies them by refl.

module _
  {s κ j ν : Level} {E : Set j} {γ : Desc {s = s} E} (M : Algebra κ γ)
  (P : G M → Set ν)
  where

  open Algebra M using (K; value; operation)

  Congruent : Method M P → Set (s ⊔ κ ⊔ ν)
  Congruent m =
    (a : Shape γ (indexed K value))
    (xs :
      (p : Position γ (indexed K value) a)
      → Der M (input γ (indexed K value) a p))
    (h k :
      (p : Position γ (indexed K value) a)
      → P (input γ (indexed K value) a p , xs p))
    → ((p : Position γ (indexed K value) a) → h p ＝ k p)
    → m a xs h ＝ m a xs k

  Homomorphic : ((g : G M) → P g) → Method M P → Set (s ⊔ κ ⊔ ν)
  Homomorphic v m =
    (a : Shape γ (indexed K value))
    (xs :
      (p : Position γ (indexed K value) a)
      → Der M (input γ (indexed K value) a p))
    → v (operation a , node (apply a) xs)
      ＝ m a xs (λ p → v (input γ (indexed K value) a p , xs p))

  ind-unique :
    (v : (g : G M) → P g) (m : Method M P) → Congruent m → Homomorphic v m
    → (g : G M) → v g ＝ ind M P m g
  ind-unique v m congruence equations g =
    Trees.induction-unique
      (λ (c : K) (d : Der M c) → P (c , d))
      (λ {c} d → v (c , d))
      (no-hole M P) (step M P m)
      (λ { (apply a) xs h k r → congruence a xs h k r })
      (record
        { at-hole = λ ()
        ; at-node = λ { (apply a) xs → equations a xs }
        })
      (pr₂ g)

  ind-homomorphic : (m : Method M P) → Homomorphic (ind M P m) m
  ind-homomorphic m a xs = refl

------------------------------------------------------------------------
-- Congruence under extensionality

-- Under extensionality for families over the positions, hypotheses
-- agreeing at every position are identical, so every method is congruent.

module _
  {s κ j ν : Level} {E : Set j} {γ : Desc {s = s} E}
  (extensionality : (A : Set s) (Y : A → Set ν) → FunExt A Y)
  (M : Algebra κ γ) (P : G M → Set ν)
  where

  open Algebra M using (K)

  congruent : (m : Method M P) → Congruent M P m
  congruent m a xs h k r =
    Trees.congruent extensionality
      (λ (c : K) (d : Der M c) → P (c , d))
      (step M P m) (apply a) xs h k r

------------------------------------------------------------------------
-- Fusion

-- A map of motives that carries the methods of one to congruent methods
-- of the other, at the mapped hypotheses, carries induction to induction:
-- the two are related by the graph of the map.

module _
  {s κ j ν ν′ : Level} {E : Set j} {γ : Desc {s = s} E} (M : Algebra κ γ)
  (P : G M → Set ν) (P′ : G M → Set ν′) (f : (g : G M) → P g → P′ g)
  where

  open Algebra M using (K; value; operation)

  Carries : Method M P → Method M P′ → Set (s ⊔ κ ⊔ ν ⊔ ν′)
  Carries m m′ =
    (a : Shape γ (indexed K value))
    (xs :
      (p : Position γ (indexed K value) a)
      → Der M (input γ (indexed K value) a p))
    (h :
      (p : Position γ (indexed K value) a)
      → P (input γ (indexed K value) a p , xs p))
    → f (operation a , node (apply a) xs) (m a xs h)
      ＝ m′ a xs (λ p → f (input γ (indexed K value) a p , xs p) (h p))

  ind-fusion :
    (m : Method M P) (m′ : Method M P′) → Congruent M P′ m′ → Carries m m′
    → (g : G M) → f g (ind M P m g) ＝ ind M P′ m′ g
  ind-fusion m m′ congruence carries g =
    Trees.induction-fusion
      (λ (c : K) (d : Der M c) → P (c , d))
      (λ (c : K) (d : Der M c) → P′ (c , d))
      (λ {c} d → f (c , d))
      (no-hole M P) (step M P m) (no-hole M P′) (step M P′ m′)
      (λ { (apply a) xs h k r → congruence a xs h k r })
      (record
        { at-hole = λ ()
        ; at-node = λ { (apply a) xs k → carries a xs k }
        })
      (pr₂ g)

-- Initiality among algebras is Morphism.Initiality: morphisms keep a code
-- together with its decoding identification, and the morphisms out of the
-- generated part form a contractible type. It goes through induction on
-- source arguments (Foundation.Induction.Initiality), since a morphism's
-- law is stated at introductions, not at layers.
