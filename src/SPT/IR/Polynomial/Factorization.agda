{-# OPTIONS --safe --without-K #-}

module SPT.IR.Polynomial.Factorization where

-- Arguments over a union of stages lie in one stage. The stages carry a
-- preorder with joins and bounds of families indexed by small types
-- (`Stages`), and each element of the union carries its stage (`rank`).
-- An argument lies in a stage when the inputs at its positions do
-- (`Within`); a code is bounded at a stage when its paths over every later
-- stage that stop at a product's arity request small types (`Over`,
-- `Arity`, `Bounded`). Every argument of a bounded code then lies in one
-- stage (`factor`, `onto`): Lemma 4.3 of IndexedUniversalIR.md, with the
-- argument and its information kept, so no continuation is moved.

open import SPT.Base

open import SPT.IR.Polynomial using
  (Poly; var; con; sigma; pi; Family; carrier; Args; info; Scheme; shape)
import SPT.IR.Polynomial.Frontier as Frontier
open import SPT.IR.Polynomial.Generated using
  (Position; input; both; nowhere)

------------------------------------------------------------------------
-- Stages

-- The stages below a regular height: a preorder with a join of two stages
-- and a bound for every family of stages indexed by a small type. In the
-- simplicial model the stages are the ordinals below λ, the small types
-- those with fewer than λ simplices, and λ's regularity gives `bound`.
-- Nonclaim: the bound is a function, not a mere existence, as in
-- Heights/Regular's `bound`; from a merely existing bound the product case
-- below would need choice over the arity.

record Stages (ℓ σ : Level) : Set (lsuc (ℓ ⊔ σ)) where
  field
    Stage : Set σ
    _⊑_ : Stage → Stage → Set σ
    ⊑-refl : (s : Stage) → s ⊑ s
    ⊑-trans : {s t u : Stage} → s ⊑ t → t ⊑ u → s ⊑ u
    join : Stage → Stage → Stage
    join-left : (s t : Stage) → s ⊑ join s t
    join-right : (s t : Stage) → t ⊑ join s t
    Small : Set ℓ → Set σ
    bound : (A : Set ℓ) → Small A → (A → Stage) → Stage
    bound-above :
      (A : Set ℓ) (n : Small A) (f : A → Stage) (x : A)
      → f x ⊑ bound A n f

------------------------------------------------------------------------
-- Paths that stop at an arity

-- A path of a code stops at a product's arity, not at a recursive input or
-- at a constant. Only these requests are bounded: a constant may be large.

module _
  {ι ℓ κ : Level} {I : Set ι} {D : I → Set (ℓ ⊔ κ)} (Z : Family ℓ κ D)
  where

  Arity : {X : Set (ℓ ⊔ κ)} (p : Poly ℓ κ D X) → Frontier.Path p Z → Set
  Arity (var i) z = 𝟘
  Arity (con A) z = 𝟘
  Arity (sigma p q) (inl z) = Arity p z
  Arity (sigma p q) (inr (a , z)) = Arity (q (info p Z a)) z
  Arity (pi A p) (inl z) = 𝟙
  Arity (pi A p) (inr (a , z)) = Arity (p a) z

------------------------------------------------------------------------
-- Arguments and paths over a stage

-- An argument lies in stage γ when the input at each of its positions
-- does; then it lies in every later stage (`later`). A path lies over δ
-- when every complete first argument it passes lies in δ. A code is
-- bounded at β when every path over a stage δ above β that stops at an
-- arity requests a small type: the arities that its contexts over δ reach.

module _
  {ι ℓ κ σ : Level} {I : Set ι} {D : I → Set (ℓ ⊔ κ)} (S : Stages ℓ σ)
  (Z : Family ℓ κ D) (rank : Σ I (carrier Z) → Stages.Stage S)
  where

  open Stages S using
    ( Stage; _⊑_; ⊑-refl; ⊑-trans; join; join-left; join-right; Small
    ; bound; bound-above)

  Within :
    {X : Set (ℓ ⊔ κ)} → Stage → (p : Poly ℓ κ D X) → Args p Z
    → Set (ℓ ⊔ σ)
  Within γ p a = (z : Position p Z a) → rank (input p Z a z) ⊑ γ

  later :
    {X : Set (ℓ ⊔ κ)} (γ δ : Stage) (p : Poly ℓ κ D X) (a : Args p Z)
    → Within γ p a → γ ⊑ δ → Within δ p a
  later γ δ p a w e z = ⊑-trans (w z) e

  Over :
    {X : Set (ℓ ⊔ κ)} → Stage → (p : Poly ℓ κ D X) → Frontier.Path p Z
    → Set (ℓ ⊔ σ)
  Over δ (var i) z = Lift (ℓ ⊔ σ) 𝟙
  Over δ (con A) z = Lift (ℓ ⊔ σ) 𝟙
  Over δ (sigma p q) (inl z) = Over δ p z
  Over δ (sigma p q) (inr (a , z)) =
    Within δ p a × Over δ (q (info p Z a)) z
  Over δ (pi A p) (inl z) = Lift (ℓ ⊔ σ) 𝟙
  Over δ (pi A p) (inr (a , z)) = Over δ (p a) z

  Bounded : {X : Set (ℓ ⊔ κ)} → Stage → Poly ℓ κ D X → Set (ℓ ⊔ σ)
  Bounded β p =
    (δ : Stage) → β ⊑ δ → (z : Frontier.Path p Z) → Over δ p z
    → Arity Z p z → Small (Frontier.requested p Z z)

  -- An argument with a stage above β that it lies in.
  record Factored {X : Set (ℓ ⊔ κ)} (β : Stage) (p : Poly ℓ κ D X)
    (a : Args p Z) : Set (ℓ ⊔ σ) where
    field
      stage : Stage
      above : β ⊑ stage
      within : Within stage p a

------------------------------------------------------------------------
-- Boundedness along a code

  -- Boundedness passes to a sum's first part, to its continuation past a
  -- first argument lying in a stage above β, and to a product's
  -- components; a product's own arity is small.

  first :
    {X : Set (ℓ ⊔ κ)} {Y : X → Set (ℓ ⊔ κ)} (β : Stage)
    (p : Poly ℓ κ D X) (q : (x : X) → Poly ℓ κ D (Y x))
    → Bounded β (sigma p q) → Bounded β p
  first β p q h δ e z o t = h δ e (inl z) o t

  past :
    {X : Set (ℓ ⊔ κ)} {Y : X → Set (ℓ ⊔ κ)} (β : Stage)
    (p : Poly ℓ κ D X) (q : (x : X) → Poly ℓ κ D (Y x))
    → Bounded β (sigma p q) → (a : Args p Z) (u : Factored β p a)
    → Bounded (Factored.stage u) (q (info p Z a))
  past β p q h a u δ e z o t =
    h δ (⊑-trans (Factored.above u) e) (inr (a , z))
      ( later (Factored.stage u) δ p a (Factored.within u) e , o) t

  component :
    (β : Stage) (A : Set ℓ) {W : A → Set (ℓ ⊔ κ)}
    (p : (x : A) → Poly ℓ κ D (W x))
    → Bounded β (pi A p) → (x : A) → Bounded β (p x)
  component β A p h x δ e z o t = h δ e (inr (x , z)) o t

  arity :
    (β : Stage) (A : Set ℓ) {W : A → Set (ℓ ⊔ κ)}
    (p : (x : A) → Poly ℓ κ D (W x))
    → Bounded β (pi A p) → Small A
  arity β A p h = h β (⊑-refl β) (inl (lift ⋆)) (lift ⋆) ⋆

------------------------------------------------------------------------
-- The factorization

  -- A pair lies in its second part's stage, which lies above the first
  -- part's; a function lies in the bound of its components' stages.

  paired :
    {X : Set (ℓ ⊔ κ)} {Y : X → Set (ℓ ⊔ κ)} (β : Stage)
    (p : Poly ℓ κ D X) (q : (x : X) → Poly ℓ κ D (Y x))
    (a : Args p Z) (b : Args (q (info p Z a)) Z) (u : Factored β p a)
    → Factored (Factored.stage u) (q (info p Z a)) b
    → Factored β (sigma p q) (a , b)
  paired β p q a b u v = record
    { stage = Factored.stage v
    ; above = ⊑-trans (Factored.above u) (Factored.above v)
    ; within =
        both
          ( λ z →
              rank (input (sigma p q) Z (a , b) z) ⊑ Factored.stage v)
          ( λ z → ⊑-trans (Factored.within u z) (Factored.above v))
          ( Factored.within v)
    }

  gathered :
    (β : Stage) (A : Set ℓ) {W : A → Set (ℓ ⊔ κ)}
    (p : (x : A) → Poly ℓ κ D (W x)) (f : (x : A) → Args (p x) Z)
    (n : Small A) → ((x : A) → Factored β (p x) (f x))
    → Factored β (pi A p) f
  gathered β A p f n u = record
    { stage = join β (bound A n (λ x → Factored.stage (u x)))
    ; above = join-left β (bound A n (λ x → Factored.stage (u x)))
    ; within = λ w →
        ⊑-trans (Factored.within (u (pr₁ w)) (pr₂ w))
          ( ⊑-trans
              ( bound-above A n (λ x → Factored.stage (u x)) (pr₁ w))
              ( join-right β (bound A n (λ x → Factored.stage (u x)))))
    }

  -- By induction on the code. A recursive input lies in its own stage; a
  -- sum's first argument is factored first, and the path past it lies over
  -- that stage, so its continuation, selected by the first argument's
  -- information over the union, is factored above it; a product's arity
  -- is small, so its components' stages have a bound.
  factor :
    {X : Set (ℓ ⊔ κ)} (β : Stage) (p : Poly ℓ κ D X) → Bounded β p
    → (a : Args p Z) → Factored β p a
  factor β (var i) h a = record
    { stage = join β (rank (i , a))
    ; above = join-left β (rank (i , a))
    ; within = λ z → join-right β (rank (i , a))
    }
  factor β (con A) h a = record
    { stage = β
    ; above = ⊑-refl β
    ; within = nowhere (λ z → rank (input (con A) Z a z) ⊑ β)
    }
  factor β (sigma p q) h (a , b) =
    paired β p q a b (factor β p (first β p q h) a)
      ( factor (Factored.stage (factor β p (first β p q h) a))
          (q (info p Z a))
          (past β p q h a (factor β p (first β p q h) a))
          b)
  factor β (pi A p) h f =
    gathered β A p f (arity β A p h)
      (λ x → factor β (p x) (component β A p h x) (f x))

------------------------------------------------------------------------
-- Rules bounded at every stage

-- A scheme grows boundedly when its rooted paths over every stage request
-- small arities. Then every argument of each of its rules over the union
-- lies in one stage above any given one (`onto`): read in the simplicial
-- model, the comparison map from the union of the steps at the stages to
-- the step at the union is onto.

module _
  {ℓ κ σ : Level} (S : Stages ℓ σ) (s : Scheme ℓ κ)
  (Z : Family ℓ κ (Scheme.Data s))
  (rank : Σ (Scheme.Index s) (carrier Z) → Stages.Stage S)
  where

  open Scheme s using (Index; rule)
  open Stages S using (Stage; Small)

  Growth : Set (ℓ ⊔ σ)
  Growth =
    (i : Index) (δ : Stage) (z : Frontier.Path (shape (rule i)) Z)
    → Over S Z rank δ (shape (rule i)) z → Arity Z (shape (rule i)) z
    → Small (Frontier.requested (shape (rule i)) Z z)

  onto :
    Growth → (β : Stage) (i : Index) (u : Args (shape (rule i)) Z)
    → Factored S Z rank β (shape (rule i)) u
  onto g β i u =
    factor S Z rank β (shape (rule i)) (λ δ e z o t → g i δ z o t) u
