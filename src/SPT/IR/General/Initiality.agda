{-# OPTIONS --safe --without-K #-}

module SPT.IR.General.Initiality where

-- Pointwise initiality of Dybjer–Setzer's elimination rule for general
-- indexed induction–recursion (IR.General), once for every inductive
-- family whose own induction has pointwise initiality
-- (`Pointwise-Initiality`, a record: a lifting of relations to the
-- hypotheses at a located argument, the hypotheses a valuation supplies
-- there, relational uniqueness of the family's induction, and the lifted
-- relation read forward at the image of a shape). IR.Indexed.General.
-- Initiality gives it for the universal family, IR.Polynomial.General.
-- Initiality for the generated part of any algebra.
--
-- A valuation with the lax law is related to induction at every element
-- (`Lax`, `ind-unique-rel`): the rule is the family's induction at the
-- method carried along the isomorphism of shapes and located arguments,
-- the law holds at the image of each shape with the family's relatedness
-- read forward (`Lawful`, `lawful-at-image`), and the extension that
-- carries the method carries the law to every located argument
-- (`carried-law`, by `extension-preserves-predicates`). Instances: the
-- fundamental theorem (`ind-rel`), uniqueness for congruent methods
-- (`ind-unique`, `ind-homomorphic`) and fusion (`ind-fusion`), where the
-- family's computation identity is used. Under extensionality every
-- method is congruent (`congruent`).

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.HalfAdjoint.Extension using
  (extension-preserves-predicates)

open import SPT.IR.General using
  (Located-Argument; Inductive-Family; Located; forth; arguments; intro;
   Method; Fiber; prepared; method; ind; Computation; ind-β)
open import SPT.IR.Description.Indexed using
  (ι; σ; δ; General; Shape; Mark; IH; map-IH)
open import SPT.IR.Polynomial using (Family; carrier; readout)

------------------------------------------------------------------------
-- Related hypotheses

-- A relation between the values of two motives lifts to their hypotheses
-- at an argument of a subcode: at a δ, related at every child of the map.

module _
  {ℓ κ μ ν ρ : Level} {I : Set ℓ} {D : I → Set (ℓ ⊔ κ)}
  (Z : Family ℓ κ D)
  (Q : (i : I) → carrier Z i → Set μ)
  (P : (i : I) → carrier Z i → Set ν)
  (C : (i : I) (t : carrier Z i) → Q i t → P i t → Set ρ)
  where

  Lifted :
    (ε : General ℓ κ I D) (x : Shape ε Z) → IH ε Z Q x → IH ε Z P x
    → Set (ℓ ⊔ ρ)
  Lifted (ι e) x h k = Lift (ℓ ⊔ ρ) 𝟙
  Lifted (σ A b) (a , x) h k = Lifted (b a) x h k
  Lifted (δ A i F) (g , x) (h , h′) (k , k′) =
    Σ ((a : A) → C (i a) (g a) (h a) (k a))
      (λ _ → Lifted (F (λ a → readout Z (i a) (g a))) x h′ k′)

------------------------------------------------------------------------
-- Pointwise initiality of a family's own induction

record Pointwise-Initiality
  {ℓ κ : Level} {I : Set ℓ} {D : I → Set (ℓ ⊔ κ)} {γ : General ℓ κ I D}
  (F : Inductive-Family γ) : Setω where
  open Inductive-Family F
  field
    Related :
      {μ ν ρ : Level}
      (Q : (i : I) → carrier family i → Set μ)
      (P : (i : I) → carrier family i → Set ν)
      (C : (i : I) (t : carrier family i) → Q i t → P i t → Set ρ)
      (i : I) (b : Located-Argument γ Arguments information i)
      → Hypotheses Q i b → Hypotheses P i b → Set (ℓ ⊔ ρ)
    values :
      {μ : Level} (Q : (i : I) → carrier family i → Set μ)
      → ((i : I) (t : carrier family i) → Q i t)
      → (i : I) (b : Located-Argument γ Arguments information i)
      → Hypotheses Q i b
    unique-rel :
      {μ ν ρ : Level}
      (Q : (i : I) → carrier family i → Set μ)
      (P : (i : I) → carrier family i → Set ν)
      (C : (i : I) (t : carrier family i) → Q i t → P i t → Set ρ)
      (v : (i : I) (t : carrier family i) → Q i t)
      (m : (i : I) (b : Located-Argument γ Arguments information i)
        → Hypotheses P i b → P i (make i b))
      → ((i : I) (b : Located-Argument γ Arguments information i)
        (k : Hypotheses P i b)
        → Related Q P C i b (values Q v i b) k
        → C i (make i b) (v i (make i b)) (m i b k))
      → (i : I) (t : carrier family i) → C i t (v i t) (induction P m i t)
    lifted-forward :
      {μ ν ρ : Level}
      (Q : (i : I) → carrier family i → Set μ)
      (P : (i : I) → carrier family i → Set ν)
      (C : (i : I) (t : carrier family i) → Q i t → P i t → Set ρ)
      (v : (i : I) (t : carrier family i) → Q i t) (x : Shape γ family)
      (k :
        Hypotheses P (pr₁ (Mark γ family x)) (to x , ap pr₁ (output-to x)))
      → Related Q P C (pr₁ (Mark γ family x)) (to x , ap pr₁ (output-to x))
          (values Q v (pr₁ (Mark γ family x)) (to x , ap pr₁ (output-to x)))
          k
      → Lifted family Q P C γ x (map-IH γ family Q v x) (hyp-forward P x k)

------------------------------------------------------------------------
-- The laws over an inductive family

module _
  {ℓ κ : Level} {I : Set ℓ} {D : I → Set (ℓ ⊔ κ)} {γ : General ℓ κ I D}
  (F : Inductive-Family γ)
  where

  open Inductive-Family F

  -- The lax law of a valuation v for methods m: at every introduction, the
  -- methods at any hypotheses related to v at the children are related to
  -- v at the introduced element. No reflexivity, transitivity or
  -- congruence is asked.

  module _
    {μ ν ρ : Level}
    (Q : (i : I) → carrier family i → Set μ)
    (P : (i : I) → carrier family i → Set ν)
    (C : (i : I) (t : carrier family i) → Q i t → P i t → Set ρ)
    where

    Lax :
      ((i : I) (t : carrier family i) → Q i t) → Method F P
      → Set (ℓ ⊔ ν ⊔ ρ)
    Lax v m =
      (x : Shape γ family) (k : IH γ family P x)
      → Lifted family Q P C γ x (map-IH γ family Q v x) k
      → C (pr₁ (Mark γ family x)) (intro F x)
          (v (pr₁ (Mark γ family x)) (intro F x)) (m x k)

  -- Methods related at related hypotheses.

  module _
    {μ ν ρ : Level}
    (Q : (i : I) → carrier family i → Set μ)
    (P : (i : I) → carrier family i → Set ν)
    (C : (i : I) (t : carrier family i) → Q i t → P i t → Set ρ)
    (n : Method F Q) (m : Method F P)
    where

    Relational : Set (ℓ ⊔ μ ⊔ ν ⊔ ρ)
    Relational =
      (x : Shape γ family) (h : IH γ family Q x) (k : IH γ family P x)
      → Lifted family Q P C γ x h k
      → C (pr₁ (Mark γ family x)) (intro F x) (n x h) (m x k)

  -- Methods are congruent when hypotheses agreeing at every child give the
  -- same value; at a δ the agreement is pointwise on the child map, so
  -- this is a genuine hypothesis there. Induction satisfies its
  -- computation equations wherever the family's induction has its own.

  module _ {ν : Level} (P : (i : I) → carrier family i → Set ν) where

    Identical : (i : I) (t : carrier family i) → P i t → P i t → Set ν
    Identical i t x y = x ＝ y

    Congruent : Method F P → Set (ℓ ⊔ ν)
    Congruent m =
      (x : Shape γ family) (h k : IH γ family P x)
      → Lifted family P P Identical γ x h k → m x h ＝ m x k

    Homomorphic :
      ((i : I) (t : carrier family i) → P i t) → Method F P → Set (ℓ ⊔ ν)
    Homomorphic v m =
      (x : Shape γ family)
      → v (pr₁ (Mark γ family x)) (intro F x)
        ＝ m x (map-IH γ family P v x)

    ind-homomorphic :
      Computation F P → (m : Method F P) → Homomorphic (ind F P m) m
    ind-homomorphic computation m x = ind-β F P computation m x

  -- A map of motives carries hypotheses along (`mapped`); the graph of the
  -- map relates them.

  module _
    {ν ν′ : Level}
    (P : (i : I) → carrier family i → Set ν)
    (P′ : (i : I) → carrier family i → Set ν′)
    (f : (i : I) (t : carrier family i) → P i t → P′ i t)
    where

    mapped :
      (ε : General ℓ κ I D) (x : Shape ε family)
      → IH ε family P x → IH ε family P′ x
    mapped (ι e) x h = lift ⋆
    mapped (σ A b) (a , x) h = mapped (b a) x h
    mapped (δ A i G) (g , x) (h , h′) =
      ( (λ a → f (i a) (g a) (h a))
      , mapped (G (λ a → readout family (i a) (g a))) x h′)

    Graph : (i : I) (t : carrier family i) → P i t → P′ i t → Set ν′
    Graph i t y z = f i t y ＝ z

    graph-agreement :
      (ε : General ℓ κ I D) (x : Shape ε family)
      (h : IH ε family P x) (k : IH ε family P′ x)
      → Lifted family P P′ Graph ε x h k
      → Lifted family P′ P′ (Identical P′) ε x (mapped ε x h) k
    graph-agreement (ι e) x h k r = r
    graph-agreement (σ A b) (a , x) h k r = graph-agreement (b a) x h k r
    graph-agreement (δ A i G) (g , x) (h , h′) (k , k′) (r , r′) =
      ( r
      , graph-agreement (G (λ a → readout family (i a) (g a))) x h′ k′ r′)

    Carries : Method F P → Method F P′ → Set (ℓ ⊔ ν ⊔ ν′)
    Carries m m′ =
      (x : Shape γ family) (h : IH γ family P x)
      → f (pr₁ (Mark γ family x)) (intro F x) (m x h)
        ＝ m′ x (mapped γ x h)

  ----------------------------------------------------------------------
  -- Relational uniqueness and its instances

  module _ (B : Pointwise-Initiality F) where

    open Pointwise-Initiality B

    module _
      {μ ν ρ : Level}
      (Q : (i : I) → carrier family i → Set μ)
      (P : (i : I) → carrier family i → Set ν)
      (C : (i : I) (t : carrier family i) → Q i t → P i t → Set ρ)
      (v : (i : I) (t : carrier family i) → Q i t)
      where

      -- The law at a located argument, for a method there.
      Lawful : (n : Located F) → Fiber F P n → Set (ℓ ⊔ ν ⊔ ρ)
      Lawful (i , b) f =
        (k : Hypotheses P i b) → Related Q P C i b (values Q v i b) k
        → C i (make i b) (v i (make i b)) (f k)

    module _
      {μ ν ρ : Level}
      (Q : (i : I) → carrier family i → Set μ)
      (P : (i : I) → carrier family i → Set ν)
      (C : (i : I) (t : carrier family i) → Q i t → P i t → Set ρ)
      (v : (i : I) (t : carrier family i) → Q i t) (m : Method F P)
      (law : Lax Q P C v m)
      where

      lawful-at-image :
        (x : Shape γ family) → Lawful Q P C v (forth F x) (prepared F P m x)
      lawful-at-image x k r =
        law x (hyp-forward P x k) (lifted-forward Q P C v x k r)

      carried-law :
        (i : I) (b : Located-Argument γ Arguments information i)
        (k : Hypotheses P i b)
        → Related Q P C i b (values Q v i b) k
        → C i (make i b) (v i (make i b)) (method F P m i b k)
      carried-law i b =
        extension-preserves-predicates (arguments F) (Fiber F P)
          (prepared F P m) (Lawful Q P C v) lawful-at-image (i , b)

      ind-unique-rel :
        (i : I) (t : carrier family i) → C i t (v i t) (ind F P m i t)
      ind-unique-rel = unique-rel Q P C v (method F P m) carried-law

    -- The fundamental theorem: methods related at related hypotheses have
    -- related inductions.

    module _
      {μ ν ρ : Level}
      (Q : (i : I) → carrier family i → Set μ)
      (P : (i : I) → carrier family i → Set ν)
      (C : (i : I) (t : carrier family i) → Q i t → P i t → Set ρ)
      (n : Method F Q) (m : Method F P)
      where

      ind-rel :
        Computation F Q → Relational Q P C n m
        → (i : I) (t : carrier family i) → C i t (ind F Q n i t) (ind F P m i t)
      ind-rel computation related =
        ind-unique-rel Q P C (ind F Q n) m
          (λ x k r →
            transport
              (λ w → C (pr₁ (Mark γ family x)) (intro F x) w (m x k))
              ((ind-β F Q computation n x) ⁻¹)
              (related x (map-IH γ family Q (ind F Q n) x) k r))

    -- Uniqueness: a valuation satisfying the computation equations of
    -- congruent methods is their induction at every element.

    module _ {ν : Level} (P : (i : I) → carrier family i → Set ν) where

      ind-unique :
        (v : (i : I) (t : carrier family i) → P i t) (m : Method F P)
        → Congruent P m → Homomorphic P v m
        → (i : I) (t : carrier family i) → v i t ＝ ind F P m i t
      ind-unique v m congruence equations =
        ind-unique-rel P P (Identical P) v m
          (λ x k r → equations x ∙ congruence x (map-IH γ family P v x) k r)

    -- Fusion: when a map of motives carries the methods of one motive to
    -- congruent methods of the other at mapped hypotheses, the image of
    -- induction is the other induction, through both computation
    -- identities.

    module _
      {ν ν′ : Level}
      (P : (i : I) → carrier family i → Set ν)
      (P′ : (i : I) → carrier family i → Set ν′)
      (f : (i : I) (t : carrier family i) → P i t → P′ i t)
      where

      ind-fusion :
        Computation F P → (m : Method F P) (m′ : Method F P′)
        → Congruent P′ m′ → Carries P P′ f m m′
        → (i : I) (t : carrier family i)
        → f i t (ind F P m i t) ＝ ind F P′ m′ i t
      ind-fusion computation m m′ congruence carries =
        ind-unique-rel P P′ (Graph P P′ f) (ind F P m) m′
          ( λ x k r →
              ap (f (pr₁ (Mark γ family x)) (intro F x))
                (ind-β F P computation m x)
              ∙ carries x (map-IH γ family P (ind F P m) x)
              ∙ congruence x
                  (mapped P P′ f γ x (map-IH γ family P (ind F P m) x))
                  k
                  (graph-agreement P P′ f γ x
                    (map-IH γ family P (ind F P m) x) k r))

------------------------------------------------------------------------
-- Congruence under extensionality

-- Under extensionality for families over the arities, hypotheses agreeing
-- at every child are identical, so every method is congruent.

module _
  {ℓ κ ν : Level} {I : Set ℓ} {D : I → Set (ℓ ⊔ κ)}
  (extensionality : (A : Set ℓ) (Y : A → Set ν) → FunExt A Y)
  {γ : General ℓ κ I D} (F : Inductive-Family γ)
  where

  open Inductive-Family F

  module _ (P : (i : I) → carrier family i → Set ν) where

    agreement :
      (ε : General ℓ κ I D) (x : Shape ε family) (h k : IH ε family P x)
      → Lifted family P P (Identical F P) ε x h k → h ＝ k
    agreement (ι e) x h k r = refl
    agreement (σ A b) (a , x) h k r = agreement (b a) x h k r
    agreement (δ A i G) (g , x) (h , h′) (k , k′) (r , r′) =
      ap₂ (λ y z → (y , z))
        (extensionality A (λ a → P (i a) (g a)) h k r)
        (agreement (G (λ a → readout family (i a) (g a))) x h′ k′ r′)

    congruent : (m : Method F P) → Congruent F P m
    congruent m x h k r = ap (m x) (agreement γ x h k r)
