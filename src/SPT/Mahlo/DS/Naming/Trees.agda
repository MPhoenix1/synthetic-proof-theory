{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Naming.Trees where

-- The trees of the formers Q of a family (C , D) and an operator Φ on it,
-- over a family (A , B) of small types, with no induction–recursion. A
-- stage is a W-type whose nodes are a constant former (a leaf), an index
-- x : A at which a family former or Φ is applied, branching over one index
-- branch and B x, or the identity former, with one branch (`Label`,
-- `Branches`, `Stage`). The trees at a stage and their outputs are defined
-- by recursion on the stage (`layer`). An output is a small type of
-- selections, each naming an element of C (`Output`, `Selection`); a
-- choice is a tree with a selection (`Choice`, `chosen`). At an applied
-- node a tree is a choice for the index, a map from its decoding into B x
-- and a choice at each y : B x (`Inputs`, `input`), and returns the former
-- or Φ at that family (`apply`). The requests at a family, decoding to D
-- of their selected elements, form an operator of the ambient family
-- (`Request`, `requested`, `requests`).
--
-- Along a map ι : A' → A, stages, trees and choices move from (A' , B ∘ ι)
-- to (A , B) (`relabel`, `shift`, `move`), keeping the chosen elements
-- (`moved`) and the outputs (`shifted`), under extensionality for families
-- of names (`pair`); along an identity B ∘ ι ＝ B' this moves requests
-- (`carry`, `carried`).

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
import SPT.Mahlo.Ambient as Ambient
open import SPT.Foundation.Tree.W using (W; sup)
import SPT.Mahlo.Specification as Specification

open import SPT.Mahlo.DS.Realization.Family using (cast)

------------------------------------------------------------------------
-- Stages

data Nullary : Set where
  empty unit two natural : Nullary

-- The family formers (wellfounded: the tree former) and the operator.
data Unary : Set where
  product sum wellfounded operator : Unary

data Label {ℓ : Level} (A : Set ℓ) : Set ℓ where
  constant : Nullary → Label A
  applied : Unary → A → Label A
  identity : Label A

Branches : {ℓ : Level} (A : Set ℓ) → (A → Set ℓ) → Label A → Set ℓ
Branches {ℓ} A B (constant t) = Lift ℓ 𝟘
Branches {ℓ} A B (applied t x) = Lift ℓ 𝟙 ⊎ B x
Branches {ℓ} A B identity = Lift ℓ 𝟙

Stage : {ℓ : Level} (A : Set ℓ) → (A → Set ℓ) → Set ℓ
Stage A B = W (Label A) (Branches A B)

leaf : {ℓ : Level} {A : Set ℓ} (B : A → Set ℓ) → Nullary → Stage A B
leaf B t = sup (constant t) (λ x → 𝟘-elim (lower x))

------------------------------------------------------------------------
-- Outputs, layers and choices

-- A small type of selections, each naming an element of C.
Output : {κ : Level} (ℓ : Level) → Set κ → Set (lsuc ℓ ⊔ κ)
Output ℓ C = Σ (Set ℓ) (λ S → S → C)

Selection : {κ ℓ : Level} {C : Set κ} → Output ℓ C → Set ℓ
Selection o = pr₁ o

reselected :
  {κ ℓ : Level} {C : Set κ} {o o' : Output ℓ C} (e : o ＝ o')
  (s : Selection o') → pr₂ o (transport Selection (e ⁻¹) s) ＝ pr₂ o' s
reselected refl s = refl

-- A small type of trees, each with its output.
Layer : {κ : Level} (ℓ : Level) → Set κ → Set (lsuc ℓ ⊔ κ)
Layer ℓ C = Σ (Set ℓ) (λ T → T → Output ℓ C)

Choice : {κ ℓ : Level} {C : Set κ} → Layer ℓ C → Set ℓ
Choice c = Σ (pr₁ c) (λ τ → Selection (pr₂ c τ))

chosen : {κ ℓ : Level} {C : Set κ} (c : Layer ℓ C) → Choice c → C
chosen c i = pr₂ (pr₂ c (pr₁ i)) (pr₂ i)

------------------------------------------------------------------------
-- Inputs at a node

module _ {κ ℓ : Level} {C : Set κ} (D : C → Set ℓ) where

  -- At a node branching over X: a choice for the index, a map from its
  -- decoding into X, and a choice at each point of X.
  Inputs : (X : Set ℓ) → Layer ℓ C → (X → Layer ℓ C) → Set ℓ
  Inputs X c₀ c =
    Σ (Choice c₀) (λ i → (D (chosen c₀ i) → X) × ((y : X) → Choice (c y)))

  input :
    (X : Set ℓ) (c₀ : Layer ℓ C) (c : X → Layer ℓ C) → Inputs X c₀ c
    → Specification.Family D
  input X c₀ c τ =
    chosen c₀ (pr₁ τ) ,
    (λ z → chosen (c (pr₁ (pr₂ τ) z)) (pr₂ (pr₂ τ) (pr₁ (pr₂ τ) z)))

  -- At an identity node: a choice and two points of its decoding.
  Points : Layer ℓ C → Set ℓ
  Points c₀ = Σ (Choice c₀) (λ i → D (chosen c₀ i) × D (chosen c₀ i))

  selected :
    (F : Specification.Family D) → Lift ℓ 𝟙 ⊎ D (pr₁ F) → C
  selected F (inl _) = pr₁ F
  selected F (inr y) = pr₂ F y

  -- An identity of families of names, by extensionality.
  pair :
    ((X : Set ℓ) → FunExt X (λ _ → C))
    → {X Y : C} {f : D X → C} {g : D Y → C}
    → (e : X ＝ Y) → ((x : D X) → f x ＝ g (cast (ap D e) x))
    → _＝_ {A = Specification.Family D} (X , f) (Y , g)
  pair extensionality {X} {f = f} {g = g} refl h =
    ap (λ k → (X , k)) (extensionality (D X) f g h)

------------------------------------------------------------------------
-- The trees of the formers and an operator

module _
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ}
  (Q : Specification.Formers C D) (Φ : Specification.Operator D)
  where

  nullary : Nullary → C
  nullary empty = Specification.Formers.empty Q
  nullary unit = Specification.Formers.unit Q
  nullary two = Specification.Formers.two Q
  nullary natural = Specification.Formers.natural Q

  -- A family former names one element; Φ, its index and its members.
  apply : Unary → Specification.Family D → Output ℓ C
  apply product F = Lift ℓ 𝟙 , (λ _ → Specification.Formers.product Q F)
  apply sum F = Lift ℓ 𝟙 , (λ _ → Specification.Formers.sum Q F)
  apply wellfounded F =
    Lift ℓ 𝟙 , (λ _ → Specification.Formers.tree Q F)
  apply operator F = (Lift ℓ 𝟙 ⊎ D (pr₁ (Φ F))) , selected D (Φ F)

  layer : {A : Set ℓ} (B : A → Set ℓ) → Stage A B → Layer ℓ C
  layer B (sup (constant t) f) =
    Lift ℓ 𝟙 , (λ _ → Lift ℓ 𝟙 , (λ _ → nullary t))
  layer B (sup (applied t x) f) =
    Inputs D (B x) (layer B (f (inl (lift ⋆))))
      (λ y → layer B (f (inr y))) ,
    (λ τ →
      apply t
        (input D (B x) (layer B (f (inl (lift ⋆))))
          (λ y → layer B (f (inr y))) τ))
  layer B (sup identity f) =
    Points D (layer B (f (lift ⋆))) ,
    (λ τ →
      Lift ℓ 𝟙 ,
      (λ _ →
        Specification.Formers.identity Q
          (chosen (layer B (f (lift ⋆))) (pr₁ τ))
          (pr₁ (pr₂ τ)) (pr₂ (pr₂ τ))))

  -- A tree at a stage with a selection of its output.
  record Request {A : Set ℓ} (B : A → Set ℓ) : Set ℓ where
    constructor request
    field
      stage : Stage A B
      tree : pr₁ (layer B stage)
      selection : Selection (pr₂ (layer B stage) tree)

  requested : {A : Set ℓ} {B : A → Set ℓ} → Request B → C
  requested {A} {B} r =
    pr₂ (pr₂ (layer B (Request.stage r)) (Request.tree r))
      (Request.selection r)

  -- The requests at a family, each decoding to D of its element.
  requests : Ambient.Operator ℓ
  requests F = Request (pr₂ F) , (λ r → D (requested r))

------------------------------------------------------------------------
-- Relabeling along a map of indices

relabel :
  {ℓ : Level} {A A' : Set ℓ} (B : A → Set ℓ) (ι : A' → A)
  → Stage A' (λ x → B (ι x)) → Stage A B
relabel B ι (sup (constant t) f) =
  sup (constant t) (λ y → relabel B ι (f y))
relabel B ι (sup (applied t x) f) =
  sup (applied t (ι x)) (λ y → relabel B ι (f y))
relabel B ι (sup identity f) = sup identity (λ y → relabel B ι (f y))

reidentified :
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ}
  (Q : Specification.Formers C D) {a a' : C} (e : a ＝ a') (p q : D a')
  → _＝_ {A = Output ℓ C}
      ( Lift ℓ 𝟙
      , (λ _ →
          Specification.Formers.identity Q a
            (cast (ap D e ⁻¹) p) (cast (ap D e ⁻¹) q)))
      (Lift ℓ 𝟙 , (λ _ → Specification.Formers.identity Q a' p q))
reidentified Q refl p q = refl

-- Trees move with their stages: the index map is composed with the
-- identity of chosen elements, and selections move along the identity of
-- outputs, which at an applied node is extensionality.

module _
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ}
  (extensionality : (X : Set ℓ) → FunExt X (λ _ → C))
  (Q : Specification.Formers C D) (Φ : Specification.Operator D)
  where

  mutual
    shift :
      {A A' : Set ℓ} (B : A → Set ℓ) (ι : A' → A)
      (s : Stage A' (λ x → B (ι x)))
      → pr₁ (layer Q Φ (λ x → B (ι x)) s)
      → pr₁ (layer Q Φ B (relabel B ι s))
    shift B ι (sup (constant t) f) τ = τ
    shift B ι (sup (applied t x) f) τ =
      move B ι (f (inl (lift ⋆))) (pr₁ τ) ,
      ( (λ z →
          pr₁ (pr₂ τ)
            (cast (ap D (moved B ι (f (inl (lift ⋆))) (pr₁ τ))) z))
      , (λ y → move B ι (f (inr y)) (pr₂ (pr₂ τ) y)))
    shift B ι (sup identity f) τ =
      move B ι (f (lift ⋆)) (pr₁ τ) ,
      ( cast (ap D (moved B ι (f (lift ⋆)) (pr₁ τ)) ⁻¹) (pr₁ (pr₂ τ))
      , cast (ap D (moved B ι (f (lift ⋆)) (pr₁ τ)) ⁻¹) (pr₂ (pr₂ τ)))

    move :
      {A A' : Set ℓ} (B : A → Set ℓ) (ι : A' → A)
      (s : Stage A' (λ x → B (ι x)))
      → Choice (layer Q Φ (λ x → B (ι x)) s)
      → Choice (layer Q Φ B (relabel B ι s))
    move B ι s i =
      shift B ι s (pr₁ i) ,
      transport Selection (shifted B ι s (pr₁ i) ⁻¹) (pr₂ i)

    moved :
      {A A' : Set ℓ} (B : A → Set ℓ) (ι : A' → A)
      (s : Stage A' (λ x → B (ι x)))
      (i : Choice (layer Q Φ (λ x → B (ι x)) s))
      → chosen (layer Q Φ B (relabel B ι s)) (move B ι s i)
        ＝ chosen (layer Q Φ (λ x → B (ι x)) s) i
    moved B ι s i = reselected (shifted B ι s (pr₁ i)) (pr₂ i)

    shifted :
      {A A' : Set ℓ} (B : A → Set ℓ) (ι : A' → A)
      (s : Stage A' (λ x → B (ι x)))
      (τ : pr₁ (layer Q Φ (λ x → B (ι x)) s))
      → pr₂ (layer Q Φ B (relabel B ι s)) (shift B ι s τ)
        ＝ pr₂ (layer Q Φ (λ x → B (ι x)) s) τ
    shifted B ι (sup (constant t) f) τ = refl
    shifted B ι (sup (applied t x) f) τ =
      ap (apply Q Φ t)
        (pair D extensionality
          (moved B ι (f (inl (lift ⋆))) (pr₁ τ))
          (λ z →
            moved B ι
              (f (inr
                (pr₁ (pr₂ τ)
                  (cast (ap D (moved B ι (f (inl (lift ⋆))) (pr₁ τ))) z))))
              (pr₂ (pr₂ τ)
                (pr₁ (pr₂ τ)
                  (cast (ap D (moved B ι (f (inl (lift ⋆))) (pr₁ τ))) z)))))
    shifted B ι (sup identity f) τ =
      reidentified Q (moved B ι (f (lift ⋆)) (pr₁ τ))
        (pr₁ (pr₂ τ)) (pr₂ (pr₂ τ))

  -- Along an identity of families of types, by its one case.
  carry :
    {A A' : Set ℓ} (B : A → Set ℓ) (ι : A' → A) {B' : A' → Set ℓ}
    → (λ x → B (ι x)) ＝ B' → Request Q Φ B' → Request Q Φ B
  carry B ι refl r =
    request (relabel B ι (Request.stage r))
      (shift B ι (Request.stage r) (Request.tree r))
      (transport Selection
        (shifted B ι (Request.stage r) (Request.tree r) ⁻¹)
        (Request.selection r))

  carried :
    {A A' : Set ℓ} (B : A → Set ℓ) (ι : A' → A) {B' : A' → Set ℓ}
    (e : (λ x → B (ι x)) ＝ B') (r : Request Q Φ B')
    → requested Q Φ (carry B ι e r) ＝ requested Q Φ r
  carried B ι refl r =
    reselected (shifted B ι (Request.stage r) (Request.tree r))
      (Request.selection r)
