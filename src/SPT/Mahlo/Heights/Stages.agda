{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Heights.Stages where

-- The stages of a layer of codes along a height, by recursion on the
-- height, with no induction–recursion. One layer of Φ's codes over a
-- universe (U , T) names the ambient formers at U's families, and Φ's index
-- and members at them (`Code`), decoded as the formers and Φ themselves
-- (`decode`); as an operator on families it is `codes`. Every operator Λ
-- on families is a layer: the stage of a node is a child with a code of Λ
-- over the child's stage (`Stage`, `decoding`):
--
--   Stage Λ (node X f) = Σ x : X. pr₁ (Λ (Stage Λ (f x) , decoding Λ (f x))).
--
-- A layer has Φ's codes when they are among its codes with their decodings
-- (`Has-Codes`; for `codes`, `codes-have-codes`). It is functorial when its
-- codes move along the maps of universes that keep decodings (`Functorial`;
-- for `codes`, Heights.Stages.Map). Along the simulation order the stages
-- of a functorial layer include, their decodings kept: along s ⊑ t each
-- code of s's stage is a code of t's (`include`, `included`), and along
-- s ⊏ t each code over s's stage is one (`raise`, `raised`). A family code
-- moves its members along the identity of its index's decoding, so the
-- moved family is the original one under extensionality for families of
-- types (`family`).

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
import SPT.Foundation.Tree as Tree
import SPT.Mahlo.Ambient as Ambient
open import SPT.Foundation.Tree.W using (W)
open import SPT.Mahlo.DS.Realization.Family using (cast)
import SPT.Mahlo.Specification as Specification
open import SPT.OrdinalGeometry.Height.Ordinals using (Height)
open import SPT.OrdinalGeometry.Height.Simulation using
  (_⊑_; _⊏_; below; under)

------------------------------------------------------------------------
-- One layer of codes over a universe

data Code
  {ℓ : Level} (Φ : Ambient.Operator ℓ) (U : Set ℓ) (T : U → Set ℓ)
  : Set ℓ where
  empty unit two natural : Code Φ U T
  product sum tree result : (a : U) → (T a → U) → Code Φ U T
  identity : (a : U) → T a → T a → Code Φ U T
  branch :
    (a : U) (b : T a → U) → pr₁ (Φ (T a , (λ x → T (b x))))
    → Code Φ U T

decode :
  {ℓ : Level} {Φ : Ambient.Operator ℓ} {U : Set ℓ} {T : U → Set ℓ}
  → Code Φ U T → Set ℓ
decode {ℓ} empty = Lift ℓ 𝟘
decode {ℓ} unit = Lift ℓ 𝟙
decode {ℓ} two = Lift ℓ 𝟚
decode {ℓ} natural = Lift ℓ ℕ
decode {ℓ} {Φ} {U} {T} (product a b) = (x : T a) → T (b x)
decode {ℓ} {Φ} {U} {T} (sum a b) = Σ (T a) (λ x → T (b x))
decode {ℓ} {Φ} {U} {T} (tree a b) = W (T a) (λ x → T (b x))
decode {ℓ} {Φ} {U} {T} (result a b) = pr₁ (Φ (T a , (λ x → T (b x))))
decode (identity a x y) = x ＝ y
decode {ℓ} {Φ} {U} {T} (branch a b i) =
  pr₂ (Φ (T a , (λ x → T (b x)))) i

-- The layer of Φ's codes, as an operator on families.
codes : {ℓ : Level} → Ambient.Operator ℓ → Ambient.Operator ℓ
codes Φ F = Code Φ (pr₁ F) (pr₂ F) , decode

------------------------------------------------------------------------
-- Identities of families of types

module _
  {ℓ : Level} (extensionality : (X : Set ℓ) → FunExt X (λ _ → Set ℓ))
  where

  -- Mathematical shape: e : A ＝ A', B ＝ B' ∘ cast e ⊢ (A , B) ＝ (A' , B').
  family :
    {A A' : Set ℓ} {B : A → Set ℓ} {B' : A' → Set ℓ} (e : A ＝ A')
    → ((x : A) → B x ＝ B' (cast e x))
    → _＝_ {A = Specification.Family (λ (X : Set ℓ) → X)} (A , B) (A' , B')
  family {A} {B = B} {B' = B'} refl h =
    ap (λ k → (A , k)) (extensionality A B B' h)

-- The identity type along an identity of its type.
reidentified :
  {ℓ : Level} {A' A : Set ℓ} (e : A' ＝ A) (x y : A)
  → (cast (e ⁻¹) x ＝ cast (e ⁻¹) y) ＝ (x ＝ y)
reidentified refl x y = refl

-- Φ's members along an identity of its inputs.
rebranched :
  {ℓ : Level} (Φ : Ambient.Operator ℓ)
  {G H : Specification.Family (λ (X : Set ℓ) → X)} (e : G ＝ H)
  (i : pr₁ (Φ H))
  → pr₂ (Φ G) (cast (ap (λ F → pr₁ (Φ F)) (e ⁻¹)) i) ＝ pr₂ (Φ H) i
rebranched Φ refl i = refl

------------------------------------------------------------------------
-- Layers with Φ's codes, and functorial layers

-- Φ's codes are codes of the layer Λ, with their decodings.
record Has-Codes {ℓ : Level} (Φ Λ : Ambient.Operator ℓ) : Set (lsuc ℓ)
  where
  field
    code : {U : Set ℓ} {T : U → Set ℓ} → Code Φ U T → pr₁ (Λ (U , T))
    code-β : {U : Set ℓ} {T : U → Set ℓ} (c : Code Φ U T) →
      pr₂ (Λ (U , T)) (code c) ＝ decode c

-- The codes of Λ move along the maps of universes that keep decodings.
record Functorial {ℓ : Level} (Λ : Ambient.Operator ℓ) : Set (lsuc ℓ)
  where
  field
    move : {U U′ : Set ℓ} (T : U → Set ℓ) (T′ : U′ → Set ℓ) (h : U → U′) →
      ((a : U) → T′ (h a) ＝ T a) → pr₁ (Λ (U , T)) → pr₁ (Λ (U′ , T′))
    move-β : {U U′ : Set ℓ} (T : U → Set ℓ) (T′ : U′ → Set ℓ)
      (h : U → U′) (h-β : (a : U) → T′ (h a) ＝ T a)
      (c : pr₁ (Λ (U , T))) →
      pr₂ (Λ (U′ , T′)) (move T T′ h h-β c) ＝ pr₂ (Λ (U , T)) c

-- The layer of Φ's codes has them.
codes-have-codes : {ℓ : Level} (Φ : Ambient.Operator ℓ) →
  Has-Codes Φ (codes Φ)
codes-have-codes Φ = record
  { code = λ c → c
  ; code-β = λ c → refl
  }

------------------------------------------------------------------------
-- Stages along a height

module _ {ℓ : Level} (Λ : Ambient.Operator ℓ) where

  mutual
    -- At a node: a child, and a code of the layer over the child's stage.
    Stage : Height ℓ → Set ℓ
    Stage (Tree.hole ())
    Stage (Tree.node X f) =
      Σ X (λ x → pr₁ (Λ (Stage (f x) , decoding (f x))))

    decoding : (t : Height ℓ) → Stage t → Set ℓ
    decoding (Tree.hole ())
    decoding (Tree.node X f) (x , c) =
      pr₂ (Λ (Stage (f x) , decoding (f x))) c

------------------------------------------------------------------------
-- Inclusions along the simulation order

module _
  {ℓ : Level} {Λ : Ambient.Operator ℓ} (functorial : Functorial Λ)
  where

  open Functorial functorial using (move; move-β)

  mutual
    -- Along s ⊑ t each code of s's stage is a code of t's.
    include : {s t : Height ℓ} → s ⊑ t → Stage Λ s → Stage Λ t
    include (below p) (x , c) = raise (p x) c

    -- Along s ⊏ t each code over s's stage is one of t's, at the child
    -- above s.
    raise : {s t : Height ℓ} → s ⊏ t →
      pr₁ (Λ (Stage Λ s , decoding Λ s)) → Stage Λ t
    raise {s} (under {h = h} z q) c =
      z , move (decoding Λ s) (decoding Λ (h z)) (include q) (included q) c

    included : {s t : Height ℓ} (q : s ⊑ t) (a : Stage Λ s) →
      decoding Λ t (include q a) ＝ decoding Λ s a
    included (below p) (x , c) = raised (p x) c

    raised : {s t : Height ℓ} (q : s ⊏ t)
      (c : pr₁ (Λ (Stage Λ s , decoding Λ s))) →
      decoding Λ t (raise q c) ＝ pr₂ (Λ (Stage Λ s , decoding Λ s)) c
    raised {s} (under {h = h} z q) c =
      move-β (decoding Λ s) (decoding Λ (h z)) (include q) (included q) c
