{-# OPTIONS --safe --without-K #-}

module SPT.IR.Univalent.Universe where

-- The rules of Shulman's higher inductive–recursive univalent universe of
-- a type-valued description γ (HoTT blog, 8 June 2014), with codes at a
-- level κ: codes and decoding, an introduction for every argument of γ
-- decoding to its output, and a path constructor `ua` that the decoding
-- sends back to its input (`Universe`). Elimination into level ν
-- (`Elimination`): a method at every introduction and a path method over
-- `ua` (`Method`, `Path-method`), with both computation rules.
-- Lumsdaine's observation: `ua` makes the fibers of the decoding
-- propositions (`fibers`), hence `ua a a refl ＝ refl` (`ua-refl`). So a
-- path method forces the motive to be a family of propositions (`forced`),
-- every family of propositions has one (`propositional`), and elimination
-- is induction into propositions (`induction`).

open import SPT.Base
open import SPT.Foundation.Fibers using (fiber)
open import SPT.Foundation.Propositions using
  (is-proposition; propositions-are-sets)

open import SPT.IR.Description using
  (Desc; indexed; Shape; Mark)
open import SPT.IR.Restriction using (Position; input)

------------------------------------------------------------------------
-- Formation, introduction and the path constructor

-- Mathematical shape, after Shulman's pseudo-Agda:
--
--   intro : Shape γ (Code , El) → Code,
--   El (intro z) ＝ Mark γ (Code , El) z,
--   ua : El a ＝ El b → a ＝ b,      ap El (ua a b p) ＝ p.
--
-- Nonclaim: no decoding law holds by conversion here; each is an identity.

record Universe
  {ℓ : Level} (κ : Level) (γ : Desc {s = ℓ} (Set ℓ))
  : Set (lsuc κ ⊔ lsuc ℓ) where
  field
    Code : Set κ
    El : Code → Set ℓ
    intro : Shape γ (indexed Code El) → Code
    intro-β :
      (z : Shape γ (indexed Code El))
      → El (intro z) ＝ Mark γ (indexed Code El) z
    ua : (a b : Code) → El a ＝ El b → a ＝ b
    ua-β : (a b : Code) (p : El a ＝ El b) → ap El (ua a b p) ＝ p

------------------------------------------------------------------------
-- Methods

-- A method gives a point of P at an introduction from points at its
-- inputs. A path method carries any point of P at a along ua to any point
-- at b: the shape of a method for a recursive path constructor, whose
-- inductive hypotheses at both ends are variables.

module _
  {ℓ κ : Level} {γ : Desc {s = ℓ} (Set ℓ)} (U : Universe κ γ)
  where

  open Universe U using (Code; El; intro; ua)

  Method : {ν : Level} → (Code → Set ν) → Set (ℓ ⊔ κ ⊔ ν)
  Method P =
    (z : Shape γ (indexed Code El))
    → ((p : Position γ (indexed Code El) z)
      → P (input γ (indexed Code El) z p))
    → P (intro z)

  Path-method : {ν : Level} → (Code → Set ν) → Set (lsuc ℓ ⊔ κ ⊔ ν)
  Path-method P =
    (a b : Code) (p : El a ＝ El b) (x : P a) (y : P b)
    → transport P (ua a b p) x ＝ y

------------------------------------------------------------------------
-- Elimination

record Elimination
  {ℓ κ : Level} {γ : Desc {s = ℓ} (Set ℓ)} (U : Universe κ γ)
  (ν : Level) : Set (lsuc ℓ ⊔ κ ⊔ lsuc ν) where
  field
    elim :
      (P : Universe.Code U → Set ν) → Method U P → Path-method U P
      → (a : Universe.Code U) → P a
    elim-intro :
      (P : Universe.Code U → Set ν) (m : Method U P)
      (n : Path-method U P)
      (z : Shape γ (indexed (Universe.Code U) (Universe.El U)))
      → elim P m n (Universe.intro U z)
        ＝ m z
            (λ p →
              elim P m n
                (input γ (indexed (Universe.Code U) (Universe.El U)) z p))
    elim-ua :
      (P : Universe.Code U → Set ν) (m : Method U P)
      (n : Path-method U P) (a b : Universe.Code U)
      (p : Universe.El U a ＝ Universe.El U b)
      → apd (elim P m n) (Universe.ua U a b p)
        ＝ n a b p (elim P m n a) (elim P m n b)

------------------------------------------------------------------------
-- Lumsdaine's observation

-- Two points (a , p) and (b , q) of the fiber over X are joined by
-- ua a b (p ∙ q ⁻¹), along which p is carried to q by ua-β. A fiber is
-- then a set, so the loop at (a , refl) given by ua a a refl is trivial,
-- and so is its first component.

module _
  {ℓ κ : Level} {γ : Desc {s = ℓ} (Set ℓ)} (U : Universe κ γ)
  where

  open Universe U using (Code; El; ua; ua-β)

  fibers : (X : Set ℓ) → is-proposition (fiber El X)
  fibers X (a , p) (b , q) =
    to-Σ-＝ (ua a b (p ∙ q ⁻¹))
      ( transport-fiber El (ua a b (p ∙ q ⁻¹)) p
      ∙ ap (λ r → r ⁻¹ ∙ p) (ua-β a b (p ∙ q ⁻¹))
      ∙ inverse-difference-cancels p q)

  -- ua a a refl carries refl to refl.
  ua-refl-carries :
    (a : Code)
    → transport (λ c → El c ＝ El a) (ua a a refl) refl ＝ refl
  ua-refl-carries a =
    transport-fiber El (ua a a refl) refl
    ∙ ap (λ r → r ⁻¹ ∙ refl) (ua-β a a refl)

  ua-refl : (a : Code) → ua a a refl ＝ refl
  ua-refl a =
    ap-pr₁-to-Σ-＝ (ua a a refl) (ua-refl-carries a) ⁻¹
    ∙ ap (ap pr₁)
        (propositions-are-sets (fibers (El a)) (a , refl) (a , refl)
          (to-Σ-＝ (ua a a refl) (ua-refl-carries a)) refl)

------------------------------------------------------------------------
-- Elimination is induction into propositions

-- A path method at a and a, along ua a a refl ＝ refl, identifies any two
-- points of P a. Conversely a family of propositions has the path method
-- that identifies the carried point with the given one.

module _
  {ℓ κ : Level} {γ : Desc {s = ℓ} (Set ℓ)} (U : Universe κ γ)
  where

  open Universe U using (Code; ua)

  forced :
    {ν : Level} (P : Code → Set ν) → Path-method U P
    → (a : Code) → is-proposition (P a)
  forced P n a x y =
    ap (λ r → transport P r x) (ua-refl U a) ⁻¹ ∙ n a a refl x y

  propositional :
    {ν : Level} (P : Code → Set ν) → ((a : Code) → is-proposition (P a))
    → Path-method U P
  propositional P h a b p x y = h b (transport P (ua a b p) x) y

  induction :
    {ν : Level} → Elimination U ν → (P : Code → Set ν)
    → ((a : Code) → is-proposition (P a)) → Method U P
    → (a : Code) → P a
  induction E P h m = Elimination.elim E P m (propositional P h)
