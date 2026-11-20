{-# OPTIONS --safe --without-K #-}

module SPT.IR.Polynomial.Induction.Initiality where

-- Pointwise initiality of the inductions of Polynomial.Induction, with no
-- extensionality beyond the one introduction uses. Hypotheses are
-- functions on positions, so relatedness is pointwise, at the positions of
-- a layer (`Layer-Related`) and at the positions of an argument
-- (`Literal-Related`, at the valuation's own `literal-values`).
--
-- Induction pulled back along split is induction on derivations at the
-- method carried along the isomorphism of arguments and layers, so a
-- valuation with the lax law at arguments is related to it everywhere: the
-- law holds at the image of each argument, and the extension carries it to
-- every layer (`Lax`, `layer-law`, by `extension-preserves-predicates`),
-- where Polynomial.Generated.Initiality applies (`ind-unique-rel`).
--
-- Induction on literal arguments is that induction at the method reading
-- literal hypotheses through `transfer`, and `transfer` keeps relatedness:
-- by induction on the code, with `carry` undoing a transport of layers by
-- path induction (`carry-related`, `transfer-related`). So a valuation with
-- the lax law at literal hypotheses is related to it everywhere
-- (`Literal-Lax`, `source-unique-rel`).

open import SPT.Base
open import SPT.Foundation.HalfAdjoint.Extension using
  (extension-preserves-predicates)

open import SPT.IR.Polynomial using
  (Poly; var; con; sigma; pi; Args; info; shape; Scheme; Extensionality)
open import SPT.IR.Polynomial.Algebra using (Algebra)
open import SPT.IR.Polynomial.Generated using (Position; input)
import SPT.IR.Polynomial.Generated as Generated
import SPT.IR.Polynomial.Generated.Initiality as Derivations
import SPT.IR.Polynomial.Induction as Induction

module _
  {ℓ κ : Level} {s : Scheme ℓ κ} (M : Algebra s)
  (let G = Generated.generated M)
  where

  open Algebra M using (family)

  ----------------------------------------------------------------------
  -- Relatedness at positions

  module _
    {μ ν ρ : Level}
    (Q : (i : Scheme.Index s) → Generated.Carrier M i → Set μ)
    (P : (i : Scheme.Index s) → Generated.Carrier M i → Set ν)
    (C :
      (i : Scheme.Index s) (t : Generated.Carrier M i) → Q i t → P i t
      → Set ρ)
    where

    Layer-Related :
      {X : Set (ℓ ⊔ κ)} (p : Poly ℓ κ (Scheme.Data s) X)
      (l : Generated.Layer M p)
      → Induction.Hypotheses M Q p l → Induction.Hypotheses M P p l
      → Set (ℓ ⊔ ρ)
    Layer-Related p l h k =
      (z : Position p family (pr₁ l))
      → C (pr₁ (input p family (pr₁ l) z))
          (pr₂ (input p family (pr₁ l) z) , pr₂ l z) (h z) (k z)

    Literal-Related :
      {X : Set (ℓ ⊔ κ)} (p : Poly ℓ κ (Scheme.Data s) X) (a : Args p G)
      → Induction.Literal M Q p a → Induction.Literal M P p a
      → Set (ℓ ⊔ ρ)
    Literal-Related p a h k =
      (z : Position p G a)
      → C (pr₁ (input p G a z)) (pr₂ (input p G a z)) (h z) (k z)

  -- The hypotheses a valuation supplies at the positions of an argument.
  literal-values :
    {μ : Level}
    (Q : (i : Scheme.Index s) → Generated.Carrier M i → Set μ)
    (v : (i : Scheme.Index s) (t : Generated.Carrier M i) → Q i t)
    {X : Set (ℓ ⊔ κ)} (p : Poly ℓ κ (Scheme.Data s) X) (a : Args p G)
    → Induction.Literal M Q p a
  literal-values Q v p a z = v (pr₁ (input p G a z)) (pr₂ (input p G a z))

  ----------------------------------------------------------------------
  -- Induction pulled back along split

  module _
    {μ ν ρ : Level} (e : Extensionality ℓ κ)
    (Q : (i : Scheme.Index s) → Generated.Carrier M i → Set μ)
    (P : (i : Scheme.Index s) → Generated.Carrier M i → Set ν)
    (C :
      (i : Scheme.Index s) (t : Generated.Carrier M i) → Q i t → P i t
      → Set ρ)
    where

    Lax :
      ((i : Scheme.Index s) (t : Generated.Carrier M i) → Q i t)
      → Induction.Method M e P → Set (ℓ ⊔ ν ⊔ ρ)
    Lax v m =
      (i : Scheme.Index s) (a : Args (shape (Scheme.rule s i)) G)
      (k :
        Induction.Hypotheses M P (shape (Scheme.rule s i))
          (pr₁ (Generated.split M e (shape (Scheme.rule s i)) a)))
      → Layer-Related Q P C (shape (Scheme.rule s i))
          (pr₁ (Generated.split M e (shape (Scheme.rule s i)) a))
          (Induction.supplied M Q v (shape (Scheme.rule s i))
            (pr₁ (Generated.split M e (shape (Scheme.rule s i)) a)))
          k
      → C i (Generated.make M e i a) (v i (Generated.make M e i a)) (m i a k)

  module _
    {μ ν ρ : Level} (e : Extensionality ℓ κ)
    (Q : (i : Scheme.Index s) → Generated.Carrier M i → Set μ)
    (P : (i : Scheme.Index s) → Generated.Carrier M i → Set ν)
    (C :
      (i : Scheme.Index s) (t : Generated.Carrier M i) → Q i t → P i t
      → Set ρ)
    (v : (i : Scheme.Index s) (t : Generated.Carrier M i) → Q i t)
    (m : Induction.Method M e P) (law : Lax e Q P C v m)
    where

    -- The law at a layer, for a method there.
    Lawful :
      (i : Scheme.Index s) (l : Generated.Layer M (shape (Scheme.rule s i)))
      → ( Induction.Hypotheses M P (shape (Scheme.rule s i)) l
        → P i (Generated.introduce M i l))
      → Set (ℓ ⊔ ν ⊔ ρ)
    Lawful i l f =
      (k : Induction.Hypotheses M P (shape (Scheme.rule s i)) l)
      → Layer-Related Q P C (shape (Scheme.rule s i)) l
          (Induction.supplied M Q v (shape (Scheme.rule s i)) l) k
      → C i (Generated.introduce M i l) (v i (Generated.introduce M i l)) (f k)

    layer-law : Derivations.Lax M Q P C v (Induction.method M e P m)
    layer-law i l =
      extension-preserves-predicates
        (Induction.presented M e (shape (Scheme.rule s i)))
        (λ k →
          Induction.Hypotheses M P (shape (Scheme.rule s i)) k
          → P i (Generated.introduce M i k))
        (m i) (Lawful i) (law i) l

    opaque
      unfolding Induction.ind

      ind-unique-rel :
        (i : Scheme.Index s) (t : Generated.Carrier M i)
        → C i t (v i t) (Induction.ind M e P m i t)
      ind-unique-rel =
        Derivations.ind-unique-rel M Q P C v (Induction.method M e P m)
          layer-law

  ----------------------------------------------------------------------
  -- Induction on literal arguments

  module _
    {μ ν ρ : Level}
    (Q : (i : Scheme.Index s) → Generated.Carrier M i → Set μ)
    (P : (i : Scheme.Index s) → Generated.Carrier M i → Set ν)
    (C :
      (i : Scheme.Index s) (t : Generated.Carrier M i) → Q i t → P i t
      → Set ρ)
    (v : (i : Scheme.Index s) (t : Generated.Carrier M i) → Q i t)
    where

    -- Undoing a transport of layers keeps relatedness to the valuation.
    carry-related :
      {X : Set (ℓ ⊔ κ)} {Y : X → Set (ℓ ⊔ κ)}
      (q : (x : X) → Poly ℓ κ (Scheme.Data s) (Y x)) {x y : X} (c : x ＝ y)
      (l : Generated.Layer M (q x))
      (k :
        Induction.Hypotheses M P (q y)
          (transport (λ w → Generated.Layer M (q w)) c l))
      → Layer-Related Q P C (q y)
          (transport (λ w → Generated.Layer M (q w)) c l)
          (Induction.supplied M Q v (q y)
            (transport (λ w → Generated.Layer M (q w)) c l))
          k
      → Layer-Related Q P C (q x) l (Induction.supplied M Q v (q x) l)
          (Induction.carry M P q c l k)
    carry-related q refl l k r = r

    transfer-related :
      (e : Extensionality ℓ κ)
      {X : Set (ℓ ⊔ κ)} (p : Poly ℓ κ (Scheme.Data s) X) (a : Args p G)
      (k : Induction.Hypotheses M P p (pr₁ (Generated.split M e p a)))
      → Layer-Related Q P C p (pr₁ (Generated.split M e p a))
          (Induction.supplied M Q v p (pr₁ (Generated.split M e p a))) k
      → Literal-Related Q P C p a (literal-values Q v p a)
          (Induction.transfer M e P p a k)
    transfer-related e (var i) a k r z = r z
    transfer-related e (con A) a k r (lift ())
    transfer-related e (sigma p q) (a , b) k r (inl z) =
      transfer-related e p a (λ y → k (inl y)) (λ y → r (inl y)) z
    transfer-related e (sigma p q) (a , b) k r (inr z) =
      transfer-related e (q (info p G a)) b
        (Induction.carry M P q (pr₂ (Generated.split M e p a) ⁻¹)
          (pr₁ (Generated.split M e (q (info p G a)) b))
          (λ y → k (inr y)))
        (carry-related q (pr₂ (Generated.split M e p a) ⁻¹)
          (pr₁ (Generated.split M e (q (info p G a)) b))
          (λ y → k (inr y)) (λ y → r (inr y)))
        z
    transfer-related e (pi A p) f k r (x , z) =
      transfer-related e (p x) (f x) (λ y → k (x , y)) (λ y → r (x , y)) z

  module _
    {μ ν ρ : Level} (e : Extensionality ℓ κ)
    (Q : (i : Scheme.Index s) → Generated.Carrier M i → Set μ)
    (P : (i : Scheme.Index s) → Generated.Carrier M i → Set ν)
    (C :
      (i : Scheme.Index s) (t : Generated.Carrier M i) → Q i t → P i t
      → Set ρ)
    where

    Literal-Lax :
      ((i : Scheme.Index s) (t : Generated.Carrier M i) → Q i t)
      → Induction.Step M e P → Set (ℓ ⊔ ν ⊔ ρ)
    Literal-Lax v m =
      (i : Scheme.Index s) (a : Args (shape (Scheme.rule s i)) G)
      (k : Induction.Literal M P (shape (Scheme.rule s i)) a)
      → Literal-Related Q P C (shape (Scheme.rule s i)) a
          (literal-values Q v (shape (Scheme.rule s i)) a) k
      → C i (Generated.make M e i a) (v i (Generated.make M e i a)) (m i a k)

  module _
    {μ ν ρ : Level} (e : Extensionality ℓ κ)
    (Q : (i : Scheme.Index s) → Generated.Carrier M i → Set μ)
    (P : (i : Scheme.Index s) → Generated.Carrier M i → Set ν)
    (C :
      (i : Scheme.Index s) (t : Generated.Carrier M i) → Q i t → P i t
      → Set ρ)
    (v : (i : Scheme.Index s) (t : Generated.Carrier M i) → Q i t)
    (m : Induction.Step M e P) (law : Literal-Lax e Q P C v m)
    where

    source-unique-rel :
      (i : Scheme.Index s) (t : Generated.Carrier M i)
      → C i t (v i t) (Induction.source M e P m i t)
    source-unique-rel =
      ind-unique-rel e Q P C v
        (λ i a h →
          m i a (Induction.transfer M e P (shape (Scheme.rule s i)) a h))
        (λ i a k r →
          law i a (Induction.transfer M e P (shape (Scheme.rule s i)) a k)
            (transfer-related Q P C v e (shape (Scheme.rule s i)) a k r))
