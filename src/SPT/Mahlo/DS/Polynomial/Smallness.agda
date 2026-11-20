{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Polynomial.Smallness where

-- Indexed polynomial induction–recursion from the smallness principle.
-- Smallness gives a closure of the frontier operator of any rules r, as a
-- small algebra of one Dybjer–Setzer description (Ambient, `closure`), and
-- the realization makes that closure a small algebra of r (`algebra`). Its
-- generated part carries the rules of indexed polynomial
-- induction–recursion for r: the carriers and their readout (`μ`, `value`),
-- introduction on arguments over the carriers themselves with its output
-- law (`make`, `make-β`), induction over derivations computing by refl
-- (`Method`, `ind`, `ind-β`), and a fold into every algebra of r that keeps
-- the readouts (`least`, `least-value`). Every element is an introduction
-- on literal arguments (`unroll`, `unroll-make`, `make-unroll`), and
-- elimination takes hypotheses at those arguments' own positions (`Step`,
-- `source`, `source-β`), by IR.Polynomial.Induction at this algebra.
-- Everything is under extensionality for families of information over the
-- arities, which contains the extensionality for families of types that
-- Ambient uses (`types`).

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)

import SPT.Mahlo.DS.Ambient as Ambient
open import SPT.IR.Polynomial using
  (Family; carrier; readout; Args; info; shape; output; Rules; scheme;
   Extensionality)
open import SPT.IR.Polynomial.Algebra using (Algebra)
import SPT.IR.Polynomial.Generated as Generated
import SPT.IR.Polynomial.Induction as Induction
import SPT.Mahlo.DS.Polynomial.Realization as Realization
open import SPT.IR.Smallness using (Smallness)

------------------------------------------------------------------------
-- Small algebras of every rules

-- Extensionality for families of types is the case of constant families.
types :
  {ℓ : Level} → Extensionality ℓ (lsuc ℓ)
  → (X : Set ℓ) → FunExt X (λ _ → Set ℓ)
types {ℓ} extensionality X = extensionality X (λ _ → Set ℓ)

algebra :
  {ℓ : Level} → Extensionality ℓ (lsuc ℓ) → Smallness ℓ → (r : Rules ℓ)
  → Algebra (scheme r)
algebra extensionality small r =
  Realization.algebra r
    ( Ambient.closure (types extensionality) (Realization.operator r)
        (Smallness.algebra small
          (Ambient.description (Realization.operator r)))
        (Smallness.law small (Ambient.description (Realization.operator r))))
    extensionality

------------------------------------------------------------------------
-- The rules of indexed polynomial induction–recursion

module _
  {ℓ : Level} (extensionality : Extensionality ℓ (lsuc ℓ))
  (small : Smallness ℓ) (r : Rules ℓ)
  where

  μ : Rules.Index r → Set ℓ
  μ = Generated.Carrier (algebra extensionality small r)

  value : (i : Rules.Index r) → μ i → Set ℓ
  value = readout (Generated.generated (algebra extensionality small r))

  make :
    (i : Rules.Index r)
    → Args (shape (Rules.rule r i))
        (Generated.generated (algebra extensionality small r))
    → μ i
  make = Generated.make (algebra extensionality small r) extensionality

  make-β :
    (i : Rules.Index r)
    (a : Args (shape (Rules.rule r i))
           (Generated.generated (algebra extensionality small r)))
    → value i (make i a)
      ＝ output (Rules.rule r i)
          (info (shape (Rules.rule r i))
            (Generated.generated (algebra extensionality small r)) a)
  make-β = Generated.make-β (algebra extensionality small r) extensionality

  Method :
    {ν : Level} → ((i : Rules.Index r) → μ i → Set ν) → Set (ℓ ⊔ ν)
  Method = Generated.Method (algebra extensionality small r)

  ind :
    {ν : Level} (P : (i : Rules.Index r) → μ i → Set ν) → Method P
    → (i : Rules.Index r) (t : μ i) → P i t
  ind = Generated.ind (algebra extensionality small r)

  ind-β :
    {ν : Level} (P : (i : Rules.Index r) → μ i → Set ν) (method : Method P)
    (i : Rules.Index r)
    (l : Generated.Layer (algebra extensionality small r)
           (shape (Rules.rule r i)))
    → ind P method i (Generated.introduce (algebra extensionality small r) i l)
      ＝ method i l
          (λ z →
            ind P method
              (pr₁
                (Generated.input (shape (Rules.rule r i))
                  (Algebra.family (algebra extensionality small r))
                  (pr₁ l) z))
              ( pr₂
                  (Generated.input (shape (Rules.rule r i))
                    (Algebra.family (algebra extensionality small r))
                    (pr₁ l) z)
              , pr₂ l z))
  ind-β = Generated.ind-β (algebra extensionality small r)

  least :
    (N : Algebra (scheme r)) (i : Rules.Index r) → μ i
    → carrier (Algebra.family N) i
  least = Generated.fold (algebra extensionality small r) extensionality

  least-value :
    (N : Algebra (scheme r)) (i : Rules.Index r) (t : μ i)
    → readout (Algebra.family N) i (least N i t) ＝ value i t
  least-value =
    Generated.fold-value (algebra extensionality small r) extensionality

------------------------------------------------------------------------
-- The rules on literal arguments

module _
  {ℓ : Level} (extensionality : Extensionality ℓ (lsuc ℓ))
  (small : Smallness ℓ) (r : Rules ℓ)
  where

  unroll :
    (i : Rules.Index r) → μ extensionality small r i
    → Args (shape (Rules.rule r i))
        (Generated.generated (algebra extensionality small r))
  unroll = Induction.unroll (algebra extensionality small r) extensionality

  unroll-make :
    (i : Rules.Index r)
    (a : Args (shape (Rules.rule r i))
           (Generated.generated (algebra extensionality small r)))
    → unroll i (make extensionality small r i a) ＝ a
  unroll-make =
    Induction.unroll-make (algebra extensionality small r) extensionality

  make-unroll :
    (i : Rules.Index r) (t : μ extensionality small r i)
    → make extensionality small r i (unroll i t) ＝ t
  make-unroll =
    Induction.make-unroll (algebra extensionality small r) extensionality

  Step :
    {ν : Level}
    → ((i : Rules.Index r) → μ extensionality small r i → Set ν)
    → Set (ℓ ⊔ ν)
  Step = Induction.Step (algebra extensionality small r) extensionality

  source :
    {ν : Level}
    (P : (i : Rules.Index r) → μ extensionality small r i → Set ν)
    → Step P → (i : Rules.Index r) (t : μ extensionality small r i) → P i t
  source = Induction.source (algebra extensionality small r) extensionality

  source-β :
    {ν : Level}
    (P : (i : Rules.Index r) → μ extensionality small r i → Set ν)
    → ((A : Set ℓ) (B : A → Set ν) → FunExt A B)
    → (m : Step P) (i : Rules.Index r)
      (a : Args (shape (Rules.rule r i))
             (Generated.generated (algebra extensionality small r)))
    → source P m i (make extensionality small r i a)
      ＝ m i a
          (λ z →
            source P m
              (pr₁
                (Generated.input (shape (Rules.rule r i))
                  (Generated.generated (algebra extensionality small r))
                  a z))
              (pr₂
                (Generated.input (shape (Rules.rule r i))
                  (Generated.generated (algebra extensionality small r))
                  a z)))
  source-β =
    Induction.source-β (algebra extensionality small r) extensionality
