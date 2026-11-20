{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Sorted.Realization.Cedents where

-- The two-sorted induction–recursive closure names exactly the derivable
-- names. Each code derives its interpretation, by induction on codes
-- (`derived`, `coded-derivable`), and every closure names the derivable
-- names under extensionality (`derivable-coded`, by
-- Cedents.derivable-named). The closure over the ambient reflection names
-- the same cedent (Naming.Cedents), so induction–recursion and the ambient
-- Mahlo rule give two small types of derivations of one inductive family,
-- each naming what the other names (`coded-sorted`, `sorted-coded`).

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
import SPT.Mahlo.Ambient as Ambient
import SPT.Mahlo.Specification as Specification

open import SPT.Mahlo.DS.Cedents using
  ( _⊆_; ∅ᶜ; Derivable
  ; empty; unit; two; natural; product; sum; tree; identity; result
  ; branch; derivable-named)
import SPT.Mahlo.DS.Naming as Naming
open import SPT.Mahlo.DS.Naming.Cedents using
  (named-derivable; derivable-sorted)
open import SPT.Mahlo.DS.Naming.Trees using (requests)
open import SPT.Mahlo.DS.Sorted using (Sort; decode; formers)
open import SPT.Mahlo.DS.Sorted.Realization.Discriminator using
  (Code; interpret; closure)
import SPT.Mahlo.DS.Sorted.Realization.Discriminator as IR

module _
  {ℓ κ : Level} {O : Set κ} (Ψ : Specification.Operator (decode ℓ O))
  where

  derived : (c : Code Ψ) → Derivable (formers ℓ O) Ψ ∅ᶜ (interpret Ψ c)
  derived IR.empty = empty
  derived IR.unit = unit
  derived IR.two = two
  derived IR.natural = natural
  derived (IR.product a b) =
    product (interpret Ψ a) (λ x → interpret Ψ (b x)) (derived a)
      (λ x → derived (b x))
  derived (IR.sum a b) =
    sum (interpret Ψ a) (λ x → interpret Ψ (b x)) (derived a)
      (λ x → derived (b x))
  derived (IR.tree a b) =
    tree (interpret Ψ a) (λ x → interpret Ψ (b x)) (derived a)
      (λ x → derived (b x))
  derived (IR.result a b) =
    result (interpret Ψ a) (λ x → interpret Ψ (b x)) (derived a)
      (λ x → derived (b x))
  derived (IR.identity a x y) = identity (interpret Ψ a) x y (derived a)
  derived (IR.branch a b y) =
    branch (interpret Ψ a) (λ x → interpret Ψ (b x)) (derived a)
      (λ x → derived (b x)) y

  coded-derivable :
    Specification.Name (interpret Ψ) ⊆ Derivable (formers ℓ O) Ψ ∅ᶜ
  coded-derivable n =
    transport (Derivable (formers ℓ O) Ψ ∅ᶜ) (pr₂ n) (derived (pr₁ n))

  derivable-coded :
    ((X : Set ℓ) → FunExt X (λ _ → Sort ℓ O))
    → Derivable (formers ℓ O) Ψ ∅ᶜ ⊆ Specification.Name (interpret Ψ)
  derivable-coded extensionality =
    derivable-named extensionality (closure Ψ)

  -- Both small types of derivations name the same names.
  module _
    {K : Set ℓ}
    (L : Specification.Closure (Ambient.formers ℓ)
      (requests (formers ℓ O) Ψ) K)
    (extensionality : (X : Set ℓ) → FunExt X (λ _ → Sort ℓ O))
    where

    coded-sorted :
      Specification.Name (interpret Ψ)
      ⊆ Specification.Name (Naming.sort (formers ℓ O) Ψ L)
    coded-sorted n =
      derivable-sorted (formers ℓ O) Ψ L extensionality
        (coded-derivable n)

    sorted-coded :
      Specification.Name (Naming.sort (formers ℓ O) Ψ L)
      ⊆ Specification.Name (interpret Ψ)
    sorted-coded n =
      derivable-coded extensionality
        (named-derivable (formers ℓ O) Ψ L n)
