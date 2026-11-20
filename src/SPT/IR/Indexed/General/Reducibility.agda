{-# OPTIONS --safe --without-K #-}

module SPT.IR.Indexed.General.Reducibility where

-- Kubánek's reducibility predicate for the external Mahlo universe
-- (Canonicity of the Mahlo Universe, MSc thesis, Chalmers 2025, §3.5) as a
-- general Dybjer–Setzer code (`reducibility`). The closed terms of one
-- Mahlo subuniverse Ma U0 El0 U+ El+ are parameters (`Syntax`), and so
-- are the predicates of his module (`Predicates`). The syntax's decoding
-- equations are absorbed into the types of the predicates: El0p reads
-- closed terms of El (El0' u), El+p those of El (El+' A B C), and U+p is
-- taken at El A and the family of El (B $$ a), the only instance El+'p
-- uses. His Map and Elp are the universal family at this code (`Map`,
-- `Elp`), with his two constructors at the indices they compute
-- (`El0'p`, `El+'p`), and his decoding clauses hold by refl
-- (`Elp-El0'p`, `Elp-El+'p`). His eliminator is Dybjer–Setzer induction
-- with curried methods, for any motive over Map (`MapElim`), and its two
-- computation equations hold by refl (`MapElim-El0'p`, `MapElim-El+'p`).
-- His own motive reads the syntactic eliminator maElim, which is object
-- syntax and not a parameter here.

open import SPT.Base

open import SPT.IR.Description.Indexed using
  (IDS; ι; σ; δ; General; general)
open import SPT.IR.Indexed using (U; value)
open import SPT.IR.General using (intro; Method; ind)
open import SPT.IR.Indexed.General using (universal)

------------------------------------------------------------------------
-- Closed terms of one Mahlo subuniverse, and the predicates

-- Ma: the closed terms of the subuniverse; El A: those of El $$ A;
-- U0: those of U0; Fam A: those of El $$ A → Ma, applied by _$$_; and
-- U+ A B: those of U+ $$ (El $$ A) $$ (lam (El[p] $$ (B[p] $$ q))).

record Syntax (ℓ : Level) : Set (lsuc ℓ) where
  infixl 15 _$$_
  field
    Ma : Set ℓ
    El : Ma → Set ℓ
    U0 : Set ℓ
    El0' : U0 → Ma
    Fam : Ma → Set ℓ
    _$$_ : {A : Ma} → Fam A → El A → Ma
    U+ : (A : Ma) → Fam A → Set ℓ
    El+' : (A : Ma) (B : Fam A) → U+ A B → Ma

record Predicates {ℓ : Level} (S : Syntax ℓ) : Set (lsuc ℓ) where
  open Syntax S
  field
    U0p : U0 → Set ℓ
    El0p : (u : U0) → U0p u → El (El0' u) → Set ℓ
    U+p :
      (A : Ma) (Ap : El A → Set ℓ) (B : Fam A)
      → ((a : El A) → Ap a → El (B $$ a) → Set ℓ) → U+ A B → Set ℓ
    El+p :
      (A : Ma) (Ap : El A → Set ℓ) (B : Fam A)
      (Bp : (a : El A) → Ap a → El (B $$ a) → Set ℓ) (C : U+ A B)
      → U+p A Ap B Bp C → El (El+' A B C) → Set ℓ

------------------------------------------------------------------------
-- The code

module _ {ℓ : Level} (S : Syntax ℓ) (R : Predicates S) where

  open Syntax S
  open Predicates R

  -- Mathematical shape, with P and Q the decodings of the recursive
  -- inputs:
  --
  --   El0'p : σ U0. σ (U0p u). ι (El0' u , El0p u up)
  --   El+'p : σ Ma. δ 𝟙 (λ _ → A). σ (Fam A).
  --           δ (Σ (El A) (P ⋆)) (λ p → B $$ pr₁ p). σ (U+ A B).
  --           σ (U+p A (P ⋆) B Q′ C). ι (El+' A B C , El+p A (P ⋆) B Q′ C Cp)
  --
  -- where Q′ a ap = Q (a , ap).

  Data : Ma → Set (lsuc ℓ)
  Data m = El m → Set ℓ

  branch : 𝟚 → General ℓ (lsuc ℓ) Ma Data
  branch ₀ = σ U0 (λ u → σ (U0p u) (λ up → ι (El0' u , El0p u up)))
  branch ₁ =
    σ Ma (λ A →
    δ (Lift ℓ 𝟙) (λ _ → A) (λ P →
    σ (Fam A) (λ B →
    δ (Σ (El A) (P (lift ⋆))) (λ p → B $$ pr₁ p) (λ Q →
    σ (U+ A B) (λ C →
    σ (U+p A (P (lift ⋆)) B (λ a ap → Q (a , ap)) C) (λ Cp →
    ι (El+' A B C , El+p A (P (lift ⋆)) B (λ a ap → Q (a , ap)) C Cp)))))))

  reducibility : General ℓ (lsuc ℓ) Ma Data
  reducibility = σ (Lift ℓ 𝟚) (λ t → branch (lower t))

------------------------------------------------------------------------
-- Map, Elp and the constructors

  Map : Ma → Set ℓ
  Map = U (general reducibility)

  Elp : (m : Ma) → Map m → El m → Set ℓ
  Elp = value (general reducibility)

  El0'p : (u : U0) → U0p u → Map (El0' u)
  El0'p u up = intro (universal reducibility) (lift ₀ , u , up , lift ⋆)

  El+'p :
    (A : Ma) (Ap : Map A) (B : Fam A)
    (Bp : (a : El A) → Elp A Ap a → Map (B $$ a)) (C : U+ A B)
    → U+p A (Elp A Ap) B (λ a ap → Elp (B $$ a) (Bp a ap)) C
    → Map (El+' A B C)
  El+'p A Ap B Bp C Cp =
    intro (universal reducibility)
      ( lift ₁ , A , (λ _ → Ap) , B , (λ p → Bp (pr₁ p) (pr₂ p)) , C , Cp
      , lift ⋆)

  Elp-El0'p : (u : U0) (up : U0p u) → Elp (El0' u) (El0'p u up) ＝ El0p u up
  Elp-El0'p u up = refl

  Elp-El+'p :
    (A : Ma) (Ap : Map A) (B : Fam A)
    (Bp : (a : El A) → Elp A Ap a → Map (B $$ a)) (C : U+ A B)
    (Cp : U+p A (Elp A Ap) B (λ a ap → Elp (B $$ a) (Bp a ap)) C)
    → Elp (El+' A B C) (El+'p A Ap B Bp C Cp)
      ＝ El+p A (Elp A Ap) B (λ a ap → Elp (B $$ a) (Bp a ap)) C Cp
  Elp-El+'p A Ap B Bp C Cp = refl

------------------------------------------------------------------------
-- The eliminator

  module _
    {ν : Level} (F : (m : Ma) → Map m → Set ν)
    (El0'm : (u : U0) (up : U0p u) → F (El0' u) (El0'p u up))
    (El+'m :
      (A : Ma) (Ap : Map A) → F A Ap
      → (B : Fam A) (Bp : (a : El A) → Elp A Ap a → Map (B $$ a))
      → ((a : El A) (ap : Elp A Ap a) → F (B $$ a) (Bp a ap))
      → (C : U+ A B)
        (Cp : U+p A (Elp A Ap) B (λ a ap → Elp (B $$ a) (Bp a ap)) C)
      → F (El+' A B C) (El+'p A Ap B Bp C Cp))
    where

    methods : Method (universal reducibility) F
    methods (lift ₀ , u , up , w) h = El0'm u up
    methods (lift ₁ , A , g , B , g′ , C , Cp , w) (k , k′ , h) =
      El+'m A (g (lift ⋆)) (k (lift ⋆)) B (λ a ap → g′ (a , ap))
        (λ a ap → k′ (a , ap)) C Cp

    MapElim : (m : Ma) (mp : Map m) → F m mp
    MapElim = ind (universal reducibility) F methods

    MapElim-El0'p :
      (u : U0) (up : U0p u) → MapElim (El0' u) (El0'p u up) ＝ El0'm u up
    MapElim-El0'p u up = refl

    MapElim-El+'p :
      (A : Ma) (Ap : Map A) (B : Fam A)
      (Bp : (a : El A) → Elp A Ap a → Map (B $$ a)) (C : U+ A B)
      (Cp : U+p A (Elp A Ap) B (λ a ap → Elp (B $$ a) (Bp a ap)) C)
      → MapElim (El+' A B C) (El+'p A Ap B Bp C Cp)
        ＝ El+'m A Ap (MapElim A Ap) B Bp
             (λ a ap → MapElim (B $$ a) (Bp a ap)) C Cp
    MapElim-El+'p A Ap B Bp C Cp = refl
