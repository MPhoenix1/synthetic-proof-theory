{-# OPTIONS --safe --without-K #-}

module SPT.IR.Indexed.General.Reducibility.Kripke.Neutral.Initiality where

-- Uniqueness for Kubánek's predicate with neutral codes (Kripke/Neutral),
-- from the initiality of Dybjer–Setzer's rule. Restriction is the only
-- valuation with its three constructor equations, at every arrow
-- (`restricted-unique`), and its three laws are relational uniqueness
-- (`restriction-identity`, `restriction-composition`,
-- `restriction-monotone`). The eliminator is unique when its El+'p method
-- respects agreement, and for every method under extensionality
-- (`MapElim-unique`, `MapElim-unique-ext`). The readback of codes needs
-- neither, its methods reading hypotheses at points (`reify-code-unique`);
-- the joint readback is unique under extensionality
-- (`readback-unique-ext`).
--
-- The laws at the codes of Reducibility/Kripke are Kripke/Initiality's at
-- the extended code, with one clause more each, for neutral codes.

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)

open import SPT.IR.Indexed using (U)
open import SPT.IR.General.Initiality using
  (Lax; ind-unique-rel; Congruent; Homomorphic; ind-unique; congruent)
open import SPT.IR.Indexed.General using (universal)
open import SPT.IR.Indexed.General.Initiality using (universal-initiality)
open import SPT.IR.Indexed.General.Reducibility using (Syntax)
open import SPT.IR.Indexed.General.Reducibility.Kripke using
  ( Ma♯; El♯; U0♯; El0'♯; Fam♯; applied; U+♯; El+'♯; Predicates; U0p
  ; U+p; Index)
open import SPT.IR.Indexed.General.Reducibility.Kripke.Neutral using
  ( Forms; Neutral-Code; Normal-Code; Extension; module Extension; Readback
  ; reducibility; Map; Elp; El0'p; El+'p; nep; Restricted; restricting
  ; restricted; Motive; methods; MapElim; Readable; readback-base
  ; readback-plus; readback-neutral; readback; fresh-reducible
  ; family-readback; Reified; plus-reified; reify-base; reify-plus
  ; reify-neutral; reify-code)
open import SPT.Foundation.Kripke using
  (Stages; Stage; Arrow; compose; identity; restrict; shift)
open import SPT.IR.Description.Indexed using (general)

------------------------------------------------------------------------
-- Restriction is determined by its constructor equations

-- A valuation into restriction's motive is compared with restriction at
-- every arrow. Restriction's method does not read its hypotheses, so the
-- lax law at the pointwise relation is the three constructor equations.

module _
  {ℓ : Level} (T : Stages ℓ) (S : Stage T → Syntax ℓ) (F : Forms T S)
  (R : Predicates T S)
  where

  record Restriction
    (ρ : (c : Stage T) (m : Ma♯ T S c) → Map T S F R c m
      → (d : Stage T) (ψ : Arrow T d c) → Map T S F R d (m ·⟨ T ⟩ ψ))
    : Set ℓ where
    field
      restricts-El0'p :
        (c : Stage T) (u : U0♯ T S c) (up : U0p T S R c u)
        (d : Stage T) (ψ : Arrow T d c)
        → ρ c (El0'♯ T S c u) (El0'p T S F R c u up) d ψ
          ＝ El0'p T S F R d (u ·⟨ T ⟩ ψ) (shift T up ψ)
      restricts-El+'p :
        (c : Stage T) (A : Ma♯ T S c)
        (Ap : (d : Stage T) (φ : Arrow T d c) → Map T S F R d (A ·⟨ T ⟩ φ))
        (B : Fam♯ T S c A)
        (Bp :
          (d : Stage T) (φ : Arrow T d c) (a : El♯ T S d (A ·⟨ T ⟩ φ))
          → Elp T S F R d (A ·⟨ T ⟩ φ) (Ap d φ) a
          → Map T S F R d (applied T S d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a))
        (C : U+♯ T S c A B)
        (Cp :
          U+p T S R c A (λ d φ → Elp T S F R d (A ·⟨ T ⟩ φ) (Ap d φ)) B
            (λ d φ a ap →
              Elp T S F R d (applied T S d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a)
                (Bp d φ a ap))
            C)
        (d : Stage T) (ψ : Arrow T d c)
        → ρ c (El+'♯ T S c A B C) (El+'p T S F R c A Ap B Bp C Cp) d ψ
          ＝ El+'p T S F R d (A ·⟨ T ⟩ ψ) (shift T Ap ψ) (B ·⟨ T ⟩ ψ)
               (shift T Bp ψ) (C ·⟨ T ⟩ ψ) (shift T Cp ψ)
      restricts-nep :
        (c : Stage T) (m : Ma♯ T S c) (mn : Neutral-Code T S F c m)
        (d : Stage T) (ψ : Arrow T d c)
        → ρ c m (nep T S F R c m mn) d ψ
          ＝ nep T S F R d (m ·⟨ T ⟩ ψ) (shift T mn ψ)

  Pointwise :
    (i : Index T S R) (mp : U (general (reducibility T S F R)) i)
    → Restricted T S F R i mp → Restricted T S F R i mp → Set ℓ
  Pointwise i mp r r′ =
    (d : Stage T) (ψ : Arrow T d (pr₁ i)) → r d ψ ＝ r′ d ψ

  restriction-law :
    (ρ : (c : Stage T) (m : Ma♯ T S c) → Map T S F R c m
      → (d : Stage T) (ψ : Arrow T d c) → Map T S F R d (m ·⟨ T ⟩ ψ))
    → Restriction ρ
    → Lax (universal (reducibility T S F R)) (Restricted T S F R)
        (Restricted T S F R)
        Pointwise (λ i u → ρ (pr₁ i) (pr₂ i) u) (restricting T S F R)
  restriction-law ρ equations (lift ₀ , lift ₀ , c , u , up , w) k r =
    Restriction.restricts-El0'p equations c u up
  restriction-law ρ equations
    (lift ₀ , lift ₁ , c , A , g , B , g′ , C , Cp , w) k r =
    Restriction.restricts-El+'p equations c A (λ d φ → g (d , φ)) B
      (λ d φ a ap → g′ (d , φ , a , ap)) C Cp
  restriction-law ρ equations (lift ₁ , c , m , mn , w) k r =
    Restriction.restricts-nep equations c m mn

  restricted-unique :
    (ρ : (c : Stage T) (m : Ma♯ T S c) → Map T S F R c m
      → (d : Stage T) (ψ : Arrow T d c) → Map T S F R d (m ·⟨ T ⟩ ψ))
    → Restriction ρ
    → (c : Stage T) (m : Ma♯ T S c) (mp : Map T S F R c m)
      (d : Stage T) (ψ : Arrow T d c)
    → ρ c m mp d ψ ＝ restricted T S F R c m mp d ψ
  restricted-unique ρ equations c m =
    ind-unique-rel (universal (reducibility T S F R))
      (universal-initiality (reducibility T S F R)) (Restricted T S F R)
      (Restricted T S F R) Pointwise (λ i u → ρ (pr₁ i) (pr₂ i) u)
      (restricting T S F R) (restriction-law ρ equations) (c , m)

  restricted-restricts : Restriction (restricted T S F R)
  restricted-restricts = record
    { restricts-El0'p = λ c u up d ψ → refl
    ; restricts-El+'p = λ c A Ap B Bp C Cp d ψ → refl
    ; restricts-nep = λ c m mn d ψ → refl
    }

------------------------------------------------------------------------
-- The laws of restriction

-- Each law is relational uniqueness against restriction, at one relation,
-- as in Kripke/Initiality: `Unchanged`, `Composite`, `Carried`. Each lax
-- law is refl or a shift at the three constructors.

module _
  {ℓ : Level} (T : Stages ℓ) (S : Stage T → Syntax ℓ) (F : Forms T S)
  (R : Predicates T S)
  where

  Elements :
    (i : Index T S R) → U (general (reducibility T S F R)) i → Set ℓ
  Elements i mp = U (general (reducibility T S F R)) i

  Unchanged :
    (i : Index T S R) (mp : U (general (reducibility T S F R)) i)
    → Elements i mp → Restricted T S F R i mp → Set ℓ
  Unchanged i mp x r = r (pr₁ i) (identity T) ＝ x

  identity-lax :
    Lax (universal (reducibility T S F R)) Elements (Restricted T S F R)
      Unchanged
      (λ i mp → mp) (restricting T S F R)
  identity-lax (lift ₀ , lift ₀ , c , u , up , w) k r = refl
  identity-lax (lift ₀ , lift ₁ , c , A , g , B , g′ , C , Cp , w) k r = refl
  identity-lax (lift ₁ , c , m , mn , w) k r = refl

  restriction-identity :
    (c : Stage T) (m : Ma♯ T S c) (mp : Map T S F R c m)
    → restricted T S F R c m mp c (identity T) ＝ mp
  restriction-identity c m =
    ind-unique-rel (universal (reducibility T S F R))
      (universal-initiality (reducibility T S F R)) Elements
      (Restricted T S F R)
      Unchanged (λ i mp → mp) (restricting T S F R) identity-lax (c , m)

  Composite :
    (i : Index T S R) (mp : U (general (reducibility T S F R)) i)
    → Restricted T S F R i mp → Restricted T S F R i mp → Set ℓ
  Composite i mp r r′ =
    (d : Stage T) (ψ : Arrow T d (pr₁ i)) (d′ : Stage T) (ψ′ : Arrow T d′ d)
    → restricted T S F R d (pr₂ i ·⟨ T ⟩ ψ) (r d ψ) d′ ψ′
      ＝ r′ d′ (ψ ⊚⟨ T ⟩ ψ′)

  -- El+'p restricted twice, by refl, on its curried arguments, as in
  -- Kripke/Initiality.
  restricted-twice-El+'p :
    (c : Stage T) (A : Ma♯ T S c)
    (Ap : (d : Stage T) (φ : Arrow T d c) → Map T S F R d (A ·⟨ T ⟩ φ))
    (B : Fam♯ T S c A)
    (Bp :
      (d : Stage T) (φ : Arrow T d c) (a : El♯ T S d (A ·⟨ T ⟩ φ))
      → Elp T S F R d (A ·⟨ T ⟩ φ) (Ap d φ) a
      → Map T S F R d (applied T S d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a))
    (C : U+♯ T S c A B)
    (Cp :
      U+p T S R c A (λ d φ → Elp T S F R d (A ·⟨ T ⟩ φ) (Ap d φ)) B
        (λ d φ a ap →
          Elp T S F R d (applied T S d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a)
            (Bp d φ a ap))
        C)
    (d : Stage T) (ψ : Arrow T d c) (d′ : Stage T) (ψ′ : Arrow T d′ d)
    → restricted T S F R d (El+'♯ T S c A B C ·⟨ T ⟩ ψ)
        (restricted T S F R c (El+'♯ T S c A B C)
          (El+'p T S F R c A Ap B Bp C Cp) d ψ)
        d′ ψ′
      ＝ El+'p T S F R d′ (A ·⟨ T ⟩ (ψ ⊚⟨ T ⟩ ψ′))
           (shift T Ap (ψ ⊚⟨ T ⟩ ψ′)) (B ·⟨ T ⟩ (ψ ⊚⟨ T ⟩ ψ′))
           (shift T Bp (ψ ⊚⟨ T ⟩ ψ′)) (C ·⟨ T ⟩ (ψ ⊚⟨ T ⟩ ψ′))
           (shift T Cp (ψ ⊚⟨ T ⟩ ψ′))
  restricted-twice-El+'p c A Ap B Bp C Cp d ψ d′ ψ′ = refl

  composition-lax :
    Lax (universal (reducibility T S F R)) (Restricted T S F R)
      (Restricted T S F R)
      Composite (λ i → restricted T S F R (pr₁ i) (pr₂ i))
      (restricting T S F R)
  composition-lax (lift ₀ , lift ₀ , c , u , up , w) k r d ψ d′ ψ′ = refl
  composition-lax
    (lift ₀ , lift ₁ , c , A , g , B , g′ , C , Cp , w) k r d ψ d′ ψ′ =
    restricted-twice-El+'p c A (λ d₁ φ → g (d₁ , φ)) B
      (λ d₁ φ a ap → g′ (d₁ , φ , a , ap)) C Cp d ψ d′ ψ′
  composition-lax (lift ₁ , c , m , mn , w) k r d ψ d′ ψ′ = refl

  restriction-composition :
    (c : Stage T) (m : Ma♯ T S c) (mp : Map T S F R c m)
    (d : Stage T) (ψ : Arrow T d c) (d′ : Stage T) (ψ′ : Arrow T d′ d)
    → restricted T S F R d (m ·⟨ T ⟩ ψ) (restricted T S F R c m mp d ψ) d′ ψ′
      ＝ restricted T S F R c m mp d′ (ψ ⊚⟨ T ⟩ ψ′)
  restriction-composition c m =
    ind-unique-rel (universal (reducibility T S F R))
      (universal-initiality (reducibility T S F R)) (Restricted T S F R)
      (Restricted T S F R) Composite
      (λ i → restricted T S F R (pr₁ i) (pr₂ i)) (restricting T S F R)
      composition-lax (c , m)

  Carried :
    (i : Index T S R) (mp : U (general (reducibility T S F R)) i)
    → Restricted T S F R i mp → Restricted T S F R i mp → Set ℓ
  Carried i mp r r′ =
    (d : Stage T) (ψ : Arrow T d (pr₁ i)) (a : El♯ T S (pr₁ i) (pr₂ i))
    → Elp T S F R (pr₁ i) (pr₂ i) mp a
    → Elp T S F R d (pr₂ i ·⟨ T ⟩ ψ) (r d ψ) (a ·⟨ T ⟩ ψ)

  monotone-lax :
    Lax (universal (reducibility T S F R)) (Restricted T S F R)
      (Restricted T S F R)
      Carried (λ i → restricted T S F R (pr₁ i) (pr₂ i))
      (restricting T S F R)
  monotone-lax (lift ₀ , lift ₀ , c , u , up , w) k r d ψ a ap = shift T ap ψ
  monotone-lax
    (lift ₀ , lift ₁ , c , A , g , B , g′ , C , Cp , w) k r d ψ a ap =
    shift T ap ψ
  monotone-lax (lift ₁ , c , m , mn , w) k r d ψ a ap = shift T ap ψ

  restriction-monotone :
    (c : Stage T) (m : Ma♯ T S c) (mp : Map T S F R c m)
    (d : Stage T) (ψ : Arrow T d c) (a : El♯ T S c m)
    → Elp T S F R c m mp a
    → Elp T S F R d (m ·⟨ T ⟩ ψ) (restricted T S F R c m mp d ψ) (a ·⟨ T ⟩ ψ)
  restriction-monotone c m =
    ind-unique-rel (universal (reducibility T S F R))
      (universal-initiality (reducibility T S F R)) (Restricted T S F R)
      (Restricted T S F R) Carried
      (λ i → restricted T S F R (pr₁ i) (pr₂ i)) (restricting T S F R)
      monotone-lax (c , m)

------------------------------------------------------------------------
-- The eliminator is determined by its computation equations

-- The method for El+'p respects agreement when hypotheses agreeing at
-- every arrow give the same value. With it, and with the three computation
-- equations, a valuation is the eliminator; under extensionality for
-- families over the arities every method respects agreement.

module _
  {ℓ ν : Level} (T : Stages ℓ) (S : Stage T → Syntax ℓ) (F : Forms T S)
  (R : Predicates T S)
  (M : (c : Stage T) (m : Ma♯ T S c) → Map T S F R c m → Set ν)
  (El+'m :
    (c : Stage T) (A : Ma♯ T S c)
    (Ap : (d : Stage T) (φ : Arrow T d c) → Map T S F R d (A ·⟨ T ⟩ φ))
    → ((d : Stage T) (φ : Arrow T d c) → M d (A ·⟨ T ⟩ φ) (Ap d φ))
    → (B : Fam♯ T S c A)
      (Bp :
        (d : Stage T) (φ : Arrow T d c) (a : El♯ T S d (A ·⟨ T ⟩ φ))
        → Elp T S F R d (A ·⟨ T ⟩ φ) (Ap d φ) a
        → Map T S F R d (applied T S d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a))
    → ( (d : Stage T) (φ : Arrow T d c) (a : El♯ T S d (A ·⟨ T ⟩ φ))
        (ap : Elp T S F R d (A ·⟨ T ⟩ φ) (Ap d φ) a)
        → M d (applied T S d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a) (Bp d φ a ap))
    → (C : U+♯ T S c A B)
      (Cp :
        U+p T S R c A (λ d φ → Elp T S F R d (A ·⟨ T ⟩ φ) (Ap d φ)) B
          (λ d φ a ap →
            Elp T S F R d (applied T S d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a)
              (Bp d φ a ap))
          C)
    → M c (El+'♯ T S c A B C) (El+'p T S F R c A Ap B Bp C Cp))
  where

  Respects : Set (ℓ ⊔ ν)
  Respects =
    (c : Stage T) (A : Ma♯ T S c)
    (Ap : (d : Stage T) (φ : Arrow T d c) → Map T S F R d (A ·⟨ T ⟩ φ))
    (h h′ : (d : Stage T) (φ : Arrow T d c) → M d (A ·⟨ T ⟩ φ) (Ap d φ))
    → ((d : Stage T) (φ : Arrow T d c) → h d φ ＝ h′ d φ)
    → (B : Fam♯ T S c A)
      (Bp :
        (d : Stage T) (φ : Arrow T d c) (a : El♯ T S d (A ·⟨ T ⟩ φ))
        → Elp T S F R d (A ·⟨ T ⟩ φ) (Ap d φ) a
        → Map T S F R d (applied T S d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a))
      (k k′ :
        (d : Stage T) (φ : Arrow T d c) (a : El♯ T S d (A ·⟨ T ⟩ φ))
        (ap : Elp T S F R d (A ·⟨ T ⟩ φ) (Ap d φ) a)
        → M d (applied T S d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a) (Bp d φ a ap))
    → ( (d : Stage T) (φ : Arrow T d c) (a : El♯ T S d (A ·⟨ T ⟩ φ))
        (ap : Elp T S F R d (A ·⟨ T ⟩ φ) (Ap d φ) a)
        → k d φ a ap ＝ k′ d φ a ap)
    → (C : U+♯ T S c A B)
      (Cp :
        U+p T S R c A (λ d φ → Elp T S F R d (A ·⟨ T ⟩ φ) (Ap d φ)) B
          (λ d φ a ap →
            Elp T S F R d (applied T S d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a)
              (Bp d φ a ap))
          C)
    → El+'m c A Ap h B Bp k C Cp ＝ El+'m c A Ap h′ B Bp k′ C Cp

module _
  {ℓ ν : Level} (T : Stages ℓ) (S : Stage T → Syntax ℓ) (F : Forms T S)
  (R : Predicates T S)
  (M : (c : Stage T) (m : Ma♯ T S c) → Map T S F R c m → Set ν)
  (El0'm :
    (c : Stage T) (u : U0♯ T S c) (up : U0p T S R c u)
    → M c (El0'♯ T S c u) (El0'p T S F R c u up))
  (El+'m :
    (c : Stage T) (A : Ma♯ T S c)
    (Ap : (d : Stage T) (φ : Arrow T d c) → Map T S F R d (A ·⟨ T ⟩ φ))
    → ((d : Stage T) (φ : Arrow T d c) → M d (A ·⟨ T ⟩ φ) (Ap d φ))
    → (B : Fam♯ T S c A)
      (Bp :
        (d : Stage T) (φ : Arrow T d c) (a : El♯ T S d (A ·⟨ T ⟩ φ))
        → Elp T S F R d (A ·⟨ T ⟩ φ) (Ap d φ) a
        → Map T S F R d (applied T S d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a))
    → ( (d : Stage T) (φ : Arrow T d c) (a : El♯ T S d (A ·⟨ T ⟩ φ))
        (ap : Elp T S F R d (A ·⟨ T ⟩ φ) (Ap d φ) a)
        → M d (applied T S d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a) (Bp d φ a ap))
    → (C : U+♯ T S c A B)
      (Cp :
        U+p T S R c A (λ d φ → Elp T S F R d (A ·⟨ T ⟩ φ) (Ap d φ)) B
          (λ d φ a ap →
            Elp T S F R d (applied T S d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a)
              (Bp d φ a ap))
          C)
    → M c (El+'♯ T S c A B C) (El+'p T S F R c A Ap B Bp C Cp))
  (nem :
    (c : Stage T) (m : Ma♯ T S c) (mn : Neutral-Code T S F c m)
    → M c m (nep T S F R c m mn))
  where

  record Computation
    (v : (c : Stage T) (m : Ma♯ T S c) (mp : Map T S F R c m) → M c m mp)
    : Set (ℓ ⊔ ν) where
    field
      computes-El0'p :
        (c : Stage T) (u : U0♯ T S c) (up : U0p T S R c u)
        → v c (El0'♯ T S c u) (El0'p T S F R c u up) ＝ El0'm c u up
      computes-El+'p :
        (c : Stage T) (A : Ma♯ T S c)
        (Ap : (d : Stage T) (φ : Arrow T d c) → Map T S F R d (A ·⟨ T ⟩ φ))
        (B : Fam♯ T S c A)
        (Bp :
          (d : Stage T) (φ : Arrow T d c) (a : El♯ T S d (A ·⟨ T ⟩ φ))
          → Elp T S F R d (A ·⟨ T ⟩ φ) (Ap d φ) a
          → Map T S F R d (applied T S d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a))
        (C : U+♯ T S c A B)
        (Cp :
          U+p T S R c A (λ d φ → Elp T S F R d (A ·⟨ T ⟩ φ) (Ap d φ)) B
            (λ d φ a ap →
              Elp T S F R d (applied T S d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a)
                (Bp d φ a ap))
            C)
        → v c (El+'♯ T S c A B C) (El+'p T S F R c A Ap B Bp C Cp)
          ＝ El+'m c A Ap (λ d φ → v d (A ·⟨ T ⟩ φ) (Ap d φ)) B Bp
               (λ d φ a ap →
                 v d (applied T S d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a)
                   (Bp d φ a ap))
               C Cp
      computes-nep :
        (c : Stage T) (m : Ma♯ T S c) (mn : Neutral-Code T S F c m)
        → v c m (nep T S F R c m mn) ＝ nem c m mn

  homomorphic :
    (v : (c : Stage T) (m : Ma♯ T S c) (mp : Map T S F R c m) → M c m mp)
    → Computation v
    → Homomorphic (universal (reducibility T S F R))
        (Motive T S F R M El0'm El+'m nem)
        (λ i u → v (pr₁ i) (pr₂ i) u)
        (methods T S F R M El0'm El+'m nem)
  homomorphic v equations (lift ₀ , lift ₀ , c , u , up , w) =
    Computation.computes-El0'p equations c u up
  homomorphic v equations
    (lift ₀ , lift ₁ , c , A , g , B , g′ , C , Cp , w) =
    Computation.computes-El+'p equations c A (λ d φ → g (d , φ)) B
      (λ d φ a ap → g′ (d , φ , a , ap)) C Cp
  homomorphic v equations (lift ₁ , c , m , mn , w) =
    Computation.computes-nep equations c m mn

  congruence :
    Respects T S F R M El+'m
    → Congruent (universal (reducibility T S F R))
        (Motive T S F R M El0'm El+'m nem)
        (methods T S F R M El0'm El+'m nem)
  congruence respects (lift ₀ , lift ₀ , c , u , up , w) h k r = refl
  congruence respects
    (lift ₀ , lift ₁ , c , A , g , B , g′ , C , Cp , w)
    (h , h′ , h″) (k , k′ , k″) (r , r′ , r″) =
    respects c A (λ d φ → g (d , φ))
      (λ d φ → h (d , φ)) (λ d φ → k (d , φ)) (λ d φ → r (d , φ)) B
      (λ d φ a ap → g′ (d , φ , a , ap))
      (λ d φ a ap → h′ (d , φ , a , ap))
      (λ d φ a ap → k′ (d , φ , a , ap))
      (λ d φ a ap → r′ (d , φ , a , ap)) C Cp
  congruence respects (lift ₁ , c , m , mn , w) h k r = refl

  MapElim-unique :
    (v : (c : Stage T) (m : Ma♯ T S c) (mp : Map T S F R c m) → M c m mp)
    → Respects T S F R M El+'m → Computation v
    → (c : Stage T) (m : Ma♯ T S c) (mp : Map T S F R c m)
    → v c m mp ＝ MapElim T S F R M El0'm El+'m nem c m mp
  MapElim-unique v respects equations c m =
    ind-unique (universal (reducibility T S F R))
      (universal-initiality (reducibility T S F R))
      (Motive T S F R M El0'm El+'m nem)
      (λ i u → v (pr₁ i) (pr₂ i) u) (methods T S F R M El0'm El+'m nem)
      (congruence respects) (homomorphic v equations) (c , m)

  MapElim-unique-ext :
    ((A : Set ℓ) (Y : A → Set ν) → FunExt A Y)
    → (v : (c : Stage T) (m : Ma♯ T S c) (mp : Map T S F R c m) → M c m mp)
    → Computation v
    → (c : Stage T) (m : Ma♯ T S c) (mp : Map T S F R c m)
    → v c m mp ＝ MapElim T S F R M El0'm El+'m nem c m mp
  MapElim-unique-ext extensionality v equations c m =
    ind-unique (universal (reducibility T S F R))
      (universal-initiality (reducibility T S F R))
      (Motive T S F R M El0'm El+'m nem)
      (λ i u → v (pr₁ i) (pr₂ i) u) (methods T S F R M El0'm El+'m nem)
      ( congruent extensionality (universal (reducibility T S F R))
          (Motive T S F R M El0'm El+'m nem)
          (methods T S F R M El0'm El+'m nem))
      (homomorphic v equations) (c , m)

  MapElim-computes : Computation (MapElim T S F R M El0'm El+'m nem)
  MapElim-computes = record
    { computes-El0'p = λ c u up → refl
    ; computes-El+'p = λ c A Ap B Bp C Cp → refl
    ; computes-nep = λ c m mn → refl
    }

------------------------------------------------------------------------
-- The readback of codes is determined by its equations

-- Its values are functions on arrows, so uniqueness is at agreement on
-- every arrow. Its El+'p method reads the hypothesis for the recursive
-- input at the identity and the family's at the fresh variable, so
-- hypotheses agreeing at every arrow give equal values, with no
-- extensionality (`family-respects`, `reify-plus-respects`).

module _
  {ℓ : Level} (T : Stages ℓ) (S : Stage T → Syntax ℓ) (F : Forms T S)
  (R : Predicates T S) (H : Readback T S F R) (V : Extension T S F)
  (let Reifying =
         Motive T S F R (Reified T S F R H V) (reify-base T S F R H V)
           (reify-plus T S F R H V) (reify-neutral T S F R H V))
  (let reifying =
         methods T S F R (Reified T S F R H V) (reify-base T S F R H V)
           (reify-plus T S F R H V) (reify-neutral T S F R H V))
  where

  record Reification
    (v : (c : Stage T) (m : Ma♯ T S c) → Map T S F R c m
      → Normal-Code T S F c m)
    : Set ℓ where
    field
      reifies-El0'p :
        (c : Stage T) (u : U0♯ T S c) (up : U0p T S R c u)
        (d : Stage T) (φ : Arrow T d c)
        → v c (El0'♯ T S c u) (El0'p T S F R c u up) d φ
          ＝ reify-base T S F R H V c u up d φ
      reifies-El+'p :
        (c : Stage T) (A : Ma♯ T S c)
        (Ap : (d : Stage T) (φ : Arrow T d c) → Map T S F R d (A ·⟨ T ⟩ φ))
        (B : Fam♯ T S c A)
        (Bp :
          (d : Stage T) (φ : Arrow T d c) (a : El♯ T S d (A ·⟨ T ⟩ φ))
          → Elp T S F R d (A ·⟨ T ⟩ φ) (Ap d φ) a
          → Map T S F R d (applied T S d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a))
        (C : U+♯ T S c A B)
        (Cp :
          U+p T S R c A (λ d φ → Elp T S F R d (A ·⟨ T ⟩ φ) (Ap d φ)) B
            (λ d φ a ap →
              Elp T S F R d (applied T S d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a)
                (Bp d φ a ap))
            C)
        (d : Stage T) (φ : Arrow T d c)
        → v c (El+'♯ T S c A B C) (El+'p T S F R c A Ap B Bp C Cp) d φ
          ＝ reify-plus T S F R H V c A Ap
               (λ d₁ φ₁ → v d₁ (A ·⟨ T ⟩ φ₁) (Ap d₁ φ₁)) B Bp
               (λ d₁ φ₁ a ap →
                 v d₁ (applied T S d₁ (A ·⟨ T ⟩ φ₁) (B ·⟨ T ⟩ φ₁) a)
                   (Bp d₁ φ₁ a ap))
               C Cp d φ
      reifies-nep :
        (c : Stage T) (m : Ma♯ T S c) (mn : Neutral-Code T S F c m)
        (d : Stage T) (φ : Arrow T d c)
        → v c m (nep T S F R c m mn) d φ
          ＝ reify-neutral T S F R H V c m mn d φ

  Agrees :
    (i : Index T S R) (mp : U (general (reducibility T S F R)) i)
    → Normal-Code T S F (pr₁ i) (pr₂ i) → Normal-Code T S F (pr₁ i) (pr₂ i)
    → Set ℓ
  Agrees i mp x y = (d : Stage T) (φ : Arrow T d (pr₁ i)) → x d φ ＝ y d φ

  family-respects :
    (c : Stage T) (A : Ma♯ T S c)
    (Ap : (d : Stage T) (φ : Arrow T d c) → Map T S F R d (A ·⟨ T ⟩ φ))
    (B : Fam♯ T S c A)
    (Bp :
      (d : Stage T) (φ : Arrow T d c) (a : El♯ T S d (A ·⟨ T ⟩ φ))
      → Elp T S F R d (A ·⟨ T ⟩ φ) (Ap d φ) a
      → Map T S F R d (applied T S d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a))
    (h k :
      (d : Stage T) (φ : Arrow T d c) (a : El♯ T S d (A ·⟨ T ⟩ φ))
      (ap : Elp T S F R d (A ·⟨ T ⟩ φ) (Ap d φ) a)
      → Normal-Code T S F d (applied T S d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a))
    → ( (d : Stage T) (φ : Arrow T d c) (a : El♯ T S d (A ·⟨ T ⟩ φ))
        (ap : Elp T S F R d (A ·⟨ T ⟩ φ) (Ap d φ) a)
        (d′ : Stage T) (φ′ : Arrow T d′ d)
        → h d φ a ap d′ φ′ ＝ k d φ a ap d′ φ′)
    → family-readback T S F R H V c A Ap B Bp h
      ＝ family-readback T S F R H V c A Ap B Bp k
  family-respects c A Ap B Bp h k r =
    ap (Extension.family-normal V c A B)
      (r (Extension.extend V c A) (Extension.weaken V c A)
        (Extension.fresh V c A)
        (fresh-reducible T S F R H V c A Ap)
        (Extension.extend V c A) (identity T))

  reify-plus-respects :
    (c : Stage T) (A : Ma♯ T S c)
    (Ap : (d : Stage T) (φ : Arrow T d c) → Map T S F R d (A ·⟨ T ⟩ φ))
    (h k : (d : Stage T) (φ : Arrow T d c) → Normal-Code T S F d (A ·⟨ T ⟩ φ))
    → ( (d : Stage T) (φ : Arrow T d c) (d′ : Stage T) (φ′ : Arrow T d′ d)
        → h d φ d′ φ′ ＝ k d φ d′ φ′)
    → (B : Fam♯ T S c A)
      (Bp :
        (d : Stage T) (φ : Arrow T d c) (a : El♯ T S d (A ·⟨ T ⟩ φ))
        → Elp T S F R d (A ·⟨ T ⟩ φ) (Ap d φ) a
        → Map T S F R d (applied T S d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a))
      (h′ k′ :
        (d : Stage T) (φ : Arrow T d c) (a : El♯ T S d (A ·⟨ T ⟩ φ))
        (ap : Elp T S F R d (A ·⟨ T ⟩ φ) (Ap d φ) a)
        → Normal-Code T S F d (applied T S d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a))
    → ( (d : Stage T) (φ : Arrow T d c) (a : El♯ T S d (A ·⟨ T ⟩ φ))
        (ap : Elp T S F R d (A ·⟨ T ⟩ φ) (Ap d φ) a)
        (d′ : Stage T) (φ′ : Arrow T d′ d)
        → h′ d φ a ap d′ φ′ ＝ k′ d φ a ap d′ φ′)
    → (C : U+♯ T S c A B)
      (Cp :
        U+p T S R c A (λ d φ → Elp T S F R d (A ·⟨ T ⟩ φ) (Ap d φ)) B
          (λ d φ a ap →
            Elp T S F R d (applied T S d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a)
              (Bp d φ a ap))
          C)
      (d : Stage T) (φ : Arrow T d c)
    → reify-plus T S F R H V c A Ap h B Bp h′ C Cp d φ
      ＝ reify-plus T S F R H V c A Ap k B Bp k′ C Cp d φ
  reify-plus-respects c A Ap h k r B Bp h′ k′ r′ C Cp d φ =
    ap₂ (plus-reified T S F R H V c A Ap B Bp C Cp d φ)
      (r d φ d (identity T))
      (family-respects d (A ·⟨ T ⟩ φ) (shift T Ap φ) (B ·⟨ T ⟩ φ)
        (shift T Bp φ) (shift T h′ φ) (shift T k′ φ)
        (λ d₁ φ₁ → r′ d₁ (φ ⊚⟨ T ⟩ φ₁)))

  reify-lax :
    (v : (c : Stage T) (m : Ma♯ T S c) → Map T S F R c m
      → Normal-Code T S F c m)
    → Reification v
    → Lax (universal (reducibility T S F R)) Reifying Reifying Agrees
        (λ i u → v (pr₁ i) (pr₂ i) u) reifying
  reify-lax v equations (lift ₀ , lift ₀ , c , u , up , w) k r =
    Reification.reifies-El0'p equations c u up
  reify-lax v equations
    (lift ₀ , lift ₁ , c , A , g , B , g′ , C , Cp , w)
    (k , k′ , h) (r , r′ , s) d φ =
    Reification.reifies-El+'p equations c A (λ d₁ φ₁ → g (d₁ , φ₁)) B
      (λ d₁ φ₁ a ap → g′ (d₁ , φ₁ , a , ap)) C Cp d φ
    ∙ reify-plus-respects c A (λ d₁ φ₁ → g (d₁ , φ₁))
        (λ d₁ φ₁ → v d₁ (A ·⟨ T ⟩ φ₁) (g (d₁ , φ₁)))
        (λ d₁ φ₁ → k (d₁ , φ₁)) (λ d₁ φ₁ → r (d₁ , φ₁)) B
        (λ d₁ φ₁ a ap → g′ (d₁ , φ₁ , a , ap))
        (λ d₁ φ₁ a ap →
          v d₁ (applied T S d₁ (A ·⟨ T ⟩ φ₁) (B ·⟨ T ⟩ φ₁) a)
            (g′ (d₁ , φ₁ , a , ap)))
        (λ d₁ φ₁ a ap → k′ (d₁ , φ₁ , a , ap))
        (λ d₁ φ₁ a ap → r′ (d₁ , φ₁ , a , ap)) C Cp d φ
  reify-lax v equations (lift ₁ , c , m , mn , w) k r =
    Reification.reifies-nep equations c m mn

  reify-code-unique :
    (v : (c : Stage T) (m : Ma♯ T S c) → Map T S F R c m
      → Normal-Code T S F c m)
    → Reification v
    → (c : Stage T) (m : Ma♯ T S c) (mp : Map T S F R c m)
      (d : Stage T) (φ : Arrow T d c)
    → v c m mp d φ ＝ reify-code T S F R H V c m mp d φ
  reify-code-unique v equations c m =
    ind-unique-rel (universal (reducibility T S F R))
      (universal-initiality (reducibility T S F R)) Reifying Reifying Agrees
      (λ i u → v (pr₁ i) (pr₂ i) u) reifying (reify-lax v equations) (c , m)

  reify-code-computes : Reification (reify-code T S F R H V)
  reify-code-computes = record
    { reifies-El0'p = λ c u up d φ → refl
    ; reifies-El+'p = λ c A Ap B Bp C Cp d φ → refl
    ; reifies-nep = λ c m mn d φ → refl
    }

------------------------------------------------------------------------
-- The joint readback, under extensionality

-- Its El+'p method builds the candidates of `readback-plus` from its
-- hypotheses as functions, and hands them to the fields of `Readback`, so
-- agreement of hypotheses gives equal values only under extensionality.

module _
  {ℓ : Level} (T : Stages ℓ) (S : Stage T → Syntax ℓ) (F : Forms T S)
  (R : Predicates T S) (H : Readback T S F R) (V : Extension T S F)
  where

  readback-unique-ext :
    ((A : Set ℓ) (Y : A → Set ℓ) → FunExt A Y)
    → (v : (c : Stage T) (m : Ma♯ T S c) (mp : Map T S F R c m)
         → Readable T S F R H V c m mp)
    → Computation T S F R (Readable T S F R H V)
        (readback-base T S F R H V) (readback-plus T S F R H V)
        (readback-neutral T S F R H V) v
    → (c : Stage T) (m : Ma♯ T S c) (mp : Map T S F R c m)
    → v c m mp ＝ readback T S F R H V c m mp
  readback-unique-ext extensionality v equations =
    MapElim-unique-ext T S F R (Readable T S F R H V)
      (readback-base T S F R H V) (readback-plus T S F R H V)
      (readback-neutral T S F R H V) extensionality v equations

  readback-computes :
    Computation T S F R (Readable T S F R H V)
      (readback-base T S F R H V) (readback-plus T S F R H V)
      (readback-neutral T S F R H V) (readback T S F R H V)
  readback-computes =
    MapElim-computes T S F R (Readable T S F R H V)
      (readback-base T S F R H V) (readback-plus T S F R H V)
      (readback-neutral T S F R H V)
