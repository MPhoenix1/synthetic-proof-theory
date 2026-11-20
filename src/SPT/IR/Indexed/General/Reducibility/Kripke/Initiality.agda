{-# OPTIONS --safe --without-K #-}

module SPT.IR.Indexed.General.Reducibility.Kripke.Initiality where

-- Uniqueness for Kubánek's predicate over stages
-- (IR.Indexed.General.Reducibility.Kripke), from the initiality of
-- Dybjer–Setzer's rule. Restriction is the only valuation with its two
-- constructor equations, at every arrow, with no extensionality
-- (`restricted-unique`), and his three laws of restriction are relational
-- uniqueness at three relations (`restriction-identity`,
-- `restriction-composition`, `restriction-monotone`). The eliminator is
-- the only one with its two computation equations when its El+'p method
-- respects agreement, and for every method under extensionality
-- (`MapElim-unique`, `MapElim-unique-ext`). Both satisfy them by refl
-- (`restricted-restricts`, `MapElim-computes`).

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
  ; U+p; Elp; Index; reducibility; Map; El0'p; El+'p; Restricted
  ; restricting; restricted; restricted-El0'p; restricted-El+'p; Motive
  ; methods; MapElim; MapElim-El0'p; MapElim-El+'p)
open import SPT.Foundation.Kripke using
  (Stages; Stage; Arrow; compose; identity; restrict; shift)
open import SPT.IR.Description.Indexed using (general)

------------------------------------------------------------------------
-- Restriction is determined by its constructor equations

-- A valuation into restriction's motive is compared with restriction at
-- every arrow. Restriction's method does not read its hypotheses, so the
-- lax law at the pointwise relation is the two constructor equations.

module _
  {ℓ : Level} (T : Stages ℓ) (S : Stage T → Syntax ℓ) (R : Predicates T S)
  where

  record Restriction
    (ρ : (c : Stage T) (m : Ma♯ T S c) → Map T S R c m
      → (d : Stage T) (ψ : Arrow T d c) → Map T S R d (m ·⟨ T ⟩ ψ))
    : Set ℓ where
    field
      restricts-El0'p :
        (c : Stage T) (u : U0♯ T S c) (up : U0p T S R c u)
        (d : Stage T) (ψ : Arrow T d c)
        → ρ c (El0'♯ T S c u) (El0'p T S R c u up) d ψ
          ＝ El0'p T S R d (u ·⟨ T ⟩ ψ) (shift T up ψ)
      restricts-El+'p :
        (c : Stage T) (A : Ma♯ T S c)
        (Ap : (d : Stage T) (φ : Arrow T d c) → Map T S R d (A ·⟨ T ⟩ φ))
        (B : Fam♯ T S c A)
        (Bp :
          (d : Stage T) (φ : Arrow T d c) (a : El♯ T S d (A ·⟨ T ⟩ φ))
          → Elp T S R d (A ·⟨ T ⟩ φ) (Ap d φ) a
          → Map T S R d (applied T S d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a))
        (C : U+♯ T S c A B)
        (Cp :
          U+p T S R c A (λ d φ → Elp T S R d (A ·⟨ T ⟩ φ) (Ap d φ)) B
            (λ d φ a ap →
              Elp T S R d (applied T S d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a)
                (Bp d φ a ap))
            C)
        (d : Stage T) (ψ : Arrow T d c)
        → ρ c (El+'♯ T S c A B C) (El+'p T S R c A Ap B Bp C Cp) d ψ
          ＝ El+'p T S R d (A ·⟨ T ⟩ ψ) (shift T Ap ψ) (B ·⟨ T ⟩ ψ)
               (shift T Bp ψ) (C ·⟨ T ⟩ ψ) (shift T Cp ψ)

  Pointwise :
    (i : Index T S R) (mp : U (general (reducibility T S R)) i)
    → Restricted T S R i mp → Restricted T S R i mp → Set ℓ
  Pointwise i mp r r′ =
    (d : Stage T) (ψ : Arrow T d (pr₁ i)) → r d ψ ＝ r′ d ψ

  restriction-law :
    (ρ : (c : Stage T) (m : Ma♯ T S c) → Map T S R c m
      → (d : Stage T) (ψ : Arrow T d c) → Map T S R d (m ·⟨ T ⟩ ψ))
    → Restriction ρ
    → Lax (universal (reducibility T S R)) (Restricted T S R) (Restricted T S R)
        Pointwise (λ i u → ρ (pr₁ i) (pr₂ i) u) (restricting T S R)
  restriction-law ρ equations (lift ₀ , c , u , up , w) k r =
    Restriction.restricts-El0'p equations c u up
  restriction-law ρ equations (lift ₁ , c , A , g , B , g′ , C , Cp , w) k r =
    Restriction.restricts-El+'p equations c A (λ d φ → g (d , φ)) B
      (λ d φ a ap → g′ (d , φ , a , ap)) C Cp

  restricted-unique :
    (ρ : (c : Stage T) (m : Ma♯ T S c) → Map T S R c m
      → (d : Stage T) (ψ : Arrow T d c) → Map T S R d (m ·⟨ T ⟩ ψ))
    → Restriction ρ
    → (c : Stage T) (m : Ma♯ T S c) (mp : Map T S R c m)
      (d : Stage T) (ψ : Arrow T d c)
    → ρ c m mp d ψ ＝ restricted T S R c m mp d ψ
  restricted-unique ρ equations c m =
    ind-unique-rel (universal (reducibility T S R))
      (universal-initiality (reducibility T S R)) (Restricted T S R)
      (Restricted T S R) Pointwise (λ i u → ρ (pr₁ i) (pr₂ i) u)
      (restricting T S R) (restriction-law ρ equations) (c , m)

  restricted-restricts : Restriction (restricted T S R)
  restricted-restricts = record
    { restricts-El0'p = restricted-El0'p T S R
    ; restricts-El+'p = restricted-El+'p T S R
    }

------------------------------------------------------------------------
-- Kubánek's laws of restriction

-- Each law is relational uniqueness against restriction, at one relation:
-- restriction at the identity is the element (`Unchanged`), restricting
-- twice is restricting along the composite (`Composite`), and a decoding
-- witness moves along restriction (`Carried`). Restriction's method does
-- not read its hypotheses, so each lax law is refl or a shift at the two
-- constructors.

module _
  {ℓ : Level} (T : Stages ℓ) (S : Stage T → Syntax ℓ) (R : Predicates T S)
  where

  Elements : (i : Index T S R) → U (general (reducibility T S R)) i → Set ℓ
  Elements i mp = U (general (reducibility T S R)) i

  Unchanged :
    (i : Index T S R) (mp : U (general (reducibility T S R)) i)
    → Elements i mp → Restricted T S R i mp → Set ℓ
  Unchanged i mp x r = r (pr₁ i) (identity T) ＝ x

  identity-lax :
    Lax (universal (reducibility T S R)) Elements (Restricted T S R) Unchanged
      (λ i mp → mp) (restricting T S R)
  identity-lax (lift ₀ , c , u , up , w) k r = refl
  identity-lax (lift ₁ , c , A , g , B , g′ , C , Cp , w) k r = refl

  restriction-identity :
    (c : Stage T) (m : Ma♯ T S c) (mp : Map T S R c m)
    → restricted T S R c m mp c (identity T) ＝ mp
  restriction-identity c m =
    ind-unique-rel (universal (reducibility T S R))
      (universal-initiality (reducibility T S R)) Elements (Restricted T S R)
      Unchanged
      (λ i mp → mp) (restricting T S R) identity-lax (c , m)

  Composite :
    (i : Index T S R) (mp : U (general (reducibility T S R)) i)
    → Restricted T S R i mp → Restricted T S R i mp → Set ℓ
  Composite i mp r r′ =
    (d : Stage T) (ψ : Arrow T d (pr₁ i)) (d′ : Stage T) (ψ′ : Arrow T d′ d)
    → restricted T S R d (pr₂ i ·⟨ T ⟩ ψ) (r d ψ) d′ ψ′ ＝ r′ d′ (ψ ⊚⟨ T ⟩ ψ′)

  -- El+'p restricted twice, by refl. Stated on its curried arguments: the
  -- same refl at the tuple of `composition-lax`'s pattern does not finish.
  restricted-twice-El+'p :
    (c : Stage T) (A : Ma♯ T S c)
    (Ap : (d : Stage T) (φ : Arrow T d c) → Map T S R d (A ·⟨ T ⟩ φ))
    (B : Fam♯ T S c A)
    (Bp :
      (d : Stage T) (φ : Arrow T d c) (a : El♯ T S d (A ·⟨ T ⟩ φ))
      → Elp T S R d (A ·⟨ T ⟩ φ) (Ap d φ) a
      → Map T S R d (applied T S d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a))
    (C : U+♯ T S c A B)
    (Cp :
      U+p T S R c A (λ d φ → Elp T S R d (A ·⟨ T ⟩ φ) (Ap d φ)) B
        (λ d φ a ap →
          Elp T S R d (applied T S d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a)
            (Bp d φ a ap))
        C)
    (d : Stage T) (ψ : Arrow T d c) (d′ : Stage T) (ψ′ : Arrow T d′ d)
    → restricted T S R d (El+'♯ T S c A B C ·⟨ T ⟩ ψ)
        (restricted T S R c (El+'♯ T S c A B C)
          (El+'p T S R c A Ap B Bp C Cp) d ψ)
        d′ ψ′
      ＝ El+'p T S R d′ (A ·⟨ T ⟩ (ψ ⊚⟨ T ⟩ ψ′)) (shift T Ap (ψ ⊚⟨ T ⟩ ψ′))
           (B ·⟨ T ⟩ (ψ ⊚⟨ T ⟩ ψ′)) (shift T Bp (ψ ⊚⟨ T ⟩ ψ′))
           (C ·⟨ T ⟩ (ψ ⊚⟨ T ⟩ ψ′)) (shift T Cp (ψ ⊚⟨ T ⟩ ψ′))
  restricted-twice-El+'p c A Ap B Bp C Cp d ψ d′ ψ′ = refl

  composition-lax :
    Lax (universal (reducibility T S R)) (Restricted T S R) (Restricted T S R)
      Composite
      (λ i → restricted T S R (pr₁ i) (pr₂ i)) (restricting T S R)
  composition-lax (lift ₀ , c , u , up , w) k r d ψ d′ ψ′ = refl
  composition-lax (lift ₁ , c , A , g , B , g′ , C , Cp , w) k r d ψ d′ ψ′ =
    restricted-twice-El+'p c A (λ d₁ φ → g (d₁ , φ)) B
      (λ d₁ φ a ap → g′ (d₁ , φ , a , ap)) C Cp d ψ d′ ψ′

  restriction-composition :
    (c : Stage T) (m : Ma♯ T S c) (mp : Map T S R c m)
    (d : Stage T) (ψ : Arrow T d c) (d′ : Stage T) (ψ′ : Arrow T d′ d)
    → restricted T S R d (m ·⟨ T ⟩ ψ) (restricted T S R c m mp d ψ) d′ ψ′
      ＝ restricted T S R c m mp d′ (ψ ⊚⟨ T ⟩ ψ′)
  restriction-composition c m =
    ind-unique-rel (universal (reducibility T S R))
      (universal-initiality (reducibility T S R)) (Restricted T S R)
      (Restricted T S R) Composite
      (λ i → restricted T S R (pr₁ i) (pr₂ i)) (restricting T S R)
      composition-lax (c , m)

  Carried :
    (i : Index T S R) (mp : U (general (reducibility T S R)) i)
    → Restricted T S R i mp → Restricted T S R i mp → Set ℓ
  Carried i mp r r′ =
    (d : Stage T) (ψ : Arrow T d (pr₁ i)) (a : El♯ T S (pr₁ i) (pr₂ i))
    → Elp T S R (pr₁ i) (pr₂ i) mp a
    → Elp T S R d (pr₂ i ·⟨ T ⟩ ψ) (r d ψ) (a ·⟨ T ⟩ ψ)

  monotone-lax :
    Lax (universal (reducibility T S R)) (Restricted T S R) (Restricted T S R)
      Carried
      (λ i → restricted T S R (pr₁ i) (pr₂ i)) (restricting T S R)
  monotone-lax (lift ₀ , c , u , up , w) k r d ψ a ap = shift T ap ψ
  monotone-lax (lift ₁ , c , A , g , B , g′ , C , Cp , w) k r d ψ a ap =
    shift T ap ψ

  restriction-monotone :
    (c : Stage T) (m : Ma♯ T S c) (mp : Map T S R c m)
    (d : Stage T) (ψ : Arrow T d c) (a : El♯ T S c m)
    → Elp T S R c m mp a
    → Elp T S R d (m ·⟨ T ⟩ ψ) (restricted T S R c m mp d ψ) (a ·⟨ T ⟩ ψ)
  restriction-monotone c m =
    ind-unique-rel (universal (reducibility T S R))
      (universal-initiality (reducibility T S R)) (Restricted T S R)
      (Restricted T S R) Carried
      (λ i → restricted T S R (pr₁ i) (pr₂ i)) (restricting T S R)
      monotone-lax (c , m)

------------------------------------------------------------------------
-- The eliminator is determined by its computation equations

-- The method for El+'p respects agreement when hypotheses agreeing at
-- every arrow give the same value. With it, and with the two computation
-- equations, a valuation is the eliminator; under extensionality for
-- families over the arities every method respects agreement.

module _
  {ℓ ν : Level} (T : Stages ℓ) (S : Stage T → Syntax ℓ) (R : Predicates T S)
  (F : (c : Stage T) (m : Ma♯ T S c) → Map T S R c m → Set ν)
  (El+'m :
    (c : Stage T) (A : Ma♯ T S c)
    (Ap : (d : Stage T) (φ : Arrow T d c) → Map T S R d (A ·⟨ T ⟩ φ))
    → ((d : Stage T) (φ : Arrow T d c) → F d (A ·⟨ T ⟩ φ) (Ap d φ))
    → (B : Fam♯ T S c A)
      (Bp :
        (d : Stage T) (φ : Arrow T d c) (a : El♯ T S d (A ·⟨ T ⟩ φ))
        → Elp T S R d (A ·⟨ T ⟩ φ) (Ap d φ) a
        → Map T S R d (applied T S d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a))
    → ( (d : Stage T) (φ : Arrow T d c) (a : El♯ T S d (A ·⟨ T ⟩ φ))
        (ap : Elp T S R d (A ·⟨ T ⟩ φ) (Ap d φ) a)
        → F d (applied T S d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a) (Bp d φ a ap))
    → (C : U+♯ T S c A B)
      (Cp :
        U+p T S R c A (λ d φ → Elp T S R d (A ·⟨ T ⟩ φ) (Ap d φ)) B
          (λ d φ a ap →
            Elp T S R d (applied T S d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a)
              (Bp d φ a ap))
          C)
    → F c (El+'♯ T S c A B C) (El+'p T S R c A Ap B Bp C Cp))
  where

  Respects : Set (ℓ ⊔ ν)
  Respects =
    (c : Stage T) (A : Ma♯ T S c)
    (Ap : (d : Stage T) (φ : Arrow T d c) → Map T S R d (A ·⟨ T ⟩ φ))
    (h h′ : (d : Stage T) (φ : Arrow T d c) → F d (A ·⟨ T ⟩ φ) (Ap d φ))
    → ((d : Stage T) (φ : Arrow T d c) → h d φ ＝ h′ d φ)
    → (B : Fam♯ T S c A)
      (Bp :
        (d : Stage T) (φ : Arrow T d c) (a : El♯ T S d (A ·⟨ T ⟩ φ))
        → Elp T S R d (A ·⟨ T ⟩ φ) (Ap d φ) a
        → Map T S R d (applied T S d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a))
      (k k′ :
        (d : Stage T) (φ : Arrow T d c) (a : El♯ T S d (A ·⟨ T ⟩ φ))
        (ap : Elp T S R d (A ·⟨ T ⟩ φ) (Ap d φ) a)
        → F d (applied T S d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a) (Bp d φ a ap))
    → ( (d : Stage T) (φ : Arrow T d c) (a : El♯ T S d (A ·⟨ T ⟩ φ))
        (ap : Elp T S R d (A ·⟨ T ⟩ φ) (Ap d φ) a)
        → k d φ a ap ＝ k′ d φ a ap)
    → (C : U+♯ T S c A B)
      (Cp :
        U+p T S R c A (λ d φ → Elp T S R d (A ·⟨ T ⟩ φ) (Ap d φ)) B
          (λ d φ a ap →
            Elp T S R d (applied T S d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a)
              (Bp d φ a ap))
          C)
    → El+'m c A Ap h B Bp k C Cp ＝ El+'m c A Ap h′ B Bp k′ C Cp

module _
  {ℓ ν : Level} (T : Stages ℓ) (S : Stage T → Syntax ℓ) (R : Predicates T S)
  (F : (c : Stage T) (m : Ma♯ T S c) → Map T S R c m → Set ν)
  (El0'm :
    (c : Stage T) (u : U0♯ T S c) (up : U0p T S R c u)
    → F c (El0'♯ T S c u) (El0'p T S R c u up))
  (El+'m :
    (c : Stage T) (A : Ma♯ T S c)
    (Ap : (d : Stage T) (φ : Arrow T d c) → Map T S R d (A ·⟨ T ⟩ φ))
    → ((d : Stage T) (φ : Arrow T d c) → F d (A ·⟨ T ⟩ φ) (Ap d φ))
    → (B : Fam♯ T S c A)
      (Bp :
        (d : Stage T) (φ : Arrow T d c) (a : El♯ T S d (A ·⟨ T ⟩ φ))
        → Elp T S R d (A ·⟨ T ⟩ φ) (Ap d φ) a
        → Map T S R d (applied T S d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a))
    → ( (d : Stage T) (φ : Arrow T d c) (a : El♯ T S d (A ·⟨ T ⟩ φ))
        (ap : Elp T S R d (A ·⟨ T ⟩ φ) (Ap d φ) a)
        → F d (applied T S d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a) (Bp d φ a ap))
    → (C : U+♯ T S c A B)
      (Cp :
        U+p T S R c A (λ d φ → Elp T S R d (A ·⟨ T ⟩ φ) (Ap d φ)) B
          (λ d φ a ap →
            Elp T S R d (applied T S d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a)
              (Bp d φ a ap))
          C)
    → F c (El+'♯ T S c A B C) (El+'p T S R c A Ap B Bp C Cp))
  where

  record Computation
    (v : (c : Stage T) (m : Ma♯ T S c) (mp : Map T S R c m) → F c m mp)
    : Set (ℓ ⊔ ν) where
    field
      computes-El0'p :
        (c : Stage T) (u : U0♯ T S c) (up : U0p T S R c u)
        → v c (El0'♯ T S c u) (El0'p T S R c u up) ＝ El0'm c u up
      computes-El+'p :
        (c : Stage T) (A : Ma♯ T S c)
        (Ap : (d : Stage T) (φ : Arrow T d c) → Map T S R d (A ·⟨ T ⟩ φ))
        (B : Fam♯ T S c A)
        (Bp :
          (d : Stage T) (φ : Arrow T d c) (a : El♯ T S d (A ·⟨ T ⟩ φ))
          → Elp T S R d (A ·⟨ T ⟩ φ) (Ap d φ) a
          → Map T S R d (applied T S d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a))
        (C : U+♯ T S c A B)
        (Cp :
          U+p T S R c A (λ d φ → Elp T S R d (A ·⟨ T ⟩ φ) (Ap d φ)) B
            (λ d φ a ap →
              Elp T S R d (applied T S d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a)
                (Bp d φ a ap))
            C)
        → v c (El+'♯ T S c A B C) (El+'p T S R c A Ap B Bp C Cp)
          ＝ El+'m c A Ap (λ d φ → v d (A ·⟨ T ⟩ φ) (Ap d φ)) B Bp
               (λ d φ a ap →
                 v d (applied T S d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a)
                   (Bp d φ a ap))
               C Cp

  homomorphic :
    (v : (c : Stage T) (m : Ma♯ T S c) (mp : Map T S R c m) → F c m mp)
    → Computation v
    → Homomorphic (universal (reducibility T S R)) (Motive T S R F El0'm El+'m)
        (λ i u → v (pr₁ i) (pr₂ i) u) (methods T S R F El0'm El+'m)
  homomorphic v equations (lift ₀ , c , u , up , w) =
    Computation.computes-El0'p equations c u up
  homomorphic v equations (lift ₁ , c , A , g , B , g′ , C , Cp , w) =
    Computation.computes-El+'p equations c A (λ d φ → g (d , φ)) B
      (λ d φ a ap → g′ (d , φ , a , ap)) C Cp

  congruence :
    Respects T S R F El+'m
    → Congruent (universal (reducibility T S R)) (Motive T S R F El0'm El+'m)
        (methods T S R F El0'm El+'m)
  congruence respects (lift ₀ , c , u , up , w) h k r = refl
  congruence respects
    (lift ₁ , c , A , g , B , g′ , C , Cp , w)
    (h , h′ , h″) (k , k′ , k″) (r , r′ , r″) =
    respects c A (λ d φ → g (d , φ))
      (λ d φ → h (d , φ)) (λ d φ → k (d , φ)) (λ d φ → r (d , φ)) B
      (λ d φ a ap → g′ (d , φ , a , ap))
      (λ d φ a ap → h′ (d , φ , a , ap))
      (λ d φ a ap → k′ (d , φ , a , ap))
      (λ d φ a ap → r′ (d , φ , a , ap)) C Cp

  MapElim-unique :
    (v : (c : Stage T) (m : Ma♯ T S c) (mp : Map T S R c m) → F c m mp)
    → Respects T S R F El+'m → Computation v
    → (c : Stage T) (m : Ma♯ T S c) (mp : Map T S R c m)
    → v c m mp ＝ MapElim T S R F El0'm El+'m c m mp
  MapElim-unique v respects equations c m =
    ind-unique (universal (reducibility T S R))
      (universal-initiality (reducibility T S R)) (Motive T S R F El0'm El+'m)
      (λ i u → v (pr₁ i) (pr₂ i) u) (methods T S R F El0'm El+'m)
      (congruence respects) (homomorphic v equations) (c , m)

  MapElim-unique-ext :
    ((A : Set ℓ) (Y : A → Set ν) → FunExt A Y)
    → (v : (c : Stage T) (m : Ma♯ T S c) (mp : Map T S R c m) → F c m mp)
    → Computation v
    → (c : Stage T) (m : Ma♯ T S c) (mp : Map T S R c m)
    → v c m mp ＝ MapElim T S R F El0'm El+'m c m mp
  MapElim-unique-ext extensionality v equations c m =
    ind-unique (universal (reducibility T S R))
      (universal-initiality (reducibility T S R)) (Motive T S R F El0'm El+'m)
      (λ i u → v (pr₁ i) (pr₂ i) u) (methods T S R F El0'm El+'m)
      ( congruent extensionality (universal (reducibility T S R))
          (Motive T S R F El0'm El+'m) (methods T S R F El0'm El+'m))
      (homomorphic v equations) (c , m)

  MapElim-computes : Computation (MapElim T S R F El0'm El+'m)
  MapElim-computes = record
    { computes-El0'p = MapElim-El0'p T S R F El0'm El+'m
    ; computes-El+'p = MapElim-El+'p T S R F El0'm El+'m
    }
