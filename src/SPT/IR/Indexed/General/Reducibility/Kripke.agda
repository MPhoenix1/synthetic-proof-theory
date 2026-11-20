{-# OPTIONS --safe --without-K #-}

module SPT.IR.Indexed.General.Reducibility.Kripke where

-- Kubánek's reducibility predicate for the external Mahlo universe
-- (Reducibility) over the stages of Foundation.Kripke, with restriction along
-- arrows. The syntax is given at every stage (`Syntax` at each stage) and
-- read at every edge into a stage (`Ma♯` and the other sorts, `applied`
-- for application). His predicates are given at one stage
-- (`Predicates`); the predicate stores them, and each of its own
-- premises, at every arrow into its stage (`U0p`, `El0p`, `U+p`, `El+p`).
-- The predicate is one general Dybjer–Setzer code over stages and codes
-- (`branch`, `reducibility`), with his two constructors at the indices
-- they compute (`Map`, `Elp`, `El0'p`, `El+'p`); its decoding clauses
-- hold by refl (`Elp-El0'p`, `Elp-El+'p`). Restriction along an arrow
-- (`restricted`) moves every stored family by precomposition, and on the
-- constructors it computes by refl (`restricted-El0'p`,
-- `restricted-El+'p`). Its identity and composition laws, and the
-- restriction of decoding witnesses, are in Kripke/Initiality. No law of
-- the stages or of the syntax is used. His eliminator, with hypotheses at
-- every arrow, computes by refl on both constructors (`MapElim`,
-- `MapElim-El0'p`, `MapElim-El+'p`).

open import SPT.Base

open import SPT.Foundation.Kripke using
  (Stages; Stage; Edge; Arrow; apply; compose; restrict; Box; shift)
open import SPT.IR.Description.Indexed using
  (ι; σ; δ; General; general)
open import SPT.IR.Indexed using (U; value)
open import SPT.IR.General using (intro; Method; ind)
open import SPT.IR.Indexed.General using (universal)
open import SPT.IR.Indexed.General.Reducibility using (Syntax)

open Syntax

------------------------------------------------------------------------
-- The syntax read at every edge into a stage

module _ {ℓ : Level} (T : Stages ℓ) (S : Stage T → Syntax ℓ) where

  Ma♯ : Stage T → Set ℓ
  Ma♯ c = (e : Stage T) → Edge T e c → Ma (S e)

  El♯ : (c : Stage T) → Ma♯ c → Set ℓ
  El♯ c A = (e : Stage T) (g : Edge T e c) → El (S e) (A e g)

  U0♯ : Stage T → Set ℓ
  U0♯ c = (e : Stage T) → Edge T e c → U0 (S e)

  El0'♯ : (c : Stage T) → U0♯ c → Ma♯ c
  El0'♯ c u = λ e g → El0' (S e) (u e g)

  Fam♯ : (c : Stage T) → Ma♯ c → Set ℓ
  Fam♯ c A = (e : Stage T) (g : Edge T e c) → Fam (S e) (A e g)

  applied : (c : Stage T) (A : Ma♯ c) → Fam♯ c A → El♯ c A → Ma♯ c
  applied c A B a = λ e g → _$$_ (S e) (B e g) (a e g)

  U+♯ : (c : Stage T) (A : Ma♯ c) → Fam♯ c A → Set ℓ
  U+♯ c A B = (e : Stage T) (g : Edge T e c) → U+ (S e) (A e g) (B e g)

  El+'♯ : (c : Stage T) (A : Ma♯ c) (B : Fam♯ c A) → U+♯ c A B → Ma♯ c
  El+'♯ c A B C = λ e g → El+' (S e) (A e g) (B e g) (C e g)

  -- Predicates on the elements of a code at every arrow into a stage, and
  -- on the values of a family over them.

  Kripke : (c : Stage T) → Ma♯ c → Set (lsuc ℓ)
  Kripke c A =
    (d : Stage T) (φ : Arrow T d c) → El♯ d (A ·⟨ T ⟩ φ) → Set ℓ

  Kripke-Family :
    (c : Stage T) (A : Ma♯ c) → Kripke c A → Fam♯ c A → Set (lsuc ℓ)
  Kripke-Family c A Ap B =
    (d : Stage T) (φ : Arrow T d c) (a : El♯ d (A ·⟨ T ⟩ φ)) → Ap d φ a
    → El♯ d (applied d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a) → Set ℓ

  -- Kubánek's predicates at one stage.

  record Predicates : Set (lsuc ℓ) where
    field
      U0p₀ : (d : Stage T) → U0♯ d → Set ℓ
      El0p₀ :
        (d : Stage T) (u : U0♯ d) → Box T d (λ d′ φ → U0p₀ d′ (u ·⟨ T ⟩ φ))
        → El♯ d (El0'♯ d u) → Set ℓ
      U+p₀ :
        (d : Stage T) (A : Ma♯ d) (Ap : Kripke d A) (B : Fam♯ d A)
        → Kripke-Family d A Ap B → U+♯ d A B → Set ℓ
      El+p₀ :
        (d : Stage T) (A : Ma♯ d) (Ap : Kripke d A) (B : Fam♯ d A)
        (Bp : Kripke-Family d A Ap B) (C : U+♯ d A B)
        → Box T d (λ d′ φ →
            U+p₀ d′ (A ·⟨ T ⟩ φ) (shift T Ap φ) (B ·⟨ T ⟩ φ)
              (shift T Bp φ) (C ·⟨ T ⟩ φ))
        → El♯ d (El+'♯ d A B C) → Set ℓ

------------------------------------------------------------------------
-- The predicate

  module _ (R : Predicates) where

    open Predicates R

    -- His predicates stored at every arrow.

    U0p : (c : Stage T) → U0♯ c → Set ℓ
    U0p c u = Box T c (λ d φ → U0p₀ d (u ·⟨ T ⟩ φ))

    El0p : (c : Stage T) (u : U0♯ c) → U0p c u → El♯ c (El0'♯ c u) → Set ℓ
    El0p c u up a =
      Box T c (λ d φ →
        El0p₀ d (u ·⟨ T ⟩ φ) (shift T up φ) (a ·⟨ T ⟩ φ))

    U+p :
      (c : Stage T) (A : Ma♯ c) (Ap : Kripke c A) (B : Fam♯ c A)
      → Kripke-Family c A Ap B → U+♯ c A B → Set ℓ
    U+p c A Ap B Bp C =
      Box T c (λ d φ →
        U+p₀ d (A ·⟨ T ⟩ φ) (shift T Ap φ) (B ·⟨ T ⟩ φ) (shift T Bp φ)
          (C ·⟨ T ⟩ φ))

    El+p :
      (c : Stage T) (A : Ma♯ c) (Ap : Kripke c A) (B : Fam♯ c A)
      (Bp : Kripke-Family c A Ap B) (C : U+♯ c A B)
      → U+p c A Ap B Bp C → El♯ c (El+'♯ c A B C) → Set ℓ
    El+p c A Ap B Bp C Cp a =
      Box T c (λ d φ →
        El+p₀ d (A ·⟨ T ⟩ φ) (shift T Ap φ) (B ·⟨ T ⟩ φ) (shift T Bp φ)
          (C ·⟨ T ⟩ φ) (shift T Cp φ) (a ·⟨ T ⟩ φ))

    -- Mathematical shape, with P and Q the decodings of the recursive
    -- inputs, each stored at every arrow φ into the stage c:
    --
    --   El0'p : σ c. σ u. σ (U0p c u). ι ((c , El0' u) , El0p c u up)
    --   El+'p : σ c. σ A. δ (Σ d. Arrow d c) (A · φ). σ B.
    --           δ (Σ d φ a. P (d , φ) a) (B · φ $$ a). σ C.
    --           σ (U+p c A P B Q C). ι ((c , El+' A B C) , El+p … Cp)

    Index : Set ℓ
    Index = Σ (Stage T) Ma♯

    Data : Index → Set (lsuc ℓ)
    Data i = El♯ (pr₁ i) (pr₂ i) → Set ℓ

    branch : 𝟚 → General ℓ (lsuc ℓ) Index Data
    branch ₀ =
      σ (Stage T) (λ c →
      σ (U0♯ c) (λ u →
      σ (U0p c u) (λ up →
      ι ((c , El0'♯ c u) , El0p c u up))))
    branch ₁ =
      σ (Stage T) (λ c →
      σ (Ma♯ c) (λ A →
      δ (Σ (Stage T) (λ d → Arrow T d c))
        (λ p → pr₁ p , (A ·⟨ T ⟩ pr₂ p)) (λ P →
      σ (Fam♯ c A) (λ B →
      δ (Σ (Stage T) (λ d → Σ (Arrow T d c) (λ φ →
          Σ (El♯ d (A ·⟨ T ⟩ φ)) (λ a → P (d , φ) a))))
        (λ q →
          pr₁ q ,
          applied (pr₁ q) (A ·⟨ T ⟩ pr₁ (pr₂ q)) (B ·⟨ T ⟩ pr₁ (pr₂ q))
            (pr₁ (pr₂ (pr₂ q))))
        (λ Q →
      σ (U+♯ c A B) (λ C →
      σ (U+p c A (λ d φ → P (d , φ)) B
          (λ d φ a ap → Q (d , φ , a , ap)) C) (λ Cp →
      ι ((c , El+'♯ c A B C) ,
        El+p c A (λ d φ → P (d , φ)) B (λ d φ a ap → Q (d , φ , a , ap))
          C Cp))))))))

    reducibility : General ℓ (lsuc ℓ) Index Data
    reducibility = σ (Lift ℓ 𝟚) (λ t → branch (lower t))

------------------------------------------------------------------------
-- Map, Elp and the constructors

    Map : (c : Stage T) → Ma♯ c → Set ℓ
    Map c m = U (general reducibility) (c , m)

    Elp : (c : Stage T) (m : Ma♯ c) → Map c m → El♯ c m → Set ℓ
    Elp c m = value (general reducibility) (c , m)

    El0'p : (c : Stage T) (u : U0♯ c) → U0p c u → Map c (El0'♯ c u)
    El0'p c u up = intro (universal reducibility) (lift ₀ , c , u , up , lift ⋆)

    El+'p :
      (c : Stage T) (A : Ma♯ c)
      (Ap : (d : Stage T) (φ : Arrow T d c) → Map d (A ·⟨ T ⟩ φ))
      (B : Fam♯ c A)
      (Bp :
        (d : Stage T) (φ : Arrow T d c) (a : El♯ d (A ·⟨ T ⟩ φ))
        → Elp d (A ·⟨ T ⟩ φ) (Ap d φ) a
        → Map d (applied d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a))
      (C : U+♯ c A B)
      → U+p c A (λ d φ → Elp d (A ·⟨ T ⟩ φ) (Ap d φ)) B
          (λ d φ a ap →
            Elp d (applied d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a) (Bp d φ a ap))
          C
      → Map c (El+'♯ c A B C)
    El+'p c A Ap B Bp C Cp =
      intro (universal reducibility)
        ( lift ₁ , c , A , (λ p → Ap (pr₁ p) (pr₂ p)) , B
        , (λ q →
            Bp (pr₁ q) (pr₁ (pr₂ q)) (pr₁ (pr₂ (pr₂ q)))
              (pr₂ (pr₂ (pr₂ q))))
        , C , Cp , lift ⋆)

    Elp-El0'p :
      (c : Stage T) (u : U0♯ c) (up : U0p c u)
      → Elp c (El0'♯ c u) (El0'p c u up) ＝ El0p c u up
    Elp-El0'p c u up = refl

    Elp-El+'p :
      (c : Stage T) (A : Ma♯ c)
      (Ap : (d : Stage T) (φ : Arrow T d c) → Map d (A ·⟨ T ⟩ φ))
      (B : Fam♯ c A)
      (Bp :
        (d : Stage T) (φ : Arrow T d c) (a : El♯ d (A ·⟨ T ⟩ φ))
        → Elp d (A ·⟨ T ⟩ φ) (Ap d φ) a
        → Map d (applied d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a))
      (C : U+♯ c A B)
      (Cp :
        U+p c A (λ d φ → Elp d (A ·⟨ T ⟩ φ) (Ap d φ)) B
          (λ d φ a ap →
            Elp d (applied d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a) (Bp d φ a ap))
          C)
      → Elp c (El+'♯ c A B C) (El+'p c A Ap B Bp C Cp)
        ＝ El+p c A (λ d φ → Elp d (A ·⟨ T ⟩ φ) (Ap d φ)) B
             (λ d φ a ap →
               Elp d (applied d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a) (Bp d φ a ap))
             C Cp
    Elp-El+'p c A Ap B Bp C Cp = refl

------------------------------------------------------------------------
-- Restriction along arrows

    Restricted : (i : Index) → U (general reducibility) i → Set ℓ
    Restricted i mp =
      (d : Stage T) (ψ : Arrow T d (pr₁ i)) → Map d (pr₂ i ·⟨ T ⟩ ψ)

    restricting : Method (universal reducibility) Restricted
    restricting (lift ₀ , c , u , up , w) h d ψ =
      El0'p d (u ·⟨ T ⟩ ψ) (shift T up ψ)
    restricting (lift ₁ , c , A , g , B , g′ , C , Cp , w) h d ψ =
      El+'p d (A ·⟨ T ⟩ ψ) (λ d′ φ → g (d′ , ψ ⊚⟨ T ⟩ φ)) (B ·⟨ T ⟩ ψ)
        (λ d′ φ a ap → g′ (d′ , ψ ⊚⟨ T ⟩ φ , a , ap)) (C ·⟨ T ⟩ ψ)
        (shift T Cp ψ)

    restricted :
      (c : Stage T) (m : Ma♯ c) → Map c m
      → (d : Stage T) (ψ : Arrow T d c) → Map d (m ·⟨ T ⟩ ψ)
    restricted c m = ind (universal reducibility) Restricted restricting (c , m)

    restricted-El0'p :
      (c : Stage T) (u : U0♯ c) (up : U0p c u)
      (d : Stage T) (ψ : Arrow T d c)
      → restricted c (El0'♯ c u) (El0'p c u up) d ψ
        ＝ El0'p d (u ·⟨ T ⟩ ψ) (shift T up ψ)
    restricted-El0'p c u up d ψ = refl

    restricted-El+'p :
      (c : Stage T) (A : Ma♯ c)
      (Ap : (d : Stage T) (φ : Arrow T d c) → Map d (A ·⟨ T ⟩ φ))
      (B : Fam♯ c A)
      (Bp :
        (d : Stage T) (φ : Arrow T d c) (a : El♯ d (A ·⟨ T ⟩ φ))
        → Elp d (A ·⟨ T ⟩ φ) (Ap d φ) a
        → Map d (applied d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a))
      (C : U+♯ c A B)
      (Cp :
        U+p c A (λ d φ → Elp d (A ·⟨ T ⟩ φ) (Ap d φ)) B
          (λ d φ a ap →
            Elp d (applied d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a) (Bp d φ a ap))
          C)
      (d : Stage T) (ψ : Arrow T d c)
      → restricted c (El+'♯ c A B C) (El+'p c A Ap B Bp C Cp) d ψ
        ＝ El+'p d (A ·⟨ T ⟩ ψ) (shift T Ap ψ) (B ·⟨ T ⟩ ψ) (shift T Bp ψ)
             (C ·⟨ T ⟩ ψ) (shift T Cp ψ)
    restricted-El+'p c A Ap B Bp C Cp d ψ = refl

------------------------------------------------------------------------
-- The eliminator

    module _
      {ν : Level} (F : (c : Stage T) (m : Ma♯ c) → Map c m → Set ν)
      (El0'm :
        (c : Stage T) (u : U0♯ c) (up : U0p c u)
        → F c (El0'♯ c u) (El0'p c u up))
      (El+'m :
        (c : Stage T) (A : Ma♯ c)
        (Ap : (d : Stage T) (φ : Arrow T d c) → Map d (A ·⟨ T ⟩ φ))
        → ((d : Stage T) (φ : Arrow T d c) → F d (A ·⟨ T ⟩ φ) (Ap d φ))
        → (B : Fam♯ c A)
          (Bp :
            (d : Stage T) (φ : Arrow T d c) (a : El♯ d (A ·⟨ T ⟩ φ))
            → Elp d (A ·⟨ T ⟩ φ) (Ap d φ) a
            → Map d (applied d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a))
        → ((d : Stage T) (φ : Arrow T d c) (a : El♯ d (A ·⟨ T ⟩ φ))
            (ap : Elp d (A ·⟨ T ⟩ φ) (Ap d φ) a)
            → F d (applied d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a) (Bp d φ a ap))
        → (C : U+♯ c A B)
          (Cp :
            U+p c A (λ d φ → Elp d (A ·⟨ T ⟩ φ) (Ap d φ)) B
              (λ d φ a ap →
                Elp d (applied d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a) (Bp d φ a ap))
              C)
        → F c (El+'♯ c A B C) (El+'p c A Ap B Bp C Cp))
      where

      Motive : (i : Index) → U (general reducibility) i → Set ν
      Motive i mp = F (pr₁ i) (pr₂ i) mp

      methods : Method (universal reducibility) Motive
      methods (lift ₀ , c , u , up , w) h = El0'm c u up
      methods (lift ₁ , c , A , g , B , g′ , C , Cp , w) (k , k′ , h) =
        El+'m c A (λ d φ → g (d , φ)) (λ d φ → k (d , φ)) B
          (λ d φ a ap → g′ (d , φ , a , ap))
          (λ d φ a ap → k′ (d , φ , a , ap)) C Cp

      MapElim : (c : Stage T) (m : Ma♯ c) (mp : Map c m) → F c m mp
      MapElim c m = ind (universal reducibility) Motive methods (c , m)

      MapElim-El0'p :
        (c : Stage T) (u : U0♯ c) (up : U0p c u)
        → MapElim c (El0'♯ c u) (El0'p c u up) ＝ El0'm c u up
      MapElim-El0'p c u up = refl

      MapElim-El+'p :
        (c : Stage T) (A : Ma♯ c)
        (Ap : (d : Stage T) (φ : Arrow T d c) → Map d (A ·⟨ T ⟩ φ))
        (B : Fam♯ c A)
        (Bp :
          (d : Stage T) (φ : Arrow T d c) (a : El♯ d (A ·⟨ T ⟩ φ))
          → Elp d (A ·⟨ T ⟩ φ) (Ap d φ) a
          → Map d (applied d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a))
        (C : U+♯ c A B)
        (Cp :
          U+p c A (λ d φ → Elp d (A ·⟨ T ⟩ φ) (Ap d φ)) B
            (λ d φ a ap →
              Elp d (applied d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a) (Bp d φ a ap))
            C)
        → MapElim c (El+'♯ c A B C) (El+'p c A Ap B Bp C Cp)
          ＝ El+'m c A Ap (λ d φ → MapElim d (A ·⟨ T ⟩ φ) (Ap d φ)) B Bp
               (λ d φ a ap →
                 MapElim d (applied d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a)
                   (Bp d φ a ap))
               C Cp
      MapElim-El+'p c A Ap B Bp C Cp = refl
