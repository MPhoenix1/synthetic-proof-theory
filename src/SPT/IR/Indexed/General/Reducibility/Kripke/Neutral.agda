{-# OPTIONS --safe --without-K #-}

module SPT.IR.Indexed.General.Reducibility.Kripke.Neutral where

-- Kubánek's Kripke predicate (Reducibility/Kripke) with neutral codes, and
-- its readback, toward normalization.
--
-- Neutral and normal forms are predicates on the syntax at one stage
-- (`Forms`), asked along every arrow into a stage (`Neutral-Code`,
-- `Neutral-El`, `Normal-Code`, `Normal-El`). The predicate is the code of
-- Reducibility/Kripke with a second part: a code neutral along every
-- arrow is reducible, and it decodes to the elements neutral along every
-- arrow (`reducibility`, `Map`, `Elp`, `El0'p`, `El+'p`, `nep`, the three
-- decoding clauses by refl). Restriction with its identity and composition
-- laws, monotonicity and the eliminator are those of Reducibility/Kripke
-- with a clause for neutral codes, each refl or a shift; at neutral codes
-- restriction and the eliminator compute by refl (`restricted-nep`,
-- `MapElim-nep`).
--
-- A Kripke predicate on the elements of a code is a candidate when it
-- takes neutral elements and gives normal ones (`Candidate`,
-- `Candidate-Family`). Assume that Kubánek's two decodings are candidates
-- when the decodings of their recursive inputs are, that his codes are
-- normal from normal parts, and that neutral forms are normal
-- (`Readback`). Assume also the extension of a stage by a variable of a
-- code, neutral along every arrow, with a family normal when its value at
-- the variable is (`Extension`). Then:
-- - the decoding of every reducible code is a candidate (`readback`,
--   `reflect`, `reify`), by induction, the clause of El+' from the
--   readback of its recursive inputs (`candidate`, `candidate-family`);
-- - every reducible code is normal (`reify-code`), by the eliminator. At
--   El+' its family is read back at the variable of its recursive input,
--   reducible there by reflection at that input's decoding
--   (`family-readback`).
-- Reflection and both readbacks commute with restriction, by refl at
-- each constructor (`reflect-restricted`, `reify-restricted`,
-- `reify-code-restricted`).

open import SPT.Base

open import SPT.Foundation.Kripke using
  (Stages; Stage; Arrow; compose; identity; restrict; Box; shift)
open import SPT.IR.Description.Indexed using
  (ι; σ; General; general)
open import SPT.IR.Indexed using (U; value)
open import SPT.IR.General using (intro; Method; ind)
open import SPT.IR.Indexed.General using (universal)
open import SPT.IR.Indexed.General.Reducibility using (Syntax)
import SPT.IR.Indexed.General.Reducibility.Kripke as Canonical

module _ {ℓ : Level} (T : Stages ℓ) (S : Stage T → Syntax ℓ)
  (let Ma♯ = Canonical.Ma♯ T S)
  (let El♯ = Canonical.El♯ T S)
  (let U0♯ = Canonical.U0♯ T S)
  (let El0'♯ = Canonical.El0'♯ T S)
  (let Fam♯ = Canonical.Fam♯ T S)
  (let applied = Canonical.applied T S)
  (let U+♯ = Canonical.U+♯ T S)
  (let El+'♯ = Canonical.El+'♯ T S)
  (let Kripke = Canonical.Kripke T S)
  (let Kripke-Family = Canonical.Kripke-Family T S)
  where

  ----------------------------------------------------------------------
  -- Neutral and normal forms

  -- At one stage: neutral and normal codes, neutral and normal elements
  -- of a code, and normal families over a code.
  record Forms : Set (lsuc ℓ) where
    field
      Neutral-Code₀ : (d : Stage T) → Ma♯ d → Set ℓ
      Neutral₀ : (d : Stage T) (A : Ma♯ d) → El♯ d A → Set ℓ
      Normal-Code₀ : (d : Stage T) → Ma♯ d → Set ℓ
      Normal₀ : (d : Stage T) (A : Ma♯ d) → El♯ d A → Set ℓ
      Normal-Family₀ : (d : Stage T) (A : Ma♯ d) → Fam♯ d A → Set ℓ

  module _ (F : Forms) (let open Forms F) where

    -- Along every arrow into a stage.

    Neutral-Code Normal-Code : (c : Stage T) → Ma♯ c → Set ℓ
    Neutral-Code c m = Box T c (λ d φ → Neutral-Code₀ d (m ·⟨ T ⟩ φ))
    Normal-Code c m = Box T c (λ d φ → Normal-Code₀ d (m ·⟨ T ⟩ φ))

    Neutral-El Normal-El : (c : Stage T) (A : Ma♯ c) → El♯ c A → Set ℓ
    Neutral-El c A a =
      Box T c (λ d φ → Neutral₀ d (A ·⟨ T ⟩ φ) (a ·⟨ T ⟩ φ))
    Normal-El c A a = Box T c (λ d φ → Normal₀ d (A ·⟨ T ⟩ φ) (a ·⟨ T ⟩ φ))

    -- A Kripke predicate on the elements of a code that takes the
    -- elements neutral along every arrow and gives normal ones; and a
    -- family of such predicates over the elements it holds of.
    Candidate : (c : Stage T) (A : Ma♯ c) → Kripke c A → Set ℓ
    Candidate c A P =
      (d : Stage T) (φ : Arrow T d c) (a : El♯ d (A ·⟨ T ⟩ φ))
      → (Neutral-El d (A ·⟨ T ⟩ φ) a → P d φ a)
        × (P d φ a → Normal₀ d (A ·⟨ T ⟩ φ) a)

    Candidate-Family :
      (c : Stage T) (A : Ma♯ c) (P : Kripke c A) (B : Fam♯ c A)
      → Kripke-Family c A P B → Set ℓ
    Candidate-Family c A P B Q =
      (d : Stage T) (φ : Arrow T d c) (a : El♯ d (A ·⟨ T ⟩ φ))
      (ap : P d φ a) (b : El♯ d (applied d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a))
      → (Neutral-El d (applied d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a) b
         → Q d φ a ap b)
        × (Q d φ a ap b
           → Normal₀ d (applied d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a) b)

    -- The extension of a stage by a variable of a code: a stage with an
    -- arrow back and an element of the code there, neutral along every
    -- arrow. A family is normal when its value at the variable is.
    record Extension : Set ℓ where
      field
        extend : (d : Stage T) → Ma♯ d → Stage T
        weaken : (d : Stage T) (A : Ma♯ d) → Arrow T (extend d A) d
        fresh :
          (d : Stage T) (A : Ma♯ d) → El♯ (extend d A) (A ·⟨ T ⟩ weaken d A)
        fresh-neutral :
          (d : Stage T) (A : Ma♯ d)
          → Neutral-El (extend d A) (A ·⟨ T ⟩ weaken d A) (fresh d A)
        family-normal :
          (d : Stage T) (A : Ma♯ d) (B : Fam♯ d A)
          → Normal-Code₀ (extend d A)
              (applied (extend d A) (A ·⟨ T ⟩ weaken d A)
                (B ·⟨ T ⟩ weaken d A) (fresh d A))
          → Normal-Family₀ d A B

    module _ (R : Canonical.Predicates T S)
      (let U0p₀ = Canonical.Predicates.U0p₀ R)
      (let El0p₀ = Canonical.Predicates.El0p₀ R)
      (let U+p₀ = Canonical.Predicates.U+p₀ R)
      (let El+p₀ = Canonical.Predicates.El+p₀ R)
      (let U0p = Canonical.U0p T S R)
      (let El0p = Canonical.El0p T S R)
      (let U+p = Canonical.U+p T S R)
      (let El+p = Canonical.El+p T S R)
      (let Index = Canonical.Index T S R)
      (let Data = Canonical.Data T S R)
      where

      -- Kubánek's decodings are candidates when the decodings of their
      -- recursive inputs are, and his codes are normal from normal parts;
      -- neutral elements and neutral codes are normal.
      record Readback : Set (lsuc ℓ) where
        field
          base-reflect :
            (d : Stage T) (u : U0♯ d)
            (up : Box T d (λ d′ φ → U0p₀ d′ (u ·⟨ T ⟩ φ)))
            (a : El♯ d (El0'♯ d u))
            → Neutral-El d (El0'♯ d u) a → El0p₀ d u up a
          base-reify :
            (d : Stage T) (u : U0♯ d)
            (up : Box T d (λ d′ φ → U0p₀ d′ (u ·⟨ T ⟩ φ)))
            (a : El♯ d (El0'♯ d u))
            → El0p₀ d u up a → Normal₀ d (El0'♯ d u) a
          plus-reflect :
            (d : Stage T) (A : Ma♯ d) (Ap : Kripke d A) (B : Fam♯ d A)
            (Bp : Kripke-Family d A Ap B) (C : U+♯ d A B)
            (Cp :
              Box T d (λ d′ φ →
                U+p₀ d′ (A ·⟨ T ⟩ φ) (shift T Ap φ) (B ·⟨ T ⟩ φ)
                  (shift T Bp φ) (C ·⟨ T ⟩ φ)))
            (a : El♯ d (El+'♯ d A B C))
            → Candidate d A Ap → Candidate-Family d A Ap B Bp
            → Neutral-El d (El+'♯ d A B C) a → El+p₀ d A Ap B Bp C Cp a
          plus-reify :
            (d : Stage T) (A : Ma♯ d) (Ap : Kripke d A) (B : Fam♯ d A)
            (Bp : Kripke-Family d A Ap B) (C : U+♯ d A B)
            (Cp :
              Box T d (λ d′ φ →
                U+p₀ d′ (A ·⟨ T ⟩ φ) (shift T Ap φ) (B ·⟨ T ⟩ φ)
                  (shift T Bp φ) (C ·⟨ T ⟩ φ)))
            (a : El♯ d (El+'♯ d A B C))
            → Candidate d A Ap → Candidate-Family d A Ap B Bp
            → El+p₀ d A Ap B Bp C Cp a → Normal₀ d (El+'♯ d A B C) a
          neutral-normal :
            (d : Stage T) (A : Ma♯ d) (a : El♯ d A)
            → Neutral-El d A a → Normal₀ d A a
          neutral-code-normal :
            (d : Stage T) (m : Ma♯ d) → Neutral-Code d m → Normal-Code₀ d m
          base-normal :
            (d : Stage T) (u : U0♯ d)
            → Box T d (λ d′ φ → U0p₀ d′ (u ·⟨ T ⟩ φ))
            → Normal-Code₀ d (El0'♯ d u)
          plus-normal :
            (d : Stage T) (A : Ma♯ d) (Ap : Kripke d A) (B : Fam♯ d A)
            (Bp : Kripke-Family d A Ap B) (C : U+♯ d A B)
            → Normal-Code₀ d A → Normal-Family₀ d A B
            → U+p₀ d A Ap B Bp C → Normal-Code₀ d (El+'♯ d A B C)

------------------------------------------------------------------------
-- The predicate

      -- Mathematical shape: the code of Reducibility/Kripke, and
      --
      --   nep : σ c. σ m. σ (Neutral-Code c m). ι ((c , m) , Neutral-El c m)

      neutral : General ℓ (lsuc ℓ) Index Data
      neutral =
        σ (Stage T) (λ c →
        σ (Ma♯ c) (λ m →
        σ (Neutral-Code c m) (λ mn →
        ι ((c , m) , Neutral-El c m))))

      part : 𝟚 → General ℓ (lsuc ℓ) Index Data
      part ₀ = Canonical.reducibility T S R
      part ₁ = neutral

      reducibility : General ℓ (lsuc ℓ) Index Data
      reducibility = σ (Lift ℓ 𝟚) (λ t → part (lower t))

      Map : (c : Stage T) → Ma♯ c → Set ℓ
      Map c m = U (general reducibility) (c , m)

      Elp : (c : Stage T) (m : Ma♯ c) → Map c m → El♯ c m → Set ℓ
      Elp c m = value (general reducibility) (c , m)

      El0'p : (c : Stage T) (u : U0♯ c) → U0p c u → Map c (El0'♯ c u)
      El0'p c u up =
        intro (universal reducibility) (lift ₀ , lift ₀ , c , u , up , lift ⋆)

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
          ( lift ₀ , lift ₁ , c , A , (λ p → Ap (pr₁ p) (pr₂ p)) , B
          , (λ q →
              Bp (pr₁ q) (pr₁ (pr₂ q)) (pr₁ (pr₂ (pr₂ q)))
                (pr₂ (pr₂ (pr₂ q))))
          , C , Cp , lift ⋆)

      nep : (c : Stage T) (m : Ma♯ c) → Neutral-Code c m → Map c m
      nep c m mn = intro (universal reducibility) (lift ₁ , c , m , mn , lift ⋆)

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

      Elp-nep :
        (c : Stage T) (m : Ma♯ c) (mn : Neutral-Code c m)
        → Elp c m (nep c m mn) ＝ Neutral-El c m
      Elp-nep c m mn = refl

------------------------------------------------------------------------
-- Restriction along arrows

      Restricted : (i : Index) → U (general reducibility) i → Set ℓ
      Restricted i mp =
        (d : Stage T) (ψ : Arrow T d (pr₁ i)) → Map d (pr₂ i ·⟨ T ⟩ ψ)

      restricting : Method (universal reducibility) Restricted
      restricting (lift ₀ , lift ₀ , c , u , up , w) h d ψ =
        El0'p d (u ·⟨ T ⟩ ψ) (shift T up ψ)
      restricting (lift ₀ , lift ₁ , c , A , g , B , g′ , C , Cp , w) h d ψ =
        El+'p d (A ·⟨ T ⟩ ψ) (λ d′ φ → g (d′ , ψ ⊚⟨ T ⟩ φ)) (B ·⟨ T ⟩ ψ)
          (λ d′ φ a ap → g′ (d′ , ψ ⊚⟨ T ⟩ φ , a , ap)) (C ·⟨ T ⟩ ψ)
          (shift T Cp ψ)
      restricting (lift ₁ , c , m , mn , w) h d ψ =
        nep d (m ·⟨ T ⟩ ψ) (shift T mn ψ)

      restricted :
        (c : Stage T) (m : Ma♯ c) → Map c m
        → (d : Stage T) (ψ : Arrow T d c) → Map d (m ·⟨ T ⟩ ψ)
      restricted c m =
        ind (universal reducibility) Restricted restricting (c , m)

      restricted-nep :
        (c : Stage T) (m : Ma♯ c) (mn : Neutral-Code c m)
        (d : Stage T) (ψ : Arrow T d c)
        → restricted c m (nep c m mn) d ψ
          ＝ nep d (m ·⟨ T ⟩ ψ) (shift T mn ψ)
      restricted-nep c m mn d ψ = refl

      Identity : (i : Index) → U (general reducibility) i → Set ℓ
      Identity i mp = restricted (pr₁ i) (pr₂ i) mp (pr₁ i) (identity T) ＝ mp

      identity-law : Method (universal reducibility) Identity
      identity-law (lift ₀ , lift ₀ , c , u , up , w) h = refl
      identity-law (lift ₀ , lift ₁ , c , A , g , B , g′ , C , Cp , w) h =
        refl
      identity-law (lift ₁ , c , m , mn , w) h = refl

      restricted-identity :
        (c : Stage T) (m : Ma♯ c) (mp : Map c m)
        → restricted c m mp c (identity T) ＝ mp
      restricted-identity c m =
        ind (universal reducibility) Identity identity-law (c , m)

      Composition : (i : Index) → U (general reducibility) i → Set ℓ
      Composition i mp =
        (d : Stage T) (ψ : Arrow T d (pr₁ i)) (d′ : Stage T) (ψ′ : Arrow T d′ d)
        → restricted d (pr₂ i ·⟨ T ⟩ ψ)
            (restricted (pr₁ i) (pr₂ i) mp d ψ) d′ ψ′
          ＝ restricted (pr₁ i) (pr₂ i) mp d′ (ψ ⊚⟨ T ⟩ ψ′)

      composition-law : Method (universal reducibility) Composition
      composition-law (lift ₀ , lift ₀ , c , u , up , w) h d ψ d′ ψ′ = refl
      composition-law
        (lift ₀ , lift ₁ , c , A , g , B , g′ , C , Cp , w) h d ψ d′ ψ′ = refl
      composition-law (lift ₁ , c , m , mn , w) h d ψ d′ ψ′ = refl

      restricted-composition :
        (c : Stage T) (m : Ma♯ c) (mp : Map c m)
        (d : Stage T) (ψ : Arrow T d c) (d′ : Stage T) (ψ′ : Arrow T d′ d)
        → restricted d (m ·⟨ T ⟩ ψ) (restricted c m mp d ψ) d′ ψ′
          ＝ restricted c m mp d′ (ψ ⊚⟨ T ⟩ ψ′)
      restricted-composition c m =
        ind (universal reducibility) Composition composition-law (c , m)

      Monotone : (i : Index) → U (general reducibility) i → Set ℓ
      Monotone i mp =
        (d : Stage T) (ψ : Arrow T d (pr₁ i)) (a : El♯ (pr₁ i) (pr₂ i))
        → Elp (pr₁ i) (pr₂ i) mp a
        → Elp d (pr₂ i ·⟨ T ⟩ ψ) (restricted (pr₁ i) (pr₂ i) mp d ψ)
            (a ·⟨ T ⟩ ψ)

      monotonicity : Method (universal reducibility) Monotone
      monotonicity (lift ₀ , lift ₀ , c , u , up , w) h d ψ a ap =
        shift T ap ψ
      monotonicity (lift ₀ , lift ₁ , c , A , g , B , g′ , C , Cp , w) h d ψ a
        ap = shift T ap ψ
      monotonicity (lift ₁ , c , m , mn , w) h d ψ a ap = shift T ap ψ

      monotone :
        (c : Stage T) (m : Ma♯ c) (mp : Map c m)
        (d : Stage T) (ψ : Arrow T d c) (a : El♯ c m)
        → Elp c m mp a → Elp d (m ·⟨ T ⟩ ψ) (restricted c m mp d ψ) (a ·⟨ T ⟩ ψ)
      monotone c m = ind (universal reducibility) Monotone monotonicity (c , m)

------------------------------------------------------------------------
-- The eliminator

      module _
        {ν : Level} (M : (c : Stage T) (m : Ma♯ c) → Map c m → Set ν)
        (El0'm :
          (c : Stage T) (u : U0♯ c) (up : U0p c u)
          → M c (El0'♯ c u) (El0'p c u up))
        (El+'m :
          (c : Stage T) (A : Ma♯ c)
          (Ap : (d : Stage T) (φ : Arrow T d c) → Map d (A ·⟨ T ⟩ φ))
          → ((d : Stage T) (φ : Arrow T d c) → M d (A ·⟨ T ⟩ φ) (Ap d φ))
          → (B : Fam♯ c A)
            (Bp :
              (d : Stage T) (φ : Arrow T d c) (a : El♯ d (A ·⟨ T ⟩ φ))
              → Elp d (A ·⟨ T ⟩ φ) (Ap d φ) a
              → Map d (applied d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a))
          → ((d : Stage T) (φ : Arrow T d c) (a : El♯ d (A ·⟨ T ⟩ φ))
              (ap : Elp d (A ·⟨ T ⟩ φ) (Ap d φ) a)
              → M d (applied d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a) (Bp d φ a ap))
          → (C : U+♯ c A B)
            (Cp :
              U+p c A (λ d φ → Elp d (A ·⟨ T ⟩ φ) (Ap d φ)) B
                (λ d φ a ap →
                  Elp d (applied d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a)
                    (Bp d φ a ap))
                C)
          → M c (El+'♯ c A B C) (El+'p c A Ap B Bp C Cp))
        (nem :
          (c : Stage T) (m : Ma♯ c) (mn : Neutral-Code c m)
          → M c m (nep c m mn))
        where

        Motive : (i : Index) → U (general reducibility) i → Set ν
        Motive i mp = M (pr₁ i) (pr₂ i) mp

        methods : Method (universal reducibility) Motive
        methods (lift ₀ , lift ₀ , c , u , up , w) h = El0'm c u up
        methods (lift ₀ , lift ₁ , c , A , g , B , g′ , C , Cp , w)
          (k , k′ , h) =
          El+'m c A (λ d φ → g (d , φ)) (λ d φ → k (d , φ)) B
            (λ d φ a ap → g′ (d , φ , a , ap))
            (λ d φ a ap → k′ (d , φ , a , ap)) C Cp
        methods (lift ₁ , c , m , mn , w) h = nem c m mn

        MapElim : (c : Stage T) (m : Ma♯ c) (mp : Map c m) → M c m mp
        MapElim c m = ind (universal reducibility) Motive methods (c , m)

        MapElim-nep :
          (c : Stage T) (m : Ma♯ c) (mn : Neutral-Code c m)
          → MapElim c m (nep c m mn) ＝ nem c m mn
        MapElim-nep c m mn = refl

------------------------------------------------------------------------
-- Readback

      module _ (H : Readback) (V : Extension)
        (let open Readback H) (let open Extension V)
        where

        -- The decoding of a reducible code takes neutral elements and
        -- gives normal ones.
        Readable : (c : Stage T) (m : Ma♯ c) → Map c m → Set ℓ
        Readable c m mp =
          (a : El♯ c m)
          → (Neutral-El c m a → Elp c m mp a) × (Elp c m mp a → Normal-El c m a)

        -- The decodings of El+''s recursive inputs, read back along every
        -- arrow, are candidates.
        candidate :
          (c : Stage T) (A : Ma♯ c)
          (Ap : (d : Stage T) (φ : Arrow T d c) → Map d (A ·⟨ T ⟩ φ))
          → ((d : Stage T) (φ : Arrow T d c) → Readable d (A ·⟨ T ⟩ φ) (Ap d φ))
          → Candidate c A (λ d φ → Elp d (A ·⟨ T ⟩ φ) (Ap d φ))
        candidate c A Ap k d φ a =
          pr₁ (k d φ a) , (λ ap → pr₂ (k d φ a) ap d (identity T))

        candidate-family :
          (c : Stage T) (A : Ma♯ c)
          (Ap : (d : Stage T) (φ : Arrow T d c) → Map d (A ·⟨ T ⟩ φ))
          (B : Fam♯ c A)
          (Bp :
            (d : Stage T) (φ : Arrow T d c) (a : El♯ d (A ·⟨ T ⟩ φ))
            → Elp d (A ·⟨ T ⟩ φ) (Ap d φ) a
            → Map d (applied d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a))
          → ((d : Stage T) (φ : Arrow T d c) (a : El♯ d (A ·⟨ T ⟩ φ))
             (ap : Elp d (A ·⟨ T ⟩ φ) (Ap d φ) a)
             → Readable d (applied d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a)
                 (Bp d φ a ap))
          → Candidate-Family c A (λ d φ → Elp d (A ·⟨ T ⟩ φ) (Ap d φ)) B
              (λ d φ a ap →
                Elp d (applied d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a) (Bp d φ a ap))
        candidate-family c A Ap B Bp k′ d φ a ap b =
          pr₁ (k′ d φ a ap b) , (λ bp → pr₂ (k′ d φ a ap b) bp d (identity T))

        -- The methods of `readback` at the three kinds of code.
        readback-base :
          (c : Stage T) (u : U0♯ c) (up : U0p c u)
          → Readable c (El0'♯ c u) (El0'p c u up)
        readback-base c u up a =
          (λ n d φ →
             base-reflect d (u ·⟨ T ⟩ φ) (shift T up φ) (a ·⟨ T ⟩ φ)
               (shift T n φ))
          , (λ ap d φ →
               base-reify d (u ·⟨ T ⟩ φ) (shift T up φ) (a ·⟨ T ⟩ φ)
                 (ap d φ))

        readback-plus :
          (c : Stage T) (A : Ma♯ c)
          (Ap : (d : Stage T) (φ : Arrow T d c) → Map d (A ·⟨ T ⟩ φ))
          → ((d : Stage T) (φ : Arrow T d c) → Readable d (A ·⟨ T ⟩ φ) (Ap d φ))
          → (B : Fam♯ c A)
            (Bp :
              (d : Stage T) (φ : Arrow T d c) (a : El♯ d (A ·⟨ T ⟩ φ))
              → Elp d (A ·⟨ T ⟩ φ) (Ap d φ) a
              → Map d (applied d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a))
          → ((d : Stage T) (φ : Arrow T d c) (a : El♯ d (A ·⟨ T ⟩ φ))
              (ap : Elp d (A ·⟨ T ⟩ φ) (Ap d φ) a)
              → Readable d (applied d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a)
                  (Bp d φ a ap))
          → (C : U+♯ c A B)
            (Cp :
              U+p c A (λ d φ → Elp d (A ·⟨ T ⟩ φ) (Ap d φ)) B
                (λ d φ a ap →
                  Elp d (applied d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a)
                    (Bp d φ a ap))
                C)
          → Readable c (El+'♯ c A B C) (El+'p c A Ap B Bp C Cp)
        readback-plus c A Ap k B Bp k′ C Cp a =
          (λ n d φ →
             plus-reflect d (A ·⟨ T ⟩ φ)
               (shift T (λ d′ φ′ → Elp d′ (A ·⟨ T ⟩ φ′) (Ap d′ φ′)) φ)
               (B ·⟨ T ⟩ φ)
               (shift T
                 (λ d′ φ′ a′ ap →
                   Elp d′ (applied d′ (A ·⟨ T ⟩ φ′) (B ·⟨ T ⟩ φ′) a′)
                     (Bp d′ φ′ a′ ap))
                 φ)
               (C ·⟨ T ⟩ φ) (shift T Cp φ) (a ·⟨ T ⟩ φ)
               (candidate d (A ·⟨ T ⟩ φ) (shift T Ap φ) (shift T k φ))
               (candidate-family d (A ·⟨ T ⟩ φ) (shift T Ap φ)
                 (B ·⟨ T ⟩ φ) (shift T Bp φ) (shift T k′ φ))
               (shift T n φ))
          , (λ ap d φ →
               plus-reify d (A ·⟨ T ⟩ φ)
                 (shift T (λ d′ φ′ → Elp d′ (A ·⟨ T ⟩ φ′) (Ap d′ φ′)) φ)
                 (B ·⟨ T ⟩ φ)
                 (shift T
                   (λ d′ φ′ a′ ap′ →
                     Elp d′ (applied d′ (A ·⟨ T ⟩ φ′) (B ·⟨ T ⟩ φ′) a′)
                       (Bp d′ φ′ a′ ap′))
                   φ)
                 (C ·⟨ T ⟩ φ) (shift T Cp φ) (a ·⟨ T ⟩ φ)
                 (candidate d (A ·⟨ T ⟩ φ) (shift T Ap φ) (shift T k φ))
                 (candidate-family d (A ·⟨ T ⟩ φ) (shift T Ap φ)
                   (B ·⟨ T ⟩ φ) (shift T Bp φ) (shift T k′ φ))
                 (ap d φ))

        readback-neutral :
          (c : Stage T) (m : Ma♯ c) (mn : Neutral-Code c m)
          → Readable c m (nep c m mn)
        readback-neutral c m mn a =
          (λ n → n)
          , (λ ap d φ →
               neutral-normal d (m ·⟨ T ⟩ φ) (a ·⟨ T ⟩ φ) (shift T ap φ))

        readback : (c : Stage T) (m : Ma♯ c) (mp : Map c m) → Readable c m mp
        readback = MapElim Readable readback-base readback-plus readback-neutral

        reflect :
          (c : Stage T) (m : Ma♯ c) (mp : Map c m) (a : El♯ c m)
          → Neutral-El c m a → Elp c m mp a
        reflect c m mp a = pr₁ (readback c m mp a)

        reify :
          (c : Stage T) (m : Ma♯ c) (mp : Map c m) (a : El♯ c m)
          → Elp c m mp a → Normal-El c m a
        reify c m mp a = pr₂ (readback c m mp a)

        -- The variable of an extension is reducible at the decoding of a
        -- reducible code, by reflection.
        fresh-reducible :
          (c : Stage T) (A : Ma♯ c)
          (Ap : (d : Stage T) (φ : Arrow T d c) → Map d (A ·⟨ T ⟩ φ))
          → Elp (extend c A) (A ·⟨ T ⟩ weaken c A)
              (Ap (extend c A) (weaken c A)) (fresh c A)
        fresh-reducible c A Ap =
          reflect (extend c A) (A ·⟨ T ⟩ weaken c A)
            (Ap (extend c A) (weaken c A)) (fresh c A) (fresh-neutral c A)

        -- El+''s family read back at the variable of its recursive input.
        family-readback :
          (c : Stage T) (A : Ma♯ c)
          (Ap : (d : Stage T) (φ : Arrow T d c) → Map d (A ·⟨ T ⟩ φ))
          (B : Fam♯ c A)
          (Bp :
            (d : Stage T) (φ : Arrow T d c) (a : El♯ d (A ·⟨ T ⟩ φ))
            → Elp d (A ·⟨ T ⟩ φ) (Ap d φ) a
            → Map d (applied d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a))
          → ((d : Stage T) (φ : Arrow T d c) (a : El♯ d (A ·⟨ T ⟩ φ))
             (ap : Elp d (A ·⟨ T ⟩ φ) (Ap d φ) a)
             → Normal-Code d (applied d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a))
          → Normal-Family₀ c A B
        family-readback c A Ap B Bp k′ =
          family-normal c A B
            (k′ (extend c A) (weaken c A) (fresh c A)
              (fresh-reducible c A Ap)
              (extend c A) (identity T))

        -- The motive of `reify-code`, and its methods at the three kinds
        -- of code. An El+' code is normal from the normal forms of its
        -- recursive input and of its family (`plus-reified`).
        Reified : (c : Stage T) (m : Ma♯ c) → Map c m → Set ℓ
        Reified c m mp = Normal-Code c m

        plus-reified :
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
                Elp d (applied d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a)
                  (Bp d φ a ap))
              C)
          (d : Stage T) (φ : Arrow T d c)
          → Normal-Code₀ d (A ·⟨ T ⟩ φ)
          → Normal-Family₀ d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ)
          → Normal-Code₀ d (El+'♯ c A B C ·⟨ T ⟩ φ)
        plus-reified c A Ap B Bp C Cp d φ nA nB =
          plus-normal d (A ·⟨ T ⟩ φ)
            (shift T (λ d′ φ′ → Elp d′ (A ·⟨ T ⟩ φ′) (Ap d′ φ′)) φ)
            (B ·⟨ T ⟩ φ)
            (shift T
              (λ d′ φ′ a ap →
                Elp d′ (applied d′ (A ·⟨ T ⟩ φ′) (B ·⟨ T ⟩ φ′) a)
                  (Bp d′ φ′ a ap))
              φ)
            (C ·⟨ T ⟩ φ) nA nB (Cp d φ)

        reify-base :
          (c : Stage T) (u : U0♯ c) (up : U0p c u) → Normal-Code c (El0'♯ c u)
        reify-base c u up d φ = base-normal d (u ·⟨ T ⟩ φ) (shift T up φ)

        reify-plus :
          (c : Stage T) (A : Ma♯ c)
          (Ap : (d : Stage T) (φ : Arrow T d c) → Map d (A ·⟨ T ⟩ φ))
          → ((d : Stage T) (φ : Arrow T d c) → Normal-Code d (A ·⟨ T ⟩ φ))
          → (B : Fam♯ c A)
            (Bp :
              (d : Stage T) (φ : Arrow T d c) (a : El♯ d (A ·⟨ T ⟩ φ))
              → Elp d (A ·⟨ T ⟩ φ) (Ap d φ) a
              → Map d (applied d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a))
          → ((d : Stage T) (φ : Arrow T d c) (a : El♯ d (A ·⟨ T ⟩ φ))
              (ap : Elp d (A ·⟨ T ⟩ φ) (Ap d φ) a)
              → Normal-Code d (applied d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a))
          → (C : U+♯ c A B)
            (Cp :
              U+p c A (λ d φ → Elp d (A ·⟨ T ⟩ φ) (Ap d φ)) B
                (λ d φ a ap →
                  Elp d (applied d (A ·⟨ T ⟩ φ) (B ·⟨ T ⟩ φ) a)
                    (Bp d φ a ap))
                C)
          → Normal-Code c (El+'♯ c A B C)
        reify-plus c A Ap k B Bp k′ C Cp d φ =
          plus-reified c A Ap B Bp C Cp d φ (k d φ d (identity T))
            (family-readback d (A ·⟨ T ⟩ φ) (shift T Ap φ) (B ·⟨ T ⟩ φ)
              (shift T Bp φ) (shift T k′ φ))

        reify-neutral :
          (c : Stage T) (m : Ma♯ c) (mn : Neutral-Code c m) → Normal-Code c m
        reify-neutral c m mn d φ =
          neutral-code-normal d (m ·⟨ T ⟩ φ) (shift T mn φ)

        -- Every reducible code is normal.
        reify-code : (c : Stage T) (m : Ma♯ c) → Map c m → Normal-Code c m
        reify-code = MapElim Reified reify-base reify-plus reify-neutral

------------------------------------------------------------------------
-- Readback commutes with restriction

        reflect-restricted :
          (c : Stage T) (m : Ma♯ c) (mp : Map c m) (d : Stage T)
          (ψ : Arrow T d c) (a : El♯ c m) (n : Neutral-El c m a)
          → reflect d (m ·⟨ T ⟩ ψ) (restricted c m mp d ψ) (a ·⟨ T ⟩ ψ)
              (shift T n ψ)
            ＝ monotone c m mp d ψ a (reflect c m mp a n)
        reflect-restricted =
          MapElim
            (λ c m mp →
              (d : Stage T) (ψ : Arrow T d c) (a : El♯ c m)
              (n : Neutral-El c m a)
              → reflect d (m ·⟨ T ⟩ ψ) (restricted c m mp d ψ) (a ·⟨ T ⟩ ψ)
                  (shift T n ψ)
                ＝ monotone c m mp d ψ a (reflect c m mp a n))
            (λ c u up d ψ a n → refl)
            (λ c A Ap k B Bp k′ C Cp d ψ a n → refl)
            (λ c m mn d ψ a n → refl)

        reify-restricted :
          (c : Stage T) (m : Ma♯ c) (mp : Map c m) (d : Stage T)
          (ψ : Arrow T d c) (a : El♯ c m) (ap : Elp c m mp a)
          → reify d (m ·⟨ T ⟩ ψ) (restricted c m mp d ψ) (a ·⟨ T ⟩ ψ)
              (monotone c m mp d ψ a ap)
            ＝ shift T (reify c m mp a ap) ψ
        reify-restricted =
          MapElim
            (λ c m mp →
              (d : Stage T) (ψ : Arrow T d c) (a : El♯ c m)
              (ap : Elp c m mp a)
              → reify d (m ·⟨ T ⟩ ψ) (restricted c m mp d ψ) (a ·⟨ T ⟩ ψ)
                  (monotone c m mp d ψ a ap)
                ＝ shift T (reify c m mp a ap) ψ)
            (λ c u up d ψ a ap → refl)
            (λ c A Ap k B Bp k′ C Cp d ψ a ap → refl)
            (λ c m mn d ψ a ap → refl)

        reify-code-restricted :
          (c : Stage T) (m : Ma♯ c) (mp : Map c m) (d : Stage T)
          (ψ : Arrow T d c)
          → reify-code d (m ·⟨ T ⟩ ψ) (restricted c m mp d ψ)
            ＝ shift T (reify-code c m mp) ψ
        reify-code-restricted =
          MapElim
            (λ c m mp →
              (d : Stage T) (ψ : Arrow T d c)
              → reify-code d (m ·⟨ T ⟩ ψ) (restricted c m mp d ψ)
                ＝ shift T (reify-code c m mp) ψ)
            (λ c u up d ψ → refl)
            (λ c A Ap k B Bp k′ C Cp d ψ → refl)
            (λ c m mn d ψ → refl)
