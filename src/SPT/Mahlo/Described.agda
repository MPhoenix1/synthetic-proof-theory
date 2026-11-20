{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Described where

-- A small Tarski universe V that reflects every operator it can describe,
-- inside itself and with code-level names. Descriptions (`Desc`), defined
-- together with V, are the identity, composition, a resident family,
-- products, sums and trees of an output, and selection over the points of a
-- code. Each has a reading as an operator on V's families (`operator`) and
-- one on families of types (`⟦_⟧`), and the two agree along the decoding
-- (`agreement`). The code `reflected d` decodes to the closure of ⟦ d ⟧
-- over the ambient family (Mahlo.Relative). Once V is complete, `embed`
-- maps that closure into V's own codes, its formers to V's formers and its
-- results and branches to the actual outputs of `operator d`, and
-- `coherence` relates the two decodings. So every described operator has a
-- reflection whose carrier is a code of V (`reflect`). The definition is
-- strictly positive because V reads its operators off codes, not off
-- functions on its families. The hypothesis is extensionality for functions
-- out of decoded types.

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
import SPT.Mahlo.Ambient as Ambient
open import SPT.Foundation.Tree.W using (W)
open import SPT.Mahlo.Decoding using (DecodingLaws)
import SPT.Mahlo.Relative as Relative
import SPT.Mahlo.Residence.Families as Families
open import SPT.Mahlo.Specification using
  (Family; Operator; Formers; Closure; Reflection)

------------------------------------------------------------------------
-- The universe and its descriptions

mutual
  data Desc : Set where
    identityᵈ : Desc
    composeᵈ : Desc → Desc → Desc
    residentᵈ : (a : V) → (Dec a → V) → Desc
    productᵈ sumᵈ treeᵈ : Desc → Desc
    selectᵈ : (a : V) → (Dec a → Desc) → Desc

  data V : Set where
    empty unit two natural : V
    pi sigma tree : (a : V) → (Dec a → V) → V
    identity : (a : V) → Dec a → Dec a → V
    reflected : Desc → V

  Dec : V → Set
  Dec empty = Lift lzero 𝟘
  Dec unit = Lift lzero 𝟙
  Dec two = Lift lzero 𝟚
  Dec natural = Lift lzero ℕ
  Dec (pi a b) = (x : Dec a) → Dec (b x)
  Dec (sigma a b) = Σ (Dec a) (λ x → Dec (b x))
  Dec (tree a b) = W (Dec a) (λ x → Dec (b x))
  Dec (identity a x y) = x ＝ y
  Dec (reflected d) = Relative.Generated (Ambient.formers lzero) ⟦ d ⟧

  -- The reading on families of types uses Dec only at codes inside d.
  ⟦_⟧ : Desc → Operator (λ (A : Set) → A)
  ⟦ identityᵈ ⟧ H = H
  ⟦ composeᵈ p q ⟧ H = ⟦ q ⟧ (⟦ p ⟧ H)
  ⟦ residentᵈ a b ⟧ H = Dec a , (λ x → Dec (b x))
  ⟦ productᵈ d ⟧ H =
    Lift lzero 𝟙 , (λ _ → (x : pr₁ (⟦ d ⟧ H)) → pr₂ (⟦ d ⟧ H) x)
  ⟦ sumᵈ d ⟧ H = Lift lzero 𝟙 , (λ _ → Σ (pr₁ (⟦ d ⟧ H)) (pr₂ (⟦ d ⟧ H)))
  ⟦ treeᵈ d ⟧ H = Lift lzero 𝟙 , (λ _ → W (pr₁ (⟦ d ⟧ H)) (pr₂ (⟦ d ⟧ H)))
  ⟦ selectᵈ a k ⟧ H =
    Σ (Dec a) (λ x → pr₁ (⟦ k x ⟧ H)) ,
    (λ p → pr₂ (⟦ k (pr₁ p) ⟧ H) (pr₂ p))

------------------------------------------------------------------------
-- Formers, and the reading on V's families

formers : Formers V Dec
formers = record
  { empty = empty
  ; unit = unit
  ; two = two
  ; natural = natural
  ; product = λ F → pi (pr₁ F) (pr₂ F)
  ; sum = λ F → sigma (pr₁ F) (pr₂ F)
  ; tree = λ F → tree (pr₁ F) (pr₂ F)
  ; identity = identity
  }

laws : DecodingLaws formers
laws = record
  { empty-β = refl
  ; unit-β = refl
  ; two-β = refl
  ; natural-β = refl
  ; product-β = λ a b → refl
  ; sum-β = λ a b → refl
  ; tree-β = λ a b → refl
  ; identity-β = λ a x y → refl
  }

-- An operator on families of V's codes.
operator : Desc → Operator Dec
operator identityᵈ G = G
operator (composeᵈ p q) G = operator q (operator p G)
operator (residentᵈ a b) G = a , b
operator (productᵈ d) G =
  unit , (λ _ → pi (pr₁ (operator d G)) (pr₂ (operator d G)))
operator (sumᵈ d) G =
  unit , (λ _ → sigma (pr₁ (operator d G)) (pr₂ (operator d G)))
operator (treeᵈ d) G =
  unit , (λ _ → tree (pr₁ (operator d G)) (pr₂ (operator d G)))
operator (selectᵈ a k) G =
  sigma a (λ x → pr₁ (operator (k x) G)) ,
  (λ p → pr₂ (operator (k (pr₁ p)) G) (pr₂ p))

-- The weakest extensionality used: functions out of one decoded type.
Extensionality : Set (lsuc (lsuc lzero))
Extensionality =
  (a : V) (B : Dec a → Set (lsuc lzero)) → FunExt (Dec a) B

------------------------------------------------------------------------
-- Type formers along a path of domains and pointwise paths of fibers

Π-path : {A B : Set} (p : A ＝ B) (F G : B → Set) →
  FunExt A (λ _ → Set) → ((y : B) → F y ＝ G y) →
  ((x : A) → F (transport (λ X → X) p x)) ＝ ((y : B) → G y)
Π-path {A} refl F G e q = ap (λ H → (x : A) → H x) (e F G q)

Σ-path : {A B : Set} (p : A ＝ B) (F G : B → Set) →
  FunExt A (λ _ → Set) → ((y : B) → F y ＝ G y) →
  Σ A (λ x → F (transport (λ X → X) p x)) ＝ Σ B G
Σ-path {A} refl F G e q = ap (Σ A) (e F G q)

W-path : {A B : Set} (p : A ＝ B) (F G : B → Set) →
  FunExt A (λ _ → Set) → ((y : B) → F y ＝ G y) →
  W A (λ x → F (transport (λ X → X) p x)) ＝ W B G
W-path {A} refl F G e q = ap (W A) (e F G q)

family-path : {A B : Set} (p : A ＝ B) (F G : B → Set) →
  FunExt A (λ _ → Set) → ((y : B) → F y ＝ G y) →
  _＝_ {A = Family (λ (X : Set) → X)}
    (A , (λ x → F (transport (λ X → X) p x))) (B , G)
family-path {A} refl F G e q = ap (A ,_) (e F G q)

identity-coherence : {A B : Set} (p : A ＝ B) (s t : B) →
  (transport (λ X → X) (p ⁻¹) s ＝ transport (λ X → X) (p ⁻¹) t)
    ＝ (s ＝ t)
identity-coherence refl s t = refl

fiber-coherence :
  {X Y : Family (λ (A : Set) → A)} (E : X ＝ Y) (y : pr₁ Y) →
  pr₂ X (transport (λ Z → Z) (ap pr₁ E ⁻¹) y) ＝ pr₂ Y y
fiber-coherence refl y = refl

------------------------------------------------------------------------
-- The two readings agree

module _ (ext : Extensionality) where

  types : (a : V) → FunExt (Dec a) (λ _ → Set)
  types a = ext a (λ _ → Set)

  codes : (a : V) → FunExt (Dec a) (λ _ → V)
  codes a f g q = ap (λ h x → lower (h x))
    (ext a (λ _ → Lift (lsuc lzero) V) (λ x → lift (f x))
      (λ x → lift (g x)) (λ x → ap lift (q x)))

  -- Both readings of a description agree along the decoding.
  agreement : (d : Desc) (G : Family Dec) →
    Families.image (λ (A : Set) → A) Dec (operator d G) ＝
      ⟦ d ⟧ (Families.image (λ (A : Set) → A) Dec G)
  agreement identityᵈ G = refl
  agreement (composeᵈ p q) G =
    agreement q (operator p G) ∙ ap ⟦ q ⟧ (agreement p G)
  agreement (residentᵈ a b) G = refl
  agreement (productᵈ d) G =
    ap (λ K → Lift lzero 𝟙 , (λ _ → (x : pr₁ K) → pr₂ K x)) (agreement d G)
  agreement (sumᵈ d) G =
    ap (λ K → Lift lzero 𝟙 , (λ _ → Σ (pr₁ K) (pr₂ K))) (agreement d G)
  agreement (treeᵈ d) G =
    ap (λ K → Lift lzero 𝟙 , (λ _ → W (pr₁ K) (pr₂ K))) (agreement d G)
  agreement (selectᵈ a k) G =
    ap
      ( λ K →
          Σ (Dec a) (λ x → pr₁ (K x)) ,
          (λ p → pr₂ (K (pr₁ p)) (pr₂ p)))
      ( ext a (λ _ → Family (λ (A : Set) → A))
          ( λ x → Families.image (λ (A : Set) → A) Dec (operator (k x) G))
          ( λ x → ⟦ k x ⟧ (Families.image (λ (A : Set) → A) Dec G))
          ( λ x → agreement (k x) G))

------------------------------------------------------------------------
-- Every described operator is reflected by a code of V

module _ (ext : Extensionality) (d : Desc) where

  mutual
    -- The closure of ⟦ d ⟧ maps into V's own codes.
    embed : Dec (reflected d) → V
    embed Relative.empty = empty
    embed Relative.unit = unit
    embed Relative.two = two
    embed Relative.natural = natural
    embed (Relative.product a b) =
      pi (embed a) (λ x → embed (b (transport (λ X → X) (coherence a) x)))
    embed (Relative.sum a b) =
      sigma (embed a)
        ( λ x → embed (b (transport (λ X → X) (coherence a) x)))
    embed (Relative.tree a b) =
      tree (embed a) (λ x → embed (b (transport (λ X → X) (coherence a) x)))
    embed (Relative.identity a s t) =
      identity (embed a) (transport (λ X → X) (coherence a ⁻¹) s)
        ( transport (λ X → X) (coherence a ⁻¹) t)
    embed (Relative.result a b) = pr₁ (operator d (input a b))
    embed (Relative.branch a b y) =
      pr₂ (operator d (input a b))
        ( transport (λ X → X) (ap pr₁ (agree a b) ⁻¹) y)

    input :
      (a : Dec (reflected d))
      → (Relative.interpret (Ambient.formers lzero) ⟦ d ⟧ a
         → Dec (reflected d))
      → Family Dec
    input a b =
      embed a , (λ x → embed (b (transport (λ X → X) (coherence a) x)))

    coherence :
      (a : Dec (reflected d))
      → Dec (embed a) ＝ Relative.interpret (Ambient.formers lzero) ⟦ d ⟧ a
    coherence Relative.empty = refl
    coherence Relative.unit = refl
    coherence Relative.two = refl
    coherence Relative.natural = refl
    coherence (Relative.product a b) =
      Π-path (coherence a) (λ y → Dec (embed (b y)))
        ( λ y → Relative.interpret (Ambient.formers lzero) ⟦ d ⟧ (b y))
        ( types ext (embed a)) (λ y → coherence (b y))
    coherence (Relative.sum a b) =
      Σ-path (coherence a) (λ y → Dec (embed (b y)))
        ( λ y → Relative.interpret (Ambient.formers lzero) ⟦ d ⟧ (b y))
        ( types ext (embed a)) (λ y → coherence (b y))
    coherence (Relative.tree a b) =
      W-path (coherence a) (λ y → Dec (embed (b y)))
        ( λ y → Relative.interpret (Ambient.formers lzero) ⟦ d ⟧ (b y))
        ( types ext (embed a)) (λ y → coherence (b y))
    coherence (Relative.identity a s t) =
      identity-coherence (coherence a) s t
    coherence (Relative.result a b) = ap pr₁ (agree a b)
    coherence (Relative.branch a b y) = fiber-coherence (agree a b) y

    agree :
      (a : Dec (reflected d))
      (b : Relative.interpret (Ambient.formers lzero) ⟦ d ⟧ a
           → Dec (reflected d))
      → Families.image (λ (A : Set) → A) Dec (operator d (input a b)) ＝
        ⟦ d ⟧
          ( Relative.interpret (Ambient.formers lzero) ⟦ d ⟧ a
          , (λ x → Relative.interpret (Ambient.formers lzero) ⟦ d ⟧ (b x)))
    agree a b =
      agreement ext d (input a b)
      ∙ ap ⟦ d ⟧
          ( family-path (coherence a)
              ( λ y → Dec (embed (b y)))
              ( λ y → Relative.interpret (Ambient.formers lzero) ⟦ d ⟧ (b y))
              ( types ext (embed a)) (λ y → coherence (b y)))

  -- A family over the child moves through the coherence of decodings.
  compress :
    (a : Dec (reflected d)) → (Dec (embed a) → Dec (reflected d))
    → Relative.interpret (Ambient.formers lzero) ⟦ d ⟧ a → Dec (reflected d)
  compress a b y = b (transport (λ X → X) (coherence a ⁻¹) y)

  recover :
    (a : Dec (reflected d)) (b : Dec (embed a) → Dec (reflected d))
    → (λ x → embed (compress a b (transport (λ X → X) (coherence a) x)))
      ＝ (λ x → embed (b x))
  recover a b =
    codes ext (embed a)
      ( λ x → embed (compress a b (transport (λ X → X) (coherence a) x)))
      ( λ x → embed (b x))
      ( λ x →
          ap (λ z → embed (b z))
            ( forth-and-back-transport (λ X → X) (coherence a) x))

  action :
    Family (λ a → Dec (embed a)) → Family (λ a → Dec (embed a))
  action (a , b) =
    let r = Relative.result a (compress a b)
    in r ,
       (λ x →
         Relative.branch a (compress a b)
           ( transport (λ X → X) (coherence r) x))

  action-β :
    (F : Family (λ a → Dec (embed a))) →
    (embed (pr₁ (action F)) , (λ x → embed (pr₂ (action F) x))) ＝
      operator d (embed (pr₁ F) , (λ x → embed (pr₂ F x)))
  action-β (a , b) =
    let G = operator d (input a (compress a b))
        R = ap pr₁ (agree a (compress a b))
    in ap (pr₁ G ,_)
         ( codes ext (pr₁ G)
             ( λ x →
                 pr₂ G
                   ( transport (λ X → X) (R ⁻¹) (transport (λ X → X) R x)))
             ( pr₂ G)
             ( λ x → ap (pr₂ G) (forth-and-back-transport (λ X → X) R x)))
       ∙ ap (λ k → operator d (embed a , k)) (recover a b)

  closure : Closure formers (operator d) (Dec (reflected d))
  closure = record
    { interpret = embed
    ; empty = Relative.empty , refl
    ; unit = Relative.unit , refl
    ; two = Relative.two , refl
    ; natural = Relative.natural , refl
    ; product = λ F →
        Relative.product (pr₁ F) (compress (pr₁ F) (pr₂ F))
        , ap (pi (embed (pr₁ F))) (recover (pr₁ F) (pr₂ F))
    ; sum = λ F →
        Relative.sum (pr₁ F) (compress (pr₁ F) (pr₂ F))
        , ap (sigma (embed (pr₁ F))) (recover (pr₁ F) (pr₂ F))
    ; tree = λ F →
        Relative.tree (pr₁ F) (compress (pr₁ F) (pr₂ F))
        , ap (tree (embed (pr₁ F))) (recover (pr₁ F) (pr₂ F))
    ; identity = λ a x y →
        Relative.identity a (transport (λ X → X) (coherence a) x)
          ( transport (λ X → X) (coherence a) y)
        , ap₂ (identity (embed a))
            ( forth-and-back-transport (λ X → X) (coherence a) x)
            ( forth-and-back-transport (λ X → X) (coherence a) y)
    ; inner = action
    ; inner-β = action-β
    }

  -- The reflection of operator d, with carrier a code of V itself.
  reflect : Reflection formers (operator d)
  reflect = record { carrier = reflected d ; closure = closure }
