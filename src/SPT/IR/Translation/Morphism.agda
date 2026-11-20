{-# OPTIONS --safe --without-K #-}

module SPT.IR.Translation.Morphism where

-- Morphisms of algebras along a translation τ over φ: each code of M goes
-- to a code of N with an identification of its decoding with the image of
-- M's under φ, and the image of an operation is N's operation at the
-- translated shape (`Fibers`, `step`, `Along`). The identity is a morphism
-- along the identity translation (`identity-along`); morphisms compose
-- along the composite translation (`compose-along`, through Translation's
-- `act-up`). Along the identity translation these are the morphisms of
-- Morphism (`along-morphism`, `morphism-along`).

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Fibers using (fiber)
open import SPT.Foundation.Induction.Initiality using (Section)

open import SPT.IR.Action using (assemble)
open import SPT.IR.Algebra using (Algebra; Law)
open import SPT.IR.Description using
  (Desc; Indexed; carrier; index; indexed; Shape; Mark)
open import SPT.IR.Layers using
  ( skeleton; read; collect; collect-natural; Marked; normal; up; down
  ; canonical; assembled; up-down)
import SPT.IR.Morphism as Morphism
open import SPT.IR.Restriction using (Position; input)
open import SPT.IR.Translation using
  ( Translation; identity; compose; translate; act; extend; pushed
  ; act-marked; act-up)

------------------------------------------------------------------------
-- Identifications

-- Transport in a family of fibers along g post-composes the identification
-- with the image of the path (`moved`). The others are the cancellations
-- the composite needs, each by path induction.

moved :
  {ℓ κ μ : Level} {A : Set ℓ} {B : Set κ} {C : Set μ} (f : B → C)
  (g : A → C) {a b : A} (p : a ＝ b) (x : fiber f (g a))
  → transport (λ y → fiber f (g y)) p x ＝ (pr₁ x , (pr₂ x ∙ ap g p))
moved f g refl x = ap (λ w → pr₁ x , w) (refl-right-neutral (pr₂ x) ⁻¹)

cancel :
  {ℓ : Level} {A : Set ℓ} {x y : A} (p : x ＝ y)
  → refl ＝ p ∙ ap (λ e → e) (p ⁻¹)
cancel refl = refl

reshape :
  {ℓ κ μ : Level} {A : Set ℓ} {B : Set κ} {C : Set μ}
  (φ : A → B) (φ′ : B → C) {x y : C} {m n : B} {e e₂ : A}
  (L : x ＝ y) (A′ : y ＝ φ′ m) (N : n ＝ m) (R : m ＝ φ e) (S : e ＝ e₂)
  → (L ∙ (A′ ∙ ap φ′ (N ⁻¹))) ∙ ap φ′ (N ∙ (R ∙ ap φ S))
    ＝ L ∙ ((A′ ∙ ap φ′ R) ∙ ap (λ a → φ′ (φ a)) S)
reshape φ φ′ refl refl refl refl refl = refl

marks :
  {ℓ κ μ : Level} {A : Set ℓ} {B : Set κ} {C : Set μ}
  (φ : A → B) (φ′ : B → C) {x : C} {b : B} {e f : A}
  (O′ : x ＝ φ′ b) (O : b ＝ φ e) (r : e ＝ f)
  → O′ ∙ ap φ′ (O ∙ ap φ r)
    ＝ (O′ ∙ ap φ′ O) ∙ ap (λ a → φ′ (φ a)) r
marks φ φ′ refl refl refl = refl

module _
  {κ κ′ j j′ : Level} {E : Set j} {E′ : Set j′} (φ : E → E′)
  (Y : Indexed κ E) (X : Indexed κ′ E′)
  (u : (k : carrier Y) → fiber (index X) (φ (index Y k)))
  where

  transported :
    {a b : E} {c : E′} (r : a ＝ b) (r′ : φ b ＝ c) (x : fiber (index Y) a)
    → transport (fiber (index X)) r′
        (extend φ Y X u b (transport (fiber (index Y)) r x))
      ＝ transport (fiber (index X)) (ap φ r ∙ r′) (extend φ Y X u a x)
  transported refl refl x = refl

------------------------------------------------------------------------
-- Morphisms along a translation

-- A morphism along τ sends each code of M into the fiber of N's decoding
-- over the image of M's. At an operation it is N's operation at the
-- shape `act` gives, its decoding read back along M's law.

Fibers :
  {s κ κ′ j j′ : Level} {E : Set j} {E′ : Set j′} (φ : E → E′)
  {γ : Desc {s = s} E} {γ′ : Desc {s = s} E′}
  (M : Algebra κ γ) (N : Algebra κ′ γ′) → Algebra.K M → Set (κ′ ⊔ j′)
Fibers φ M N k = fiber (Algebra.value N) (φ (Algebra.value M k))

module _
  {s κ κ′ j j′ : Level} {E : Set j} {E′ : Set j′} {φ : E → E′}
  {γ : Desc {s = s} E} {γ′ : Desc {s = s} E′}
  (arities : (A : Set s) (B : A → Set j′) → FunExt A B)
  (τ : Translation φ γ γ′) (M : Algebra κ γ) (N : Algebra κ′ γ′)
  (law : Law M) (law′ : Law N)
  where

  open Algebra M using (K; value; operation)

  step : Argument-Step (input γ (indexed K value)) operation (Fibers φ M N)
  step z h =
    let a =
          act arities τ (indexed K value)
            (indexed (Algebra.K N) (Algebra.value N)) z h
    in
    Algebra.operation N (pr₁ a) , (law′ (pr₁ a) ∙ (pr₂ a ∙ ap φ (law z ⁻¹)))

  Along : Set (s ⊔ κ ⊔ κ′ ⊔ j′)
  Along = Section (input γ (indexed K value)) operation (Fibers φ M N) step

------------------------------------------------------------------------
-- The identity

-- Along the identity translation the translated layer is the layer, so
-- `act` at the canonical points is `up` of `down`, which is the shape.

module _
  {s κ j : Level} {E : Set j} {γ : Desc {s = s} E}
  (arities : (A : Set s) (B : A → Set j) → FunExt A B)
  (M : Algebra κ γ) (law : Law M)
  where

  open Algebra M using (K; value; operation)

  identity-along : Along arities (identity γ) M M law law
  identity-along = record
    { valuation = λ k → k , refl
    ; equations = λ z →
        ap (λ w → operation z , w) (cancel (law z))
        ∙ ap
            ( λ t →
                operation (pr₁ t)
                , (law (pr₁ t) ∙ (pr₂ t ∙ ap (λ e → e) (law z ⁻¹))))
            ( ap
                ( λ m →
                    up arities (indexed K value) γ
                      (Mark γ (indexed K value) z)
                      ( ( skeleton (indexed K value) γ z
                        , collect (indexed K value) (fiber value) γ z
                            (canonical (indexed K value) γ z))
                      , m))
                ( ap-id (read (indexed K value) γ z)
                ∙ refl-right-neutral (read (indexed K value) γ z) ⁻¹)
            ∙ up-down arities (indexed K value) γ
                (Mark γ (indexed K value) z) (z , refl))
            ⁻¹
    }

------------------------------------------------------------------------
-- Composition

-- The composite of u after v at a code is v's point of N's fiber, carried
-- by u's extension to the fibers of N's decoding. At an operation, v's
-- equation and then u's bring it to P's operation at a translated shape
-- (`moved`, `reshape`); `act-up` identifies the translation of the
-- translated layer, and the layer-level identity is pointwise
-- (`transported`, `collect-natural`, `marks`).

module _
  {s κ κ′ κ″ j j′ j″ : Level}
  {E : Set j} {E′ : Set j′} {E″ : Set j″}
  {φ : E → E′} {φ′ : E′ → E″}
  {γ : Desc {s = s} E} {γ′ : Desc {s = s} E′} {γ″ : Desc {s = s} E″}
  (arities′ : (A : Set s) (B : A → Set j′) → FunExt A B)
  (positions′ : (A : Set s) (B : A → Set (κ′ ⊔ j′)) → FunExt A B)
  (arities″ : (A : Set s) (B : A → Set j″) → FunExt A B)
  (positions″ : (A : Set s) (B : A → Set (κ″ ⊔ j″)) → FunExt A B)
  (τ′ : Translation φ′ γ′ γ″) (τ : Translation φ γ γ′)
  (M : Algebra κ γ) (N : Algebra κ′ γ′) (P : Algebra κ″ γ″)
  (law : Law M) (law′ : Law N) (law″ : Law P)
  (u : Along arities″ τ′ N P law′ law″)
  (v : Along arities′ τ M N law law′)
  where

  open Algebra M using (K; value; operation)

  composed :
    (k : K)
    → fiber (Algebra.value P) (φ′ (φ (value k)))
  composed k =
    extend φ′ (indexed (Algebra.K N) (Algebra.value N))
      (indexed (Algebra.K P) (Algebra.value P))
      (Section.valuation u) (φ (value k)) (Section.valuation v k)

  layered :
    (z : Shape γ (indexed K value))
    → translate τ′ (indexed (Algebra.K P) (Algebra.value P))
        (φ′ (φ (Mark γ (indexed K value) z)))
        ( pushed φ′ (indexed (Algebra.K N) (Algebra.value N))
            (indexed (Algebra.K P) (Algebra.value P)) (Section.valuation u)
            γ′ (φ (Mark γ (indexed K value) z))
            ( translate τ (indexed (Algebra.K N) (Algebra.value N))
                (φ (Mark γ (indexed K value) z))
                ( ( skeleton (indexed K value) γ z
                  , collect (indexed K value)
                      (λ e → fiber (Algebra.value N) (φ e)) γ z
                      (λ p →
                        Section.valuation v (input γ (indexed K value) z p)))
                , ap φ (read (indexed K value) γ z))))
      ＝ translate (compose τ′ τ) (indexed (Algebra.K P) (Algebra.value P))
          (φ′ (φ (Mark γ (indexed K value) z)))
          ( ( skeleton (indexed K value) γ z
            , collect (indexed K value)
                (λ e → fiber (Algebra.value P) (φ′ (φ e))) γ z
                (λ p → composed (input γ (indexed K value) z p)))
          , ap (λ e → φ′ (φ e)) (read (indexed K value) γ z))
  layered z =
    let c = skeleton (indexed K value) γ z
    in
    ap₂
      (λ G m → (Translation.shape τ′ (Translation.shape τ c) , G) , m)
      ( positions″
          ( Position γ″ (indexed E″ (λ e → e))
              (Translation.shape τ′ (Translation.shape τ c)))
          ( λ q →
              fiber (Algebra.value P)
                ( input γ″ (indexed E″ (λ e → e))
                    (Translation.shape τ′ (Translation.shape τ c)) q))
          ( λ q →
              transport (fiber (Algebra.value P))
                (Translation.inputs τ′ (Translation.shape τ c) q)
                ( extend φ′ (indexed (Algebra.K N) (Algebra.value N))
                    (indexed (Algebra.K P) (Algebra.value P))
                    (Section.valuation u)
                    ( input γ′ (indexed E′ (λ e → e))
                        (Translation.shape τ c)
                        (Translation.back τ′ (Translation.shape τ c) q))
                    ( transport (fiber (Algebra.value N))
                        ( Translation.inputs τ c
                            (Translation.back τ′ (Translation.shape τ c) q))
                        ( collect (indexed K value)
                            (λ e → fiber (Algebra.value N) (φ e)) γ z
                            ( λ p →
                                Section.valuation v
                                  (input γ (indexed K value) z p))
                            ( Translation.back τ c
                                ( Translation.back τ′
                                    (Translation.shape τ c) q))))))
          ( λ q →
              transport (fiber (Algebra.value P))
                ( ap φ′
                    ( Translation.inputs τ c
                        (Translation.back τ′ (Translation.shape τ c) q))
                ∙ Translation.inputs τ′ (Translation.shape τ c) q)
                ( collect (indexed K value)
                    (λ e → fiber (Algebra.value P) (φ′ (φ e))) γ z
                    (λ p → composed (input γ (indexed K value) z p))
                    ( Translation.back τ c
                        ( Translation.back τ′
                            (Translation.shape τ c) q))))
          ( λ q →
              transported φ′ (indexed (Algebra.K N) (Algebra.value N))
                (indexed (Algebra.K P) (Algebra.value P))
                (Section.valuation u)
                ( Translation.inputs τ c
                    (Translation.back τ′ (Translation.shape τ c) q))
                (Translation.inputs τ′ (Translation.shape τ c) q)
                ( collect (indexed K value)
                    (λ e → fiber (Algebra.value N) (φ e)) γ z
                    ( λ p →
                        Section.valuation v
                          (input γ (indexed K value) z p))
                    ( Translation.back τ c
                        ( Translation.back τ′
                            (Translation.shape τ c) q)))
              ∙ ap
                  ( transport (fiber (Algebra.value P))
                      ( ap φ′
                          ( Translation.inputs τ c
                              ( Translation.back τ′
                                  (Translation.shape τ c) q))
                      ∙ Translation.inputs τ′ (Translation.shape τ c) q))
                  ( collect-natural (indexed K value)
                      (λ e → fiber (Algebra.value N) (φ e))
                      (λ e → fiber (Algebra.value P) (φ′ (φ e)))
                      ( λ e →
                          extend φ′ (indexed (Algebra.K N) (Algebra.value N))
                            (indexed (Algebra.K P) (Algebra.value P))
                            (Section.valuation u) (φ e))
                      γ z
                      ( λ p →
                          Section.valuation v
                            (input γ (indexed K value) z p))
                      ( Translation.back τ c
                          ( Translation.back τ′
                              (Translation.shape τ c) q))
                    ⁻¹)))
      ( marks φ φ′ (Translation.output τ′ (Translation.shape τ c))
          (Translation.output τ c)
          (read (indexed K value) γ z))

  compose-along : Along arities″ (compose τ′ τ) M P law law″
  compose-along = record
    { valuation = composed
    ; equations = λ z →
        let a =
              act arities′ τ (indexed K value)
                (indexed (Algebra.K N) (Algebra.value N)) z
                ( λ p →
                    Section.valuation v (input γ (indexed K value) z p))
            b =
              act arities″ τ′ (indexed (Algebra.K N) (Algebra.value N))
                (indexed (Algebra.K P) (Algebra.value P)) (pr₁ a)
                ( λ p →
                    Section.valuation u
                      ( input γ′
                          (indexed (Algebra.K N) (Algebra.value N))
                          (pr₁ a) p))
            r = law′ (pr₁ a) ∙ (pr₂ a ∙ ap φ (law z ⁻¹))
        in
        ap
          ( extend φ′ (indexed (Algebra.K N) (Algebra.value N))
              (indexed (Algebra.K P) (Algebra.value P))
              (Section.valuation u) (φ (value (operation z))))
          (Section.equations v z)
        ∙ ( ap
              ( transport
                  (λ e → fiber (Algebra.value P) (φ′ e)) r)
              (Section.equations u (pr₁ a))
          ∙ ( moved (Algebra.value P) φ′ r
                ( Algebra.operation P (pr₁ b)
                , ( law″ (pr₁ b)
                  ∙ (pr₂ b ∙ ap φ′ (law′ (pr₁ a) ⁻¹))))
            ∙ ( ap (λ w → Algebra.operation P (pr₁ b) , w)
                  ( reshape φ φ′ (law″ (pr₁ b)) (pr₂ b) (law′ (pr₁ a))
                      (pr₂ a) (law z ⁻¹))
              ∙ ap
                  ( λ t →
                      Algebra.operation P (pr₁ t)
                      , ( law″ (pr₁ t)
                        ∙ ( pr₂ t
                          ∙ ap (λ e → φ′ (φ e)) (law z ⁻¹))))
                  ( act-up arities′ positions′ arities″ positions″ τ′
                      (indexed (Algebra.K N) (Algebra.value N))
                      (indexed (Algebra.K P) (Algebra.value P))
                      (Section.valuation u)
                      (φ (Mark γ (indexed K value) z))
                      ( translate τ (indexed (Algebra.K N) (Algebra.value N))
                          (φ (Mark γ (indexed K value) z))
                          ( ( skeleton (indexed K value) γ z
                            , collect (indexed K value)
                                (λ e → fiber (Algebra.value N) (φ e)) γ z
                                ( λ p →
                                    Section.valuation v
                                      (input γ (indexed K value) z p)))
                          , ap φ (read (indexed K value) γ z)))
                  ∙ ap
                      ( up arities″
                          (indexed (Algebra.K P) (Algebra.value P)) γ″
                          (φ′ (φ (Mark γ (indexed K value) z))))
                      (layered z)))))
    }

------------------------------------------------------------------------
-- Morphisms of algebras

-- Along the identity translation, `act` is Action's assembly with the
-- adjusted extensionality (Layers' `assembled`), so its step is Morphism's
-- and the two kinds of section are the same.

module _
  {s κ κ′ j : Level} {E : Set j} {γ : Desc {s = s} E}
  (arities : (A : Set s) (B : A → Set j) → FunExt A B)
  (M : Algebra κ γ) (N : Algebra κ′ γ) (law : Law M) (law′ : Law N)
  where

  open Algebra M using (K; value; operation)

  steps-agree :
    (z : Shape γ (indexed K value))
    (h :
      (p : Position γ (indexed K value) z)
      → Morphism.Fibers M N (input γ (indexed K value) z p))
    → step arities (identity γ) M N law law′ z h
      ＝ Morphism.step (normal E arities) M N law law′ z h
  steps-agree z h =
    let w =
          assemble (normal E arities) (indexed K value)
            (indexed (Algebra.K N) (Algebra.value N)) γ z h
    in
    ap
      ( λ t →
          Algebra.operation N (pr₁ t)
          , (law′ (pr₁ t) ∙ (pr₂ t ∙ ap (λ e → e) (law z ⁻¹))))
      ( ap
          ( λ m →
              up arities (indexed (Algebra.K N) (Algebra.value N)) γ
                (Mark γ (indexed K value) z)
                ( ( skeleton (indexed K value) γ z
                  , collect (indexed K value)
                      (fiber (Algebra.value N)) γ z h)
                , m))
          (ap-id (read (indexed K value) γ z))
      ∙ assembled arities (indexed K value)
          (indexed (Algebra.K N) (Algebra.value N)) γ z h ⁻¹)
    ∙ ap
        ( λ d →
            Algebra.operation N (pr₁ w)
            , (law′ (pr₁ w) ∙ (pr₂ w ∙ d)))
        (ap-id (law z ⁻¹))

  along-morphism :
    Along arities (identity γ) M N law law′
    → Morphism.Morphism (normal E arities) M N law law′
  along-morphism v = record
    { valuation = Section.valuation v
    ; equations = λ z →
        Section.equations v z
        ∙ steps-agree z
            (λ p → Section.valuation v (input γ (indexed K value) z p))
    }

  morphism-along :
    Morphism.Morphism (normal E arities) M N law law′
    → Along arities (identity γ) M N law law′
  morphism-along f = record
    { valuation = Section.valuation f
    ; equations = λ z →
        Section.equations f z
        ∙ steps-agree z
            (λ p → Section.valuation f (input γ (indexed K value) z p)) ⁻¹
    }
