{-# OPTIONS --safe --without-K #-}

module SPT.IR.Translation where

-- Translations of Dybjer–Setzer descriptions along a map φ of their
-- outputs: a map of the shapes over the outputs, each position of the
-- target read back at a position of the source, with the inputs and the
-- output identified along φ (`Translation`, `identity`, `compose`). A
-- translation acts on layers by its shape map and reads points back
-- (`translate`), so on shapes over any family, through Layers (`act`). The
-- action is natural: acting on an assembled layer is translating the
-- layer's image (`extend`, `pushed`, `act-marked`, `act-up`).

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Fibers using (fiber)

open import SPT.IR.Action using (assemble)
open import SPT.IR.Description using
  (Desc; Indexed; carrier; index; indexed; Shape; Mark)
open import SPT.IR.Layers using
  ( skeleton; read; collect; collect-natural; Marked; Layered; normal; up
  ; canonical; down-up)
open import SPT.IR.Restriction using (Position; input; Layer)

------------------------------------------------------------------------
-- Translations

-- A shape of γ over its outputs goes to a shape of γ′ over its outputs.
-- Each position of the target reads back a position of the source, so a
-- position may be erased or used twice; its input is the image of the
-- input read back. The output is the image of the output.

record Translation
  {s j j′ : Level} {E : Set j} {E′ : Set j′} (φ : E → E′)
  (γ : Desc {s = s} E) (γ′ : Desc {s = s} E′) : Set (s ⊔ j ⊔ j′) where
  field
    shape :
      Shape γ (indexed E (λ e → e)) → Shape γ′ (indexed E′ (λ e → e))
    back :
      (c : Shape γ (indexed E (λ e → e)))
      → Position γ′ (indexed E′ (λ e → e)) (shape c)
      → Position γ (indexed E (λ e → e)) c
    inputs :
      (c : Shape γ (indexed E (λ e → e)))
      (q : Position γ′ (indexed E′ (λ e → e)) (shape c))
      → φ (input γ (indexed E (λ e → e)) c (back c q))
        ＝ input γ′ (indexed E′ (λ e → e)) (shape c) q
    output :
      (c : Shape γ (indexed E (λ e → e)))
      → Mark γ′ (indexed E′ (λ e → e)) (shape c)
        ＝ φ (Mark γ (indexed E (λ e → e)) c)

identity :
  {s j : Level} {E : Set j} (γ : Desc {s = s} E)
  → Translation (λ e → e) γ γ
identity γ = record
  { shape = λ c → c
  ; back = λ c q → q
  ; inputs = λ c q → refl
  ; output = λ c → refl
  }

compose :
  {s j j′ j″ : Level} {E : Set j} {E′ : Set j′} {E″ : Set j″}
  {φ : E → E′} {φ′ : E′ → E″}
  {γ : Desc {s = s} E} {γ′ : Desc {s = s} E′} {γ″ : Desc {s = s} E″}
  → Translation φ′ γ′ γ″ → Translation φ γ γ′
  → Translation (λ e → φ′ (φ e)) γ γ″
compose {φ′ = φ′} τ′ τ = record
  { shape = λ c → Translation.shape τ′ (Translation.shape τ c)
  ; back = λ c q →
      Translation.back τ c
        (Translation.back τ′ (Translation.shape τ c) q)
  ; inputs = λ c q →
      ap φ′
        ( Translation.inputs τ c
            (Translation.back τ′ (Translation.shape τ c) q))
      ∙ Translation.inputs τ′ (Translation.shape τ c) q
  ; output = λ c →
      Translation.output τ′ (Translation.shape τ c)
      ∙ ap φ′ (Translation.output τ c)
  }

------------------------------------------------------------------------
-- The action on layers and on shapes

-- A layer of γ with points of W along φ, the image of its output
-- identified with o (`Pointed`), translates to a layer of γ′ with points
-- of W: the point at a position of the target is the point read back,
-- moved along the identification of inputs. On a shape over Z with points
-- of W along φ at its inputs, the action is `up` of the translated layer
-- of its skeleton (`act`).

Pointed :
  {s κ j j′ : Level} {E : Set j} {E′ : Set j′} (φ : E → E′)
  (γ : Desc {s = s} E) (W : Indexed κ E′) → E′
  → Set (s ⊔ κ ⊔ j ⊔ j′)
Pointed {E = E} φ γ W o =
  Σ (Layer (λ e → e) (λ e → fiber (index W) (φ e)) γ)
    (λ l → φ (Mark γ (indexed E (λ e → e)) (pr₁ l)) ＝ o)

module _
  {s κ j j′ : Level} {E : Set j} {E′ : Set j′} {φ : E → E′}
  {γ : Desc {s = s} E} {γ′ : Desc {s = s} E′}
  (τ : Translation φ γ γ′) (W : Indexed κ E′)
  where

  translate : (o : E′) → Pointed φ γ W o → Layered γ′ W o
  translate o ((c , h) , m) =
    ( Translation.shape τ c
    , ( λ q →
          transport (fiber (index W)) (Translation.inputs τ c q)
            (h (Translation.back τ c q))))
    , (Translation.output τ c ∙ m)

module _
  {s κ κ′ j j′ : Level} {E : Set j} {E′ : Set j′} {φ : E → E′}
  {γ : Desc {s = s} E} {γ′ : Desc {s = s} E′}
  (arities : (A : Set s) (B : A → Set j′) → FunExt A B)
  (τ : Translation φ γ γ′) (Z : Indexed κ E) (W : Indexed κ′ E′)
  where

  act :
    (z : Shape γ Z)
    → ((p : Position γ Z z) → fiber (index W) (φ (index Z (input γ Z z p))))
    → Marked γ′ W (φ (Mark γ Z z))
  act z h =
    up arities W γ′ (φ (Mark γ Z z))
      ( translate τ W (φ (Mark γ Z z))
          ( (skeleton Z γ z , collect Z (λ e → fiber (index W) (φ e)) γ z h)
          , ap φ (read Z γ z)))

------------------------------------------------------------------------
-- Naturality

-- A valuation u of Y's codes in the fibers of X's decoding along φ
-- extends to the fibers of Y's decoding (`extend`), and so acts on layers
-- (`pushed`). Acting on an assembled layer at the values of u is
-- translating its image under u (`act-up`): the assembled layer is `down`
-- of itself, and `collect` commutes with the extension of u.

module _
  {κ κ′ j j′ : Level} {E : Set j} {E′ : Set j′} (φ : E → E′)
  (Y : Indexed κ E) (X : Indexed κ′ E′)
  (u : (k : carrier Y) → fiber (index X) (φ (index Y k)))
  where

  extend : (e : E) → fiber (index Y) e → fiber (index X) (φ e)
  extend e x =
    transport (λ b → fiber (index X) (φ b)) (pr₂ x) (u (pr₁ x))

  pushed :
    {s : Level} (γ : Desc {s = s} E) (o : E)
    → Layered γ Y o → Pointed φ γ X (φ o)
  pushed γ o ((c , h) , m) =
    (c , (λ p → extend (input γ (indexed E (λ e → e)) c p) (h p))) , ap φ m

assoc₃ :
  {ℓ : Level} {A : Set ℓ} {a b c d e : A}
  (p : a ＝ b) (q : b ＝ c) (r : c ＝ d) (t : d ＝ e)
  → (p ∙ (q ∙ r)) ∙ t ＝ p ∙ (q ∙ (r ∙ t))
assoc₃ refl refl r t = refl

module _
  {s κ κ′ j j′ : Level} {E : Set j} {E′ : Set j′} {φ : E → E′}
  {γ : Desc {s = s} E} {γ′ : Desc {s = s} E′}
  (arities : (A : Set s) (B : A → Set j) → FunExt A B)
  (positions : (A : Set s) (B : A → Set (κ ⊔ j)) → FunExt A B)
  (arities′ : (A : Set s) (B : A → Set j′) → FunExt A B)
  (positions′ : (A : Set s) (B : A → Set (κ′ ⊔ j′)) → FunExt A B)
  (τ : Translation φ γ γ′) (Y : Indexed κ E) (X : Indexed κ′ E′)
  (u : (k : carrier Y) → fiber (index X) (φ (index Y k)))
  where

  act-marked : (o : E) → Marked γ Y o → Marked γ′ X (φ o)
  act-marked o (y , m) =
    let a = act arities′ τ Y X y (λ p → u (input γ Y y p))
    in pr₁ a , (pr₂ a ∙ ap φ m)

  act-up :
    (o : E) (t : Layered γ Y o)
    → act-marked o (up arities Y γ o t)
      ＝ up arities′ X γ′ (φ o) (translate τ X (φ o) (pushed φ Y X u γ o t))
  act-up o t =
    let y = pr₁ (up arities Y γ o t)
        n = pr₂ (up arities Y γ o t)
        c = skeleton Y γ y
        F =
          collect Y (λ e → fiber (index X) (φ e)) γ y
            (λ p → u (input γ Y y p))
        a =
          assemble (normal E′ arities′) (indexed E′ (λ e → e)) X γ′
            (Translation.shape τ c)
            ( λ q →
                transport (fiber (index X)) (Translation.inputs τ c q)
                  (F (Translation.back τ c q)))
    in
    ap (λ w → pr₁ a , w)
      (assoc₃ (pr₂ a) (Translation.output τ c) (ap φ (read Y γ y)) (ap φ n))
    ∙ ( ap₂
          ( λ G M →
              up arities′ X γ′ (φ o)
                (translate τ X (φ o) ((c , G) , M)))
          ( positions′ (Position γ (indexed E (λ e → e)) c)
              (λ p → fiber (index X) (φ (input γ (indexed E (λ e → e)) c p)))
              F
              ( λ p →
                  extend φ Y X u (input γ (indexed E (λ e → e)) c p)
                    (collect Y (fiber (index Y)) γ y (canonical Y γ y) p))
              ( collect-natural Y (fiber (index Y))
                  (λ e → fiber (index X) (φ e)) (extend φ Y X u) γ y
                  (canonical Y γ y)))
          (ap-∙ φ (read Y γ y) n ⁻¹)
      ∙ ap
          ( λ t′ →
              up arities′ X γ′ (φ o)
                (translate τ X (φ o) (pushed φ Y X u γ o t′)))
          (down-up arities positions Y γ o t))
