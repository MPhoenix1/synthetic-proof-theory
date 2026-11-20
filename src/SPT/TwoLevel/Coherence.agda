{-# OPTIONS --safe --without-K --two-level --no-projection-like #-}

module SPT.TwoLevel.Coherence where

-- Classes of identifications closed under path induction with coherent
-- data (Class). Inverses, composites and applications stay in the class.
-- The class every contains all identifications; strict contains those
-- induced by strict identifications of two-level type theory. Two
-- identifications in strict agree (strictly-agree), coherently.
-- Strict identification (_≐_) admits application (apˢ), transport
-- (transportˢ), composition (_∙ˢ_) and passage to identity (fibrant).

open import Agda.Primitive using (SSet; SSetω)
open import SPT.Base

------------------------------------------------------------------------
-- Strict identification and the outer unit type

infix 6 _≐_

data _≐_ {ℓ : Level} {A : Set ℓ} (x : A) : A → SSet ℓ where
  same : x ≐ x

module _ {ℓ : Level} {A : Set ℓ} where

  infixl 15 _∙ˢ_

  fibrant : {x y : A} → x ≐ y → x ＝ y
  fibrant same = refl

  _∙ˢ_ : {x y z : A} → x ≐ y → y ≐ z → x ≐ z
  same ∙ˢ e = e

module _ {ℓ κ : Level} {A : Set ℓ} {B : Set κ} where

  apˢ : (f : A → B) {x y : A} → x ≐ y → f x ≐ f y
  apˢ f same = same

module _ {ℓ κ : Level} {A : Set ℓ} (P : A → Set κ) where

  transportˢ : {x y : A} → x ≐ y → P x → P y
  transportˢ same u = u

record 𝟙ˢ {ℓ : Level} : SSet ℓ where
  constructor ⋆ˢ

------------------------------------------------------------------------
-- Coherence classes

record Class : SSetω where
  field
    Coherent : {κ : Level} {X : Set κ} {x y : X} → x ＝ y → SSet κ
    coherent-refl : {κ : Level} {X : Set κ} {x : X} →
      Coherent (refl {x = x})
    along-right-over :
      {κ ℓ μ ν : Level} {X : Set κ} {x : X}
      {W : (y : X) → x ＝ y → Set μ}
      {Z : (y : X) (e : x ＝ y) → W y e → Set ℓ}
      {a b : (y : X) (e : x ＝ y) (w : W y e) → Z y e w}
      (F : (y : X) (e : x ＝ y) (w : W y e) → a y e w ＝ b y e w)
      (H : (y : X) (e : x ＝ y) → W y e → SSet ν) →
      ((w : W x refl) → H x refl w → Coherent (F x refl w)) →
      {y : X} {e : x ＝ y} → Coherent e →
      (w : W y e) → H y e w → Coherent (F y e w)
    along-left-over :
      {κ ℓ μ ν : Level} {X : Set κ} {x : X}
      {W : (y : X) → y ＝ x → Set μ}
      {Z : (y : X) (e : y ＝ x) → W y e → Set ℓ}
      {a b : (y : X) (e : y ＝ x) (w : W y e) → Z y e w}
      (F : (y : X) (e : y ＝ x) (w : W y e) → a y e w ＝ b y e w)
      (H : (y : X) (e : y ＝ x) → W y e → SSet ν) →
      ((w : W x refl) → H x refl w → Coherent (F x refl w)) →
      {y : X} {e : y ＝ x} → Coherent e →
      (w : W y e) → H y e w → Coherent (F y e w)

-- Supplying the point fixes the identity before its coherence is used.
coherent-at : (K : Class) {κ : Level} {X : Set κ} (x : X) →
  Class.Coherent K (refl {x = x})
coherent-at K x = Class.coherent-refl K

------------------------------------------------------------------------
-- Path induction, inverses, composites and applications

module _ (K : Class) where

  open Class K

  along-right :
    {κ ℓ : Level} {X : Set κ} {x : X}
    {Z : (y : X) → x ＝ y → Set ℓ}
    {a b : (y : X) (e : x ＝ y) → Z y e}
    (F : (y : X) (e : x ＝ y) → a y e ＝ b y e) →
    Coherent (F x refl) → {y : X} {e : x ＝ y} → Coherent e →
    Coherent (F y e)
  along-right F c ce =
    along-right-over (λ y e (w : 𝟙) → F y e) (λ y e w → 𝟙ˢ {lzero})
      (λ w h → c) ce ⋆ ⋆ˢ

  along-left :
    {κ ℓ : Level} {X : Set κ} {x : X}
    {Z : (y : X) → y ＝ x → Set ℓ}
    {a b : (y : X) (e : y ＝ x) → Z y e}
    (F : (y : X) (e : y ＝ x) → a y e ＝ b y e) →
    Coherent (F x refl) → {y : X} {e : y ＝ x} → Coherent e →
    Coherent (F y e)
  along-left F c ce =
    along-left-over (λ y e (w : 𝟙) → F y e) (λ y e w → 𝟙ˢ {lzero})
      (λ w h → c) ce ⋆ ⋆ˢ

  coherent-ap :
    {κ ℓ : Level} {X : Set κ} {Y : Set ℓ} (f : X → Y) {x y : X}
    {e : x ＝ y} → Coherent e → Coherent (ap f e)
  coherent-ap f ce = along-right (λ y e → ap f e) coherent-refl ce

  coherent-⁻¹ :
    {κ : Level} {X : Set κ} {x y : X} {e : x ＝ y} → Coherent e →
    Coherent (e ⁻¹)
  coherent-⁻¹ ce = along-right (λ y e → e ⁻¹) coherent-refl ce

  coherent-∙ :
    {κ : Level} {X : Set κ} {x y z : X} {e : x ＝ y} {d : y ＝ z} →
    Coherent e → Coherent d → Coherent (e ∙ d)
  coherent-∙ {e = e} ce cd =
    along-right (λ z d′ → e ∙ d′)
      (along-right (λ y e′ → e′ ∙ refl) coherent-refl ce) cd

  coherent-ap₂ :
    {κ ℓ μ : Level} {X : Set κ} {Y : Set ℓ} {W : Set μ}
    (f : X → Y → W) {x x′ : X} {y y′ : Y} {e : x ＝ x′} {d : y ＝ y′} →
    Coherent e → Coherent d → Coherent (ap₂ f e d)
  coherent-ap₂ f {e = e} ce cd =
    along-right (λ y′ d′ → ap₂ f e d′)
      (along-right (λ x′ e′ → ap₂ f e′ refl) coherent-refl ce) cd

------------------------------------------------------------------------
-- Every identification

every : Class
every = record
  { Coherent = λ e → 𝟙ˢ
  ; coherent-refl = ⋆ˢ
  ; along-right-over = λ F H base ce w h → ⋆ˢ
  ; along-left-over = λ F H base ce w h → ⋆ˢ
  }

------------------------------------------------------------------------
-- Identifications induced by strict ones

record Strictly {κ : Level} {X : Set κ} {x y : X} (e : x ＝ y) : SSet κ
  where
  constructor strictly
  field
    witness : x ≐ y
    agrees : fibrant witness ≐ e

strictly-right :
  {κ ℓ μ ν : Level} {X : Set κ} {x : X}
  {W : (y : X) → x ＝ y → Set μ}
  {Z : (y : X) (e : x ＝ y) → W y e → Set ℓ}
  {a b : (y : X) (e : x ＝ y) (w : W y e) → Z y e w}
  (F : (y : X) (e : x ＝ y) (w : W y e) → a y e w ＝ b y e w)
  (H : (y : X) (e : x ＝ y) → W y e → SSet ν) →
  ((w : W x refl) → H x refl w → Strictly (F x refl w)) →
  {y : X} {e : x ＝ y} → Strictly e →
  (w : W y e) → H y e w → Strictly (F y e w)
strictly-right F H base (strictly same same) w h = base w h

strictly-left :
  {κ ℓ μ ν : Level} {X : Set κ} {x : X}
  {W : (y : X) → y ＝ x → Set μ}
  {Z : (y : X) (e : y ＝ x) → W y e → Set ℓ}
  {a b : (y : X) (e : y ＝ x) (w : W y e) → Z y e w}
  (F : (y : X) (e : y ＝ x) (w : W y e) → a y e w ＝ b y e w)
  (H : (y : X) (e : y ＝ x) → W y e → SSet ν) →
  ((w : W x refl) → H x refl w → Strictly (F x refl w)) →
  {y : X} {e : y ＝ x} → Strictly e →
  (w : W y e) → H y e w → Strictly (F y e w)
strictly-left F H base (strictly same same) w h = base w h

strict : Class
strict = record
  { Coherent = Strictly
  ; coherent-refl = strictly same same
  ; along-right-over = strictly-right
  ; along-left-over = strictly-left
  }

module _ {κ : Level} {X : Set κ} {x y : X} {e d : x ＝ y} where

  strictly-agree : Strictly e → Strictly d → e ＝ d
  strictly-agree (strictly same same) (strictly same same) = refl

  strictly-agree-coherent : (ce : Strictly e) (cd : Strictly d) →
    Strictly (strictly-agree ce cd)
  strictly-agree-coherent (strictly same same) (strictly same same) =
    strictly same same
