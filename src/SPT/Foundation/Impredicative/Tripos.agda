{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Impredicative.Tripos where

-- The canonical hyperdoctrine of small predicates, and triposes. Over a base
-- of types of level α, the predicates on X are the maps X → Set ℓ, ordered by
-- inclusion and reindexed by precomposition (`reindex`; `reindex-identity`,
-- `reindex-compose` by computation), with the pointwise Heyting operations
-- (`top`, `bottom`, `_∧_`, `_∨_`, `_⇒_`) and their universal properties
-- (`every-predicate-is-below-top`, `bottom-is-below-every-predicate`,
-- `meet-is-the-greatest-lower-bound`, `join-is-the-least-upper-bound`,
-- `implication-is-right-adjoint-to-meet`), which reindexing preserves by
-- computation (`reindex-preserves-the-heyting-operations`). A tripos adds
-- quantifiers along every map of the base, adjoint to reindexing and
-- satisfying Beck–Chevalley along the canonical pullbacks
-- (`Canonical-Pullback`, `Quantifiers`), and a generic predicate, of which
-- every predicate is a reindexing up to equivalence
-- (`Generic-Predicate`, `Tripos`).
--
-- Over the small base (α = ℓ) the quantifiers are Σ and Π along the fibers,
-- with no hypothesis (`Exists`, `All`, `canonical-quantifiers`), and a
-- generic predicate is exactly a classifier
-- (`classifier-gives-generic-predicate`,
-- `generic-predicate-gives-classifier`): the hyperdoctrine is a tripos
-- exactly when Set ℓ has a classifier (`classifier-gives-tripos`,
-- `tripos-gives-classifier`). Its power objects classify relations
-- (`Power-Object`, `power-member`, `power-objects-classify-relations`) and
-- are power presentations (`generic-predicate-gives-power-presentations`).
-- Over the base of the next level (α = ℓ + 1) the generic predicate is
-- free, Set ℓ with the identity (`types-are-generic`), and weak resizing
-- supplies the quantifiers (`weak-resizing-gives-quantifiers`,
-- `weak-resizing-gives-tripos`). So a classifier and weak resizing are the
-- two halves of the tripos axioms, over the two bases. Quantifiers over the
-- next level give each of its types a small reflection (`Small-Reflection`,
-- `quantifiers-give-small-reflections`); no converse to weak resizing is
-- claimed.

open import SPT.Base
open import SPT.Foundation.Impredicative.Classification using
  (Resizing; Classifier; chosen; encode; decode)
open import SPT.Foundation.Impredicative.Classifier using
  (Power-Presentation)
open import SPT.Foundation.LogicalEquivalence using (_⇔_)

------------------------------------------------------------------------
-- Reindexing

module _ {α β ℓ : Level} {X : Set α} {Y : Set β} where

  -- Mathematical shape: reindex f ψ = ψ ∘ f.
  reindex : (X → Y) → (Y → Set ℓ) → X → Set ℓ
  reindex f ψ x = ψ (f x)

module _ {α ℓ : Level} {X : Set α} where

  reindex-identity : (φ : X → Set ℓ) → reindex (λ (x : X) → x) φ ＝ φ
  reindex-identity φ = refl

module _ {α ℓ : Level} {X Y Z : Set α} where

  reindex-compose : (f : X → Y) (g : Y → Z) (ψ : Z → Set ℓ) →
    reindex (λ x → g (f x)) ψ ＝ reindex f (reindex g ψ)
  reindex-compose f g ψ = refl

------------------------------------------------------------------------
-- The Heyting operations, pointwise

module _ {α : Level} {X : Set α} where

  top : (ℓ : Level) → X → Set ℓ
  top ℓ x = Lift ℓ 𝟙

  bottom : (ℓ : Level) → X → Set ℓ
  bottom ℓ x = Lift ℓ 𝟘

module _ {α ℓ : Level} {X : Set α} where

  infixr 54 _∧_
  infixr 52 _∨_
  infixr 50 _⇒_

  _∧_ : (X → Set ℓ) → (X → Set ℓ) → X → Set ℓ
  (φ ∧ ψ) x = φ x × ψ x

  _∨_ : (X → Set ℓ) → (X → Set ℓ) → X → Set ℓ
  (φ ∨ ψ) x = φ x ⊎ ψ x

  _⇒_ : (X → Set ℓ) → (X → Set ℓ) → X → Set ℓ
  (φ ⇒ ψ) x = φ x → ψ x

module _ {α ℓ : Level} {X : Set α} where

  every-predicate-is-below-top : (φ : X → Set ℓ) → φ ⊆ᵖ top ℓ
  every-predicate-is-below-top φ x p = lift ⋆

  bottom-is-below-every-predicate : (φ : X → Set ℓ) → bottom ℓ ⊆ᵖ φ
  bottom-is-below-every-predicate φ x b = 𝟘-elim (lower b)

  meet-is-the-greatest-lower-bound : (χ φ ψ : X → Set ℓ) →
    (χ ⊆ᵖ φ ∧ ψ) ⇔ ((χ ⊆ᵖ φ) × (χ ⊆ᵖ ψ))
  meet-is-the-greatest-lower-bound χ φ ψ =
    (λ h → (λ x p → pr₁ (h x p)) , (λ x p → pr₂ (h x p))) ,
    (λ h x p → pr₁ h x p , pr₂ h x p)

  join-is-the-least-upper-bound : (φ ψ χ : X → Set ℓ) →
    (φ ∨ ψ ⊆ᵖ χ) ⇔ ((φ ⊆ᵖ χ) × (ψ ⊆ᵖ χ))
  join-is-the-least-upper-bound φ ψ χ =
    (λ h → (λ x p → h x (inl p)) , (λ x q → h x (inr q))) ,
    (λ h x → cases (pr₁ h x) (pr₂ h x))

  implication-is-right-adjoint-to-meet : (φ χ ψ : X → Set ℓ) →
    (φ ∧ χ ⊆ᵖ ψ) ⇔ (φ ⊆ᵖ χ ⇒ ψ)
  implication-is-right-adjoint-to-meet φ χ ψ =
    (λ h x p q → h x (p , q)) ,
    (λ h x w → h x (pr₁ w) (pr₂ w))

module _ {α ℓ : Level} {X Y : Set α} where

  reindex-preserves-the-heyting-operations : (f : X → Y)
    (φ ψ : Y → Set ℓ) →
    (reindex f (φ ∧ ψ) ＝ reindex f φ ∧ reindex f ψ) ×
    (reindex f (φ ∨ ψ) ＝ reindex f φ ∨ reindex f ψ) ×
    (reindex f (φ ⇒ ψ) ＝ reindex f φ ⇒ reindex f ψ)
  reindex-preserves-the-heyting-operations f φ ψ = refl , refl , refl

------------------------------------------------------------------------
-- Quantifiers and generic predicates

module _ {α : Level} {X Y Z : Set α} where

  -- Mathematical shape: Σ ((x , z) : X × Z). f x ＝ g z.
  Canonical-Pullback : (X → Y) → (Z → Y) → Set α
  Canonical-Pullback f g = Σ (X × Z) (λ p → f (pr₁ p) ＝ g (pr₂ p))

  pullback-left : (f : X → Y) (g : Z → Y) → Canonical-Pullback f g → X
  pullback-left f g w = pr₁ (pr₁ w)

  pullback-right : (f : X → Y) (g : Z → Y) → Canonical-Pullback f g → Z
  pullback-right f g w = pr₂ (pr₁ w)

-- Mathematical shape: adjoints to reindexing on both sides along every map,
-- satisfying Beck–Chevalley along the canonical pullbacks.
record Quantifiers (α ℓ : Level) : Set (lsuc α ⊔ lsuc ℓ) where
  field
    exists : {X Y : Set α} → (X → Y) → (X → Set ℓ) → Y → Set ℓ
    all : {X Y : Set α} → (X → Y) → (X → Set ℓ) → Y → Set ℓ
    exists-adjoint : {X Y : Set α} (f : X → Y) (φ : X → Set ℓ)
      (ψ : Y → Set ℓ) → (exists f φ ⊆ᵖ ψ) ⇔ (φ ⊆ᵖ reindex f ψ)
    all-adjoint : {X Y : Set α} (f : X → Y) (φ : X → Set ℓ)
      (ψ : Y → Set ℓ) → (reindex f ψ ⊆ᵖ φ) ⇔ (ψ ⊆ᵖ all f φ)
    exists-beck-chevalley : {X Y Z : Set α} (f : X → Y) (g : Z → Y)
      (φ : X → Set ℓ) →
      reindex g (exists f φ) ≈ᵖ
        exists (pullback-right f g) (reindex (pullback-left f g) φ)
    all-beck-chevalley : {X Y Z : Set α} (f : X → Y) (g : Z → Y)
      (φ : X → Set ℓ) →
      reindex g (all f φ) ≈ᵖ
        all (pullback-right f g) (reindex (pullback-left f g) φ)

-- Mathematical shape: an object proxies of the base and a predicate proxy
-- on it, of which every predicate is a reindexing up to equivalence.
record Generic-Predicate (α ℓ : Level) : Set (lsuc α ⊔ lsuc ℓ) where
  field
    proxies : Set α
    proxy : proxies → Set ℓ
    classify : (X : Set α) (φ : X → Set ℓ) →
      Σ (X → proxies) (λ χ → φ ≈ᵖ reindex χ proxy)

record Tripos (α ℓ : Level) : Set (lsuc α ⊔ lsuc ℓ) where
  field
    quantifiers : Quantifiers α ℓ
    generic : Generic-Predicate α ℓ

------------------------------------------------------------------------
-- The canonical quantifiers

module _ {α ℓ : Level} {X Y : Set α} where

  -- Mathematical shape: Exists f φ y = Σ (x : X). (f x ＝ y) × φ x.
  Exists : (X → Y) → (X → Set ℓ) → Y → Set (α ⊔ ℓ)
  Exists f φ y = Σ X (λ x → (f x ＝ y) × φ x)

  -- Mathematical shape: All f φ y = Π (x : X). f x ＝ y → φ x.
  All : (X → Y) → (X → Set ℓ) → Y → Set (α ⊔ ℓ)
  All f φ y = (x : X) → f x ＝ y → φ x

module _ {α ℓ κ : Level} {X Y : Set α} where

  Exists-is-left-adjoint : (f : X → Y) (φ : X → Set ℓ) (ψ : Y → Set κ) →
    (Exists f φ ⊆ᵖ ψ) ⇔ (φ ⊆ᵖ reindex f ψ)
  Exists-is-left-adjoint f φ ψ =
    (λ h x p → h (f x) (x , refl , p)) ,
    (λ k y w → transport ψ (pr₁ (pr₂ w)) (k (pr₁ w) (pr₂ (pr₂ w))))

  All-is-right-adjoint : (f : X → Y) (φ : X → Set ℓ) (ψ : Y → Set κ) →
    (reindex f ψ ⊆ᵖ φ) ⇔ (ψ ⊆ᵖ All f φ)
  All-is-right-adjoint f φ ψ =
    (λ k y q x e → k x (transport ψ (e ⁻¹) q)) ,
    (λ k x q → k (f x) q x refl)

module _ {α ℓ : Level} {X Y Z : Set α} where

  Exists-satisfies-beck-chevalley : (f : X → Y) (g : Z → Y)
    (φ : X → Set ℓ) →
    reindex g (Exists f φ) ≈ᵖ
      Exists (pullback-right f g) (reindex (pullback-left f g) φ)
  Exists-satisfies-beck-chevalley f g φ =
    (λ z w → ((pr₁ w , z) , pr₁ (pr₂ w)) , refl , pr₂ (pr₂ w)) ,
    ( λ z w →
        pr₁ (pr₁ (pr₁ w)) ,
        pr₂ (pr₁ w) ∙ ap g (pr₁ (pr₂ w)) ,
        pr₂ (pr₂ w))

  All-satisfies-beck-chevalley : (f : X → Y) (g : Z → Y)
    (φ : X → Set ℓ) →
    reindex g (All f φ) ≈ᵖ
      All (pullback-right f g) (reindex (pullback-left f g) φ)
  All-satisfies-beck-chevalley f g φ =
    (λ z h p moved → h (pr₁ (pr₁ p)) (pr₂ p ∙ ap g moved)) ,
    (λ z h x e → h ((x , z) , e) refl)

------------------------------------------------------------------------
-- The small base

-- Over the small base, Σ and Π are the quantifiers, with no hypothesis.
canonical-quantifiers : (ℓ : Level) → Quantifiers ℓ ℓ
canonical-quantifiers ℓ = record
  { exists = Exists
  ; all = All
  ; exists-adjoint = Exists-is-left-adjoint
  ; all-adjoint = All-is-right-adjoint
  ; exists-beck-chevalley = Exists-satisfies-beck-chevalley
  ; all-beck-chevalley = All-satisfies-beck-chevalley
  }

-- A classifier is a generic predicate over the small base.
classifier-gives-generic-predicate : {ℓ : Level} →
  Classifier (λ (X : Set ℓ) → X) → Generic-Predicate ℓ ℓ
classifier-gives-generic-predicate C = record
  { proxies = Classifier.proxies C
  ; proxy = Classifier.proxy C
  ; classify = λ X φ →
      (λ x → chosen C (φ x)) ,
      (λ x → encode C (φ x)) ,
      (λ x → decode C (φ x))
  }

-- A generic predicate over the small base is a classifier: the predicates
-- on the unit type are the small types.
generic-predicate-gives-classifier : {ℓ : Level} →
  Generic-Predicate ℓ ℓ → Classifier (λ (X : Set ℓ) → X)
generic-predicate-gives-classifier {ℓ} G = record
  { proxies = Generic-Predicate.proxies G
  ; proxy = Generic-Predicate.proxy G
  ; classify = λ Y →
      pr₁
        (Generic-Predicate.classify G (Lift ℓ 𝟙) (λ (u : Lift ℓ 𝟙) → Y))
        (lift ⋆) ,
      pr₁
        ( pr₂
            ( Generic-Predicate.classify G (Lift ℓ 𝟙)
                (λ (u : Lift ℓ 𝟙) → Y)))
        (lift ⋆) ,
      pr₂
        ( pr₂
            ( Generic-Predicate.classify G (Lift ℓ 𝟙)
                (λ (u : Lift ℓ 𝟙) → Y)))
        (lift ⋆)
  }

-- The canonical hyperdoctrine over Set ℓ is a tripos exactly when Set ℓ has
-- a classifier.
classifier-gives-tripos : {ℓ : Level} → Classifier (λ (X : Set ℓ) → X) →
  Tripos ℓ ℓ
classifier-gives-tripos {ℓ} C = record
  { quantifiers = canonical-quantifiers ℓ
  ; generic = classifier-gives-generic-predicate C
  }

tripos-gives-classifier : {ℓ : Level} → Tripos ℓ ℓ →
  Classifier (λ (X : Set ℓ) → X)
tripos-gives-classifier T =
  generic-predicate-gives-classifier (Tripos.generic T)

------------------------------------------------------------------------
-- Power objects

module _ {α ℓ : Level} (G : Generic-Predicate α ℓ) where

  -- The maps from X to the generic object.
  Power-Object : Set α → Set α
  Power-Object X = X → Generic-Predicate.proxies G

  -- Membership, read through the generic predicate.
  power-member : {X : Set α} → X → Power-Object X → Set ℓ
  power-member x s = Generic-Predicate.proxy G (s x)

  -- Every relation between X and Y is membership along a map from Y to the
  -- power object of X.
  power-objects-classify-relations : {X Y : Set α} (ρ : X × Y → Set ℓ) →
    Σ (Y → Power-Object X)
      (λ s → ρ ≈ᵖ (λ p → power-member (pr₁ p) (s (pr₂ p))))
  power-objects-classify-relations {X} {Y} ρ =
    (λ y x → pr₁ (Generic-Predicate.classify G (X × Y) ρ) (x , y)) ,
    pr₂ (Generic-Predicate.classify G (X × Y) ρ)

-- Over the small base, the power objects are power presentations.
generic-predicate-gives-power-presentations : {ℓ : Level} →
  Generic-Predicate ℓ ℓ → (A : Set ℓ) → Power-Presentation A
generic-predicate-gives-power-presentations G A = record
  { Subsets = Power-Object G A
  ; member = λ s a → power-member G a s
  ; retain = λ X → pr₁ (Generic-Predicate.classify G A X)
  ; recover = λ X a →
      pr₁ (pr₂ (Generic-Predicate.classify G A X)) a ,
      pr₂ (pr₂ (Generic-Predicate.classify G A X)) a
  }

------------------------------------------------------------------------
-- The base of the next level

-- Set ℓ is an object of that base and the identity a generic predicate,
-- with no hypothesis.
types-are-generic : (ℓ : Level) → Generic-Predicate (lsuc ℓ) ℓ
types-are-generic ℓ = record
  { proxies = Set ℓ
  ; proxy = λ X → X
  ; classify = λ X φ → φ , (λ x p → p) , (λ x p → p)
  }

-- Weak resizing presents the canonical quantifiers over the next level.
weak-resizing-gives-quantifiers : {ℓ : Level} →
  Resizing (λ (X : Set ℓ) → X) → Quantifiers (lsuc ℓ) ℓ
weak-resizing-gives-quantifiers r = record
  { exists = λ f φ y → pr₁ (r (Exists f φ y))
  ; all = λ f φ y → pr₁ (r (All f φ y))
  ; exists-adjoint = λ f φ ψ →
      ( λ h →
          pr₁ (Exists-is-left-adjoint f φ ψ)
            (λ y e → h y (pr₁ (pr₂ (r (Exists f φ y))) e))) ,
      ( λ k y e →
          pr₂ (Exists-is-left-adjoint f φ ψ) k y
            (pr₂ (pr₂ (r (Exists f φ y))) e))
  ; all-adjoint = λ f φ ψ →
      ( λ k y q →
          pr₁ (pr₂ (r (All f φ y))) (pr₁ (All-is-right-adjoint f φ ψ) k y q)) ,
      ( λ k →
          pr₂ (All-is-right-adjoint f φ ψ)
            (λ y q → pr₂ (pr₂ (r (All f φ y))) (k y q)))
  ; exists-beck-chevalley = λ f g φ →
      ( λ z e →
          pr₁
            ( pr₂
                ( r
                    ( Exists (pullback-right f g)
                        (reindex (pullback-left f g) φ) z)))
            ( pr₁ (Exists-satisfies-beck-chevalley f g φ) z
                (pr₂ (pr₂ (r (Exists f φ (g z)))) e))) ,
      ( λ z e →
          pr₁ (pr₂ (r (Exists f φ (g z))))
            ( pr₂ (Exists-satisfies-beck-chevalley f g φ) z
                ( pr₂
                    ( pr₂
                        ( r
                            ( Exists (pullback-right f g)
                                (reindex (pullback-left f g) φ) z)))
                    e)))
  ; all-beck-chevalley = λ f g φ →
      ( λ z h →
          pr₁
            ( pr₂
                ( r
                    ( All (pullback-right f g)
                        (reindex (pullback-left f g) φ) z)))
            ( pr₁ (All-satisfies-beck-chevalley f g φ) z
                (pr₂ (pr₂ (r (All f φ (g z)))) h))) ,
      ( λ z h →
          pr₁ (pr₂ (r (All f φ (g z))))
            ( pr₂ (All-satisfies-beck-chevalley f g φ) z
                ( pr₂
                    ( pr₂
                        ( r
                            ( All (pullback-right f g)
                                (reindex (pullback-left f g) φ) z)))
                    h)))
  }

-- With weak resizing, the hyperdoctrine of small predicates over the types
-- of the next level is a tripos.
weak-resizing-gives-tripos : {ℓ : Level} → Resizing (λ (X : Set ℓ) → X) →
  Tripos (lsuc ℓ) ℓ
weak-resizing-gives-tripos {ℓ} r = record
  { quantifiers = weak-resizing-gives-quantifiers r
  ; generic = types-are-generic ℓ
  }

------------------------------------------------------------------------
-- What quantifiers over the next level give back

-- Mathematical shape: a small type with a map from P through which every
-- map from P into a small type factors, up to logical equivalence.
record Small-Reflection {ℓ : Level} (P : Set (lsuc ℓ)) : Set (lsuc ℓ) where
  field
    shadow : Set ℓ
    unit : P → shadow
    elim : (ψ : Set ℓ) → (P → ψ) → shadow → ψ

module _ {ℓ : Level} (Q : Quantifiers (lsuc ℓ) ℓ) (P : Set (lsuc ℓ)) where

  -- The existential of the true predicate along the map to the point.
  quantified-shadow : Set ℓ
  quantified-shadow =
    Quantifiers.exists Q (λ (p : P) → lift ⋆) (λ (p : P) → Lift ℓ 𝟙)
      (lift ⋆)

  -- Weak resizing would also return from the shadow to P; quantifiers alone
  -- are not claimed to.
  quantifiers-give-small-reflections : Small-Reflection P
  quantifiers-give-small-reflections = record
    { shadow = quantified-shadow
    ; unit = λ p →
        pr₁
          ( Quantifiers.exists-adjoint Q (λ (p : P) → lift ⋆)
              (λ (p : P) → Lift ℓ 𝟙)
              (λ (u : Lift (lsuc ℓ) 𝟙) → quantified-shadow))
          (λ u s → s) p (lift ⋆)
    ; elim = λ ψ k →
        pr₂
          ( Quantifiers.exists-adjoint Q (λ (p : P) → lift ⋆)
              (λ (p : P) → Lift ℓ 𝟙) (λ (u : Lift (lsuc ℓ) 𝟙) → ψ))
          (λ p u → k p) (lift ⋆)
    }
