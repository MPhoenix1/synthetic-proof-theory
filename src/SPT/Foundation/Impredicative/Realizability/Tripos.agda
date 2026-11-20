{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Impredicative.Realizability.Tripos where

-- The realizability tripos of a partial combinatory algebra over the base
-- of small types. A predicate on X assigns to each point a subset of the
-- carrier, a point of a presentation of the subsets
-- (`Subset-Presentation`), and φ entails ψ when one element sends every
-- realizer of φ x to a realizer of ψ x, uniformly in x (`Entailment`):
--
--   Entailment X φ ψ = Σ e. Π x a. a ∈ φ x → Σ b. e · a ≃ b × b ∈ ψ x.
--
-- The operations and their universal properties need no smallness of the
-- subsets: every predicate is its own subset one level up
-- (`predicates-are-subsets`). Only the generic predicate needs a power
-- presentation (`realizability-tripos`), which a classifier supplies
-- (`classifier-gives-realizability-tripos`). At the one-point algebra
-- entailment is inclusion at the point
-- (`one-point-entailment-is-inclusion`), and the generic predicate read at
-- the point is a classifier (`one-point-tripos-gives-classifier`).

open import SPT.Base
open import SPT.Foundation.Impredicative.Classification using (Classifier)
open import SPT.Foundation.Impredicative.Classifier using
  (Power-Presentation; classifier-gives-power-presentations)
open import SPT.Foundation.Impredicative.Realizability.CombinatoryAlgebra
  using
  ( Partial-Combinatory-Algebra; identity; identity-β; composite
  ; composite-β; second; first-after; first-after-β; second-after
  ; second-after-β; pairing; pairing-β; injection; injection-β; copairing
  ; copairing-left; copairing-right; curry; curry-β; uncurry; uncurry-β
  ; constant-after; constant-after-β)
open import SPT.Foundation.Impredicative.Tripos using
  (top; bottom; Exists; All; pullback-left; pullback-right)
open import SPT.Foundation.Impredicative.Tripos.Indexed using
  (Indexed-Tripos)
open import SPT.Foundation.LogicalEquivalence using (_⇔_)

------------------------------------------------------------------------
-- Presentations of the subsets of the carrier

-- A type of subsets of C, at level κ, retaining every predicate on C of
-- level ℓ up to pointwise logical equivalence. A power presentation is
-- one with κ = ℓ (`power-presentation-gives-subset-presentation`).
-- Without that smallness every predicate is its own subset
-- (`predicates-are-subsets`).

record Subset-Presentation {γ : Level} (C : Set γ) (ℓ κ : Level) :
  Set (γ ⊔ lsuc ℓ ⊔ lsuc κ) where
  field
    Subsets : Set κ
    member : Subsets → C → Set ℓ
    retain : (C → Set ℓ) → Subsets
    recover : (X : C → Set ℓ) (a : C) →
      (X a → member (retain X) a) × (member (retain X) a → X a)

power-presentation-gives-subset-presentation : {ℓ : Level} {C : Set ℓ} →
  Power-Presentation C → Subset-Presentation C ℓ ℓ
power-presentation-gives-subset-presentation power = record
  { Subsets = Power-Presentation.Subsets power
  ; member = Power-Presentation.member power
  ; retain = Power-Presentation.retain power
  ; recover = Power-Presentation.recover power
  }

predicates-are-subsets : {γ : Level} (C : Set γ) (ℓ : Level) →
  Subset-Presentation C ℓ (γ ⊔ lsuc ℓ)
predicates-are-subsets C ℓ = record
  { Subsets = C → Set ℓ
  ; member = λ S → S
  ; retain = λ X → X
  ; recover = λ X a → (λ x → x) , (λ x → x)
  }

------------------------------------------------------------------------
-- Entailment and the connectives

-- The predicates have level γ ⊔ ℓ, for an algebra of level γ: a realizer
-- of a meet or an implication quantifies over the carrier.

module _ {γ : Level} (ℓ : Level) {κ : Level}
  (A : Partial-Combinatory-Algebra γ)
  (power :
    Subset-Presentation (Partial-Combinatory-Algebra.Carrier A) (γ ⊔ ℓ) κ)
  where

  open Partial-Combinatory-Algebra A using (Carrier; apply; k)
  open Subset-Presentation power using (Subsets; member; retain; recover)

  ----------------------------------------------------------------------
  -- Realizers and entailment

  -- A subset retains a predicate on the carrier up to logical
  -- equivalence (`into-retained`, `out-of-retained`). An entailment is a
  -- realizer together with its action on realizers.

  into-retained : (P : Carrier → Set (γ ⊔ ℓ)) (a : Carrier) → P a →
    member (retain P) a
  into-retained P a = pr₁ (recover P a)

  out-of-retained : (P : Carrier → Set (γ ⊔ ℓ)) (a : Carrier) →
    member (retain P) a → P a
  out-of-retained P a = pr₂ (recover P a)

  Realizes : (X : Set (γ ⊔ ℓ)) → (X → Subsets) → (X → Subsets) →
    Carrier → Set (γ ⊔ ℓ)
  Realizes X φ ψ e = (x : X) (a : Carrier) → member (φ x) a →
    Σ Carrier (λ b → apply e a b × member (ψ x) b)

  Entailment : (X : Set (γ ⊔ ℓ)) → (X → Subsets) → (X → Subsets) →
    Set (γ ⊔ ℓ)
  Entailment X φ ψ = Σ Carrier (Realizes X φ ψ)

  -- Pointwise inclusion of subsets is realized by the identity.
  by-identity : (X : Set (γ ⊔ ℓ)) (φ ψ : X → Subsets) →
    ((x : X) (a : Carrier) → member (φ x) a → member (ψ x) a) →
    Entailment X φ ψ
  by-identity X φ ψ h =
    identity A , (λ x a m → a , identity-β A a , h x a m)

  compose-entailments : (X : Set (γ ⊔ ℓ)) (φ ψ χ : X → Subsets) →
    Entailment X φ ψ → Entailment X ψ χ → Entailment X φ χ
  compose-entailments X φ ψ χ (e₁ , r₁) (e₂ , r₂) =
    e₂ ∘⟨ A ⟩ e₁ ,
    ( λ x a m →
        let (b , p , mb) = r₁ x a m
            (c , q , mc) = r₂ x b mb
        in c , composite-β A p q , mc)

  -- The same realizer restricts along a map of points.
  reindex-entailment : (X Y : Set (γ ⊔ ℓ)) (f : X → Y) (φ ψ : Y → Subsets) →
    Entailment Y φ ψ → Entailment X (λ x → φ (f x)) (λ x → ψ (f x))
  reindex-entailment X Y f φ ψ e = pr₁ e , (λ x a m → pr₂ e (f x) a m)

  ----------------------------------------------------------------------
  -- Subsets and predicates

  -- A realizer of a meet is a pair, read by k and second; a realizer of
  -- a join is a pair whose first component is the tag k or second; a
  -- realizer of an implication sends realizers to realizers. The
  -- realizers of an existential at y are the realizers of φ x for some x
  -- over y, Exists of membership; a realizer of a universal applies to
  -- every argument with a value in each fiber, All of the values. The top
  -- and bottom predicates retain top and bottom.

  Projections : Subsets → Subsets → Carrier → Set (γ ⊔ ℓ)
  Projections S T a =
    Σ Carrier (λ b → apply a k b × member S b) ×
    Σ Carrier (λ c′ → apply a (second A) c′ × member T c′)

  Tagged : Subsets → Subsets → Carrier → Set (γ ⊔ ℓ)
  Tagged S T a =
    Σ Carrier (λ c′ → apply a k k × apply a (second A) c′ × member S c′) ⊎
    Σ Carrier (λ c′ →
      apply a k (second A) × apply a (second A) c′ × member T c′)

  Implies : Subsets → Subsets → Carrier → Set (γ ⊔ ℓ)
  Implies S T e = (b : Carrier) → member S b →
    Σ Carrier (λ c′ → apply e b c′ × member T c′)

  -- Mathematical shape: Witnessed f φ y a = Exists f (λ x → a ∈ φ x) y.
  Witnessed : {X Y : Set (γ ⊔ ℓ)} → (X → Y) → (X → Subsets) → Y →
    Carrier → Set (γ ⊔ ℓ)
  Witnessed f φ y a = Exists f (λ x → member (φ x) a) y

  -- Mathematical shape: Uniform f φ y g = All f (λ x → Π b. g · b ∈ φ x) y.
  Uniform : {X Y : Set (γ ⊔ ℓ)} → (X → Y) → (X → Subsets) → Y →
    Carrier → Set (γ ⊔ ℓ)
  Uniform f φ y g =
    All f
      ( λ x → (b : Carrier) →
          Σ Carrier (λ c′ → apply g b c′ × member (φ x) c′))
      y

  reindex-predicate : {X Y : Set (γ ⊔ ℓ)} → (X → Y) → (Y → Subsets) →
    X → Subsets
  reindex-predicate f φ x = φ (f x)

  top-predicate : {X : Set (γ ⊔ ℓ)} → X → Subsets
  top-predicate x = retain (top (γ ⊔ ℓ))

  bottom-predicate : {X : Set (γ ⊔ ℓ)} → X → Subsets
  bottom-predicate x = retain (bottom (γ ⊔ ℓ))

  meet-predicate : {X : Set (γ ⊔ ℓ)} → (X → Subsets) → (X → Subsets) →
    X → Subsets
  meet-predicate φ ψ x = retain (Projections (φ x) (ψ x))

  join-predicate : {X : Set (γ ⊔ ℓ)} → (X → Subsets) → (X → Subsets) →
    X → Subsets
  join-predicate φ ψ x = retain (Tagged (φ x) (ψ x))

  implication-predicate : {X : Set (γ ⊔ ℓ)} → (X → Subsets) →
    (X → Subsets) → X → Subsets
  implication-predicate φ ψ x = retain (Implies (φ x) (ψ x))

  exists-predicate : {X Y : Set (γ ⊔ ℓ)} → (X → Y) → (X → Subsets) →
    Y → Subsets
  exists-predicate f φ y = retain (Witnessed f φ y)

  all-predicate : {X Y : Set (γ ⊔ ℓ)} → (X → Y) → (X → Subsets) →
    Y → Subsets
  all-predicate f φ y = retain (Uniform f φ y)

  ----------------------------------------------------------------------
  -- Universal properties

  -- Each direction is one combinator; its law turns the realizers of the
  -- premises into a realizer of the conclusion.

  meet-forward : (X : Set (γ ⊔ ℓ)) (χ φ ψ : X → Subsets) →
    Entailment X χ (meet-predicate φ ψ) → Entailment X χ φ × Entailment X χ ψ
  meet-forward X χ φ ψ (e , r) =
    ( first-after A e ,
      ( λ x a m →
          let (p , ep , mp) = r x a m
              ((b , pb , mb) , rest) =
                out-of-retained (Projections (φ x) (ψ x)) p mp
          in b , first-after-β A ep pb , mb)) ,
    ( second-after A e ,
      ( λ x a m →
          let (p , ep , mp) = r x a m
              (rest , (c , pc , mc)) =
                out-of-retained (Projections (φ x) (ψ x)) p mp
          in c , second-after-β A ep pc , mc))

  meet-backward : (X : Set (γ ⊔ ℓ)) (χ φ ψ : X → Subsets) →
    Entailment X χ φ × Entailment X χ ψ → Entailment X χ (meet-predicate φ ψ)
  meet-backward X χ φ ψ ((e₁ , r₁) , (e₂ , r₂)) =
    ⟨ e₁ , e₂ ⟩⟨ A ⟩ ,
    ( λ x a m →
        let (b , p₁ , mb) = r₁ x a m
            (c , p₂ , mc) = r₂ x a m
            (p , pa , pk , ps) = pairing-β A p₁ p₂
        in p ,
           pa ,
           into-retained (Projections (φ x) (ψ x)) p
             ((b , pk , mb) , (c , ps , mc)))

  join-forward : (X : Set (γ ⊔ ℓ)) (φ ψ χ : X → Subsets) →
    Entailment X (join-predicate φ ψ) χ → Entailment X φ χ × Entailment X ψ χ
  join-forward X φ ψ χ (e , r) =
    ( e ∘⟨ A ⟩ injection A k ,
      ( λ x a m →
          let (p , ia , pk , ps) = injection-β A k a
              (c , ec , mc) =
                r x p
                  ( into-retained (Tagged (φ x) (ψ x)) p
                      (inl (a , pk , ps , m)))
          in c , composite-β A ia ec , mc)) ,
    ( e ∘⟨ A ⟩ injection A (second A) ,
      ( λ x a m →
          let (p , ia , pk , ps) = injection-β A (second A) a
              (c , ec , mc) =
                r x p
                  ( into-retained (Tagged (φ x) (ψ x)) p
                      (inr (a , pk , ps , m)))
          in c , composite-β A ia ec , mc))

  join-backward : (X : Set (γ ⊔ ℓ)) (φ ψ χ : X → Subsets) →
    Entailment X φ χ × Entailment X ψ χ → Entailment X (join-predicate φ ψ) χ
  join-backward X φ ψ χ ((e₁ , r₁) , (e₂ , r₂)) =
    [ e₁ , e₂ ]⟨ A ⟩ ,
    ( λ x p m →
        cases
          ( λ on-left →
              let (c , pk , ps , mc) = on-left
                  (r , er , mr) = r₁ x c mc
              in r , copairing-left A pk ps er , mr)
          ( λ on-right →
              let (c , pk , ps , mc) = on-right
                  (r , er , mr) = r₂ x c mc
              in r , copairing-right A pk ps er , mr)
          ( out-of-retained (Tagged (φ x) (ψ x)) p m))

  implication-forward : (X : Set (γ ⊔ ℓ)) (χ φ ψ : X → Subsets) →
    Entailment X (meet-predicate χ φ) ψ →
    Entailment X χ (implication-predicate φ ψ)
  implication-forward X χ φ ψ (e , r) =
    curry A e ,
    ( λ x a m →
        let (g , ag , rest) = curry-β A e a
        in g ,
           ag ,
           into-retained (Implies (φ x) (ψ x)) g
             ( λ b mb →
                 let (p , (pk , ps) , applies) = rest b
                     (c , ec , mc) =
                       r x p
                         ( into-retained (Projections (χ x) (φ x)) p
                             ((a , pk , m) , (b , ps , mb)))
                 in c , applies c ec , mc))

  implication-backward : (X : Set (γ ⊔ ℓ)) (χ φ ψ : X → Subsets) →
    Entailment X χ (implication-predicate φ ψ) →
    Entailment X (meet-predicate χ φ) ψ
  implication-backward X χ φ ψ (e , r) =
    uncurry A e ,
    ( λ x p m →
        let ((a , pk , ma) , (b , ps , mb)) =
              out-of-retained (Projections (χ x) (φ x)) p m
            (g , eg , mg) = r x a ma
            (c , gc , mc) = out-of-retained (Implies (φ x) (ψ x)) g mg b mb
        in c , uncurry-β A pk ps eg gc , mc)

  exists-forward : (X Y : Set (γ ⊔ ℓ)) (f : X → Y) (φ : X → Subsets)
    (ψ : Y → Subsets) → Entailment Y (exists-predicate f φ) ψ →
    Entailment X φ (reindex-predicate f ψ)
  exists-forward X Y f φ ψ (e , r) =
    e ,
    ( λ x a m →
        r (f x) a (into-retained (Witnessed f φ (f x)) a (x , refl , m)))

  exists-backward : (X Y : Set (γ ⊔ ℓ)) (f : X → Y) (φ : X → Subsets)
    (ψ : Y → Subsets) → Entailment X φ (reindex-predicate f ψ) →
    Entailment Y (exists-predicate f φ) ψ
  exists-backward X Y f φ ψ (e , r) =
    e ,
    ( λ y a m →
        let (x , moved , mx) = out-of-retained (Witnessed f φ y) a m
            (b , eb , mb) = r x a mx
        in b , eb , transport (λ y′ → member (ψ y′) b) moved mb)

  all-forward : (X Y : Set (γ ⊔ ℓ)) (f : X → Y) (φ : X → Subsets)
    (ψ : Y → Subsets) → Entailment X (reindex-predicate f ψ) φ →
    Entailment Y ψ (all-predicate f φ)
  all-forward X Y f φ ψ (e , r) =
    constant-after A e ,
    ( λ y a m →
        let (g , ag , gives) = constant-after-β A e a
        in g ,
           ag ,
           into-retained (Uniform f φ y) g
             ( λ x moved b →
                 let (c , ec , mc) =
                       r x a (transport (λ y′ → member (ψ y′) a) (moved ⁻¹) m)
                 in c , gives b c ec , mc))

  all-backward : (X Y : Set (γ ⊔ ℓ)) (f : X → Y) (φ : X → Subsets)
    (ψ : Y → Subsets) → Entailment Y ψ (all-predicate f φ) →
    Entailment X (reindex-predicate f ψ) φ
  all-backward X Y f φ ψ (e , r) =
    first-after A e ,
    ( λ x a m →
        let (g , eg , mg) = r (f x) a m
            (c , gk , mc) = out-of-retained (Uniform f φ (f x)) g mg x refl k
        in c , first-after-β A eg gk , mc)

  ----------------------------------------------------------------------
  -- Beck–Chevalley

  -- Along a canonical pullback both sides have the same realizers; the
  -- identity realizes both directions.

  exists-beck-chevalley : (X Y Z : Set (γ ⊔ ℓ)) (f : X → Y) (g : Z → Y)
    (φ : X → Subsets) →
    Entailment Z (reindex-predicate g (exists-predicate f φ))
      (exists-predicate (pullback-right f g)
        (reindex-predicate (pullback-left f g) φ)) ×
    Entailment Z
      (exists-predicate (pullback-right f g)
        (reindex-predicate (pullback-left f g) φ))
      (reindex-predicate g (exists-predicate f φ))
  exists-beck-chevalley X Y Z f g φ =
    by-identity Z
      ( reindex-predicate g (exists-predicate f φ))
      ( exists-predicate (pullback-right f g)
          ( reindex-predicate (pullback-left f g) φ))
      ( λ z a m →
          let (x , moved , mx) = out-of-retained (Witnessed f φ (g z)) a m
          in into-retained
               ( Witnessed (pullback-right f g)
                   ( reindex-predicate (pullback-left f g) φ) z)
               a
               (((x , z) , moved) , refl , mx)) ,
    by-identity Z
      ( exists-predicate (pullback-right f g)
          ( reindex-predicate (pullback-left f g) φ))
      ( reindex-predicate g (exists-predicate f φ))
      ( λ z a m →
          let (((x , z′) , moved) , shifted , mx) =
                out-of-retained
                  ( Witnessed (pullback-right f g)
                      ( reindex-predicate (pullback-left f g) φ) z)
                  a
                  m
          in into-retained (Witnessed f φ (g z)) a
               (x , (moved ∙ ap g shifted) , mx))

  all-beck-chevalley : (X Y Z : Set (γ ⊔ ℓ)) (f : X → Y) (g : Z → Y)
    (φ : X → Subsets) →
    Entailment Z (reindex-predicate g (all-predicate f φ))
      (all-predicate (pullback-right f g)
        (reindex-predicate (pullback-left f g) φ)) ×
    Entailment Z
      (all-predicate (pullback-right f g)
        (reindex-predicate (pullback-left f g) φ))
      (reindex-predicate g (all-predicate f φ))
  all-beck-chevalley X Y Z f g φ =
    by-identity Z
      ( reindex-predicate g (all-predicate f φ))
      ( all-predicate (pullback-right f g)
          ( reindex-predicate (pullback-left f g) φ))
      ( λ z a m →
          into-retained
            ( Uniform (pullback-right f g)
                ( reindex-predicate (pullback-left f g) φ) z)
            a
            ( λ w shifted b →
                out-of-retained (Uniform f φ (g z)) a m
                  ( pullback-left f g w)
                  ( pr₂ w ∙ ap g shifted)
                  b)) ,
    by-identity Z
      ( all-predicate (pullback-right f g)
          ( reindex-predicate (pullback-left f g) φ))
      ( reindex-predicate g (all-predicate f φ))
      ( λ z a m →
          into-retained (Uniform f φ (g z)) a
            ( λ x moved b →
                out-of-retained
                  ( Uniform (pullback-right f g)
                      ( reindex-predicate (pullback-left f g) φ) z)
                  a
                  m
                  ((x , z) , moved)
                  refl
                  b))

------------------------------------------------------------------------
-- The realizability tripos

-- Reindexing is precomposition, so it commutes with every operation by
-- computation. The generic predicate is the identity on subsets, which
-- have to be small: the presentation is at the level of the carrier.

module _ {ℓ : Level} (A : Partial-Combinatory-Algebra ℓ)
  (power : Subset-Presentation (Partial-Combinatory-Algebra.Carrier A) ℓ ℓ)
  where

  open Subset-Presentation power using (Subsets)

  realizability-tripos : Indexed-Tripos ℓ ℓ ℓ
  realizability-tripos = record
    { Predicate = λ X → X → Subsets
    ; entails = λ {X} φ ψ → Entailment ℓ A power X φ ψ
    ; entails-refl = λ {X} φ → by-identity ℓ A power X φ φ (λ x a m → m)
    ; entails-trans = λ {X} φ ψ χ → compose-entailments ℓ A power X φ ψ χ
    ; reindex-along = reindex-predicate ℓ A power
    ; reindex-monotone = λ {X} {Y} f φ ψ e →
        reindex-entailment ℓ A power X Y f φ ψ e
    ; reindex-identity = λ {X} φ →
        by-identity ℓ A power X φ φ (λ x a m → m) ,
        by-identity ℓ A power X φ φ (λ x a m → m)
    ; reindex-compose = λ {X} {Y} {Z} f g φ →
        by-identity ℓ A power X
          ( reindex-predicate ℓ A power (λ x → g (f x)) φ)
          ( reindex-predicate ℓ A power f (reindex-predicate ℓ A power g φ))
          ( λ x a m → m) ,
        by-identity ℓ A power X
          ( reindex-predicate ℓ A power f (reindex-predicate ℓ A power g φ))
          ( reindex-predicate ℓ A power (λ x → g (f x)) φ)
          ( λ x a m → m)
    ; truth = top-predicate ℓ A power
    ; falsity = bottom-predicate ℓ A power
    ; meet = meet-predicate ℓ A power
    ; join = join-predicate ℓ A power
    ; implication = implication-predicate ℓ A power
    ; truth-intro = λ {X} φ →
        by-identity ℓ A power X φ (top-predicate ℓ A power)
          ( λ x a m → into-retained ℓ A power (top ℓ) a (lift ⋆))
    ; falsity-elim = λ {X} φ →
        by-identity ℓ A power X (bottom-predicate ℓ A power) φ
          ( λ x a m →
              𝟘-elim (lower (out-of-retained ℓ A power (bottom ℓ) a m)))
    ; meet-adjoint = λ {X} χ φ ψ →
        meet-forward ℓ A power X χ φ ψ , meet-backward ℓ A power X χ φ ψ
    ; join-adjoint = λ {X} φ ψ χ →
        join-forward ℓ A power X φ ψ χ , join-backward ℓ A power X φ ψ χ
    ; implication-adjoint = λ {X} χ φ ψ →
        implication-forward ℓ A power X χ φ ψ ,
        implication-backward ℓ A power X χ φ ψ
    ; reindex-truth = λ {X} {Y} f →
        by-identity ℓ A power X (top-predicate ℓ A power)
          ( top-predicate ℓ A power) (λ x a m → m) ,
        by-identity ℓ A power X (top-predicate ℓ A power)
          ( top-predicate ℓ A power) (λ x a m → m)
    ; reindex-falsity = λ {X} {Y} f →
        by-identity ℓ A power X (bottom-predicate ℓ A power)
          ( bottom-predicate ℓ A power) (λ x a m → m) ,
        by-identity ℓ A power X (bottom-predicate ℓ A power)
          ( bottom-predicate ℓ A power) (λ x a m → m)
    ; reindex-meet = λ {X} {Y} f φ ψ →
        by-identity ℓ A power X
          ( reindex-predicate ℓ A power f (meet-predicate ℓ A power φ ψ))
          ( meet-predicate ℓ A power (reindex-predicate ℓ A power f φ)
              ( reindex-predicate ℓ A power f ψ))
          ( λ x a m → m) ,
        by-identity ℓ A power X
          ( meet-predicate ℓ A power (reindex-predicate ℓ A power f φ)
              ( reindex-predicate ℓ A power f ψ))
          ( reindex-predicate ℓ A power f (meet-predicate ℓ A power φ ψ))
          ( λ x a m → m)
    ; reindex-join = λ {X} {Y} f φ ψ →
        by-identity ℓ A power X
          ( reindex-predicate ℓ A power f (join-predicate ℓ A power φ ψ))
          ( join-predicate ℓ A power (reindex-predicate ℓ A power f φ)
              ( reindex-predicate ℓ A power f ψ))
          ( λ x a m → m) ,
        by-identity ℓ A power X
          ( join-predicate ℓ A power (reindex-predicate ℓ A power f φ)
              ( reindex-predicate ℓ A power f ψ))
          ( reindex-predicate ℓ A power f (join-predicate ℓ A power φ ψ))
          ( λ x a m → m)
    ; reindex-implication = λ {X} {Y} f φ ψ →
        by-identity ℓ A power X
          ( reindex-predicate ℓ A power f
              ( implication-predicate ℓ A power φ ψ))
          ( implication-predicate ℓ A power
              ( reindex-predicate ℓ A power f φ)
              ( reindex-predicate ℓ A power f ψ))
          ( λ x a m → m) ,
        by-identity ℓ A power X
          ( implication-predicate ℓ A power
              ( reindex-predicate ℓ A power f φ)
              ( reindex-predicate ℓ A power f ψ))
          ( reindex-predicate ℓ A power f
              ( implication-predicate ℓ A power φ ψ))
          ( λ x a m → m)
    ; exists = exists-predicate ℓ A power
    ; all = all-predicate ℓ A power
    ; exists-adjoint = λ {X} {Y} f φ ψ →
        exists-forward ℓ A power X Y f φ ψ ,
        exists-backward ℓ A power X Y f φ ψ
    ; all-adjoint = λ {X} {Y} f φ ψ →
        all-forward ℓ A power X Y f φ ψ , all-backward ℓ A power X Y f φ ψ
    ; exists-beck-chevalley = λ {X} {Y} {Z} f g φ →
        exists-beck-chevalley ℓ A power X Y Z f g φ
    ; all-beck-chevalley = λ {X} {Y} {Z} f g φ →
        all-beck-chevalley ℓ A power X Y Z f g φ
    ; proxies = Subsets
    ; proxy = λ S → S
    ; classify = λ X φ →
        φ ,
        by-identity ℓ A power X φ φ (λ x a m → m) ,
        by-identity ℓ A power X φ φ (λ x a m → m)
    }

------------------------------------------------------------------------
-- From a classifier

-- A classifier gives every small type a power presentation, in
-- particular the carrier of any partial combinatory algebra.

classifier-gives-realizability-tripos : {ℓ : Level} →
  Classifier (λ (X : Set ℓ) → X) → Partial-Combinatory-Algebra ℓ →
  Indexed-Tripos ℓ ℓ ℓ
classifier-gives-realizability-tripos C A =
  realizability-tripos A
    ( power-presentation-gives-subset-presentation
        ( classifier-gives-power-presentations C
            (Partial-Combinatory-Algebra.Carrier A)))

------------------------------------------------------------------------
-- The one-point algebra

-- Every application is defined. A realizer then carries no information,
-- so entailment is inclusion of the subsets read at the point, and the
-- generic predicate read at the point classifies every small type.

one-point : (ℓ : Level) → Partial-Combinatory-Algebra ℓ
one-point ℓ = record
  { Carrier = Lift ℓ 𝟙
  ; apply = λ a b c → Lift ℓ 𝟙
  ; functional = λ p q → refl
  ; k = lift ⋆
  ; s = lift ⋆
  ; k-defined = λ a → lift ⋆ , lift ⋆
  ; k-law = λ p → lift ⋆
  ; s-defined = λ a → lift ⋆ , lift ⋆
  ; s-defined₂ = λ b p → lift ⋆ , lift ⋆
  ; s-law = λ p q u v w → lift ⋆
  ; s-law-converse = λ p q w → lift ⋆ , lift ⋆ , lift ⋆ , lift ⋆ , lift ⋆
  }

one-point-entailment-is-inclusion : {ℓ : Level}
  (power : Power-Presentation (Lift ℓ 𝟙)) (X : Set ℓ)
  (φ ψ : X → Power-Presentation.Subsets power) →
  Entailment ℓ (one-point ℓ)
    (power-presentation-gives-subset-presentation power) X φ ψ ⇔
  ( (x : X) → Power-Presentation.member power (φ x) (lift ⋆) →
    Power-Presentation.member power (ψ x) (lift ⋆))
one-point-entailment-is-inclusion power X φ ψ =
  (λ entailment x m → pr₂ (pr₂ (pr₂ entailment x (lift ⋆) m))) ,
  (λ h → lift ⋆ , (λ x a m → lift ⋆ , lift ⋆ , h x m))

one-point-tripos-gives-classifier : {ℓ : Level} →
  Power-Presentation (Lift ℓ 𝟙) → Classifier (λ (X : Set ℓ) → X)
one-point-tripos-gives-classifier {ℓ} power = record
  { proxies =
      Indexed-Tripos.proxies
        ( realizability-tripos (one-point ℓ)
            (power-presentation-gives-subset-presentation power))
  ; proxy = λ S →
      Power-Presentation.member power
        ( Indexed-Tripos.proxy
            ( realizability-tripos (one-point ℓ)
                (power-presentation-gives-subset-presentation power))
            S)
        (lift ⋆)
  ; classify = λ Y →
      let (χ , to , from) =
            Indexed-Tripos.classify
              ( realizability-tripos (one-point ℓ)
                  (power-presentation-gives-subset-presentation power))
              ( Lift ℓ 𝟙)
              ( λ (t : Lift ℓ 𝟙) →
                  Power-Presentation.retain power (λ (u : Lift ℓ 𝟙) → Y))
      in χ (lift ⋆) ,
         ( λ y →
             pr₁
               ( one-point-entailment-is-inclusion power (Lift ℓ 𝟙)
                   ( λ (t : Lift ℓ 𝟙) →
                       Power-Presentation.retain power
                         (λ (u : Lift ℓ 𝟙) → Y))
                   χ)
               to
               (lift ⋆)
               ( pr₁
                   ( Power-Presentation.recover power
                       (λ (u : Lift ℓ 𝟙) → Y) (lift ⋆))
                   y)) ,
         ( λ m →
             pr₂
               ( Power-Presentation.recover power
                   (λ (u : Lift ℓ 𝟙) → Y) (lift ⋆))
               ( pr₁
                   ( one-point-entailment-is-inclusion power (Lift ℓ 𝟙) χ
                       ( λ (t : Lift ℓ 𝟙) →
                           Power-Presentation.retain power
                             (λ (u : Lift ℓ 𝟙) → Y)))
                   from
                   (lift ⋆)
                   m))
  }
