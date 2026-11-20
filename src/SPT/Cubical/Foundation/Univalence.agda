{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Univalence where

-- Univalence is a hypothesis, never assumed: at one pair of types
-- (`is-univalent-at`), at one level (`is-univalent`), or at every level
-- (`Univalence`). An equivalence is a map with contractible fibers
-- (`Equivalence`). Every isomorphism is one, through its half-adjoint
-- coherence (`isomorphisms-have-contractible-fibers`,
-- `isomorphism-to-equivalence`); conversely the centers of the fibers
-- invert an equivalence (`equivalence-to-isomorphism`). Transport along
-- an identification of types is an equivalence (`idtoeq`), and univalence
-- at A and B says that `idtoeq` has contractible fibers there.
--
-- Univalence at one pair turns every isomorphism of the pair into an
-- identification (`isotoid`, `idtoeq-isotoid`), along which transport is
-- the forward map and transport back the backward map
-- (`transport-isotoid`, `transport-isotoid-⁻¹`):
--
--   transport (λ X → X) (isotoid u E) a ＝ forward E a.
--
-- Two families with an isomorphism at every point are identified, under
-- extensionality for families and univalence at each pair of fibers
-- (`pointwise-isotoid`); its happly at a point is the identification there
-- (`happly-pointwise-isotoid`). Along it, a section and the identity of
-- the total space are carried by the forward maps
-- (`transport-pointwise-isotoid`, `retype-pointwise-isotoid`).
--
-- Univalence gives function extensionality, by Voevodsky's argument.
-- Under univalence at a pair, precomposition with an equivalence between
-- them is left-cancellable (`precomposition-is-left-cancellable`), since
-- the equivalence is transport along an identification. The diagonal of
-- a type Y into its path space (`Path-Space`, `diagonal`) is an
-- equivalence after which the two endpoint projections agree, so they
-- agree; hence maps into Y that agree at every point are identified
-- (`funext-into`), under univalence at Y and its path space only. Then
-- postcomposition with the first projection of a family of contractible
-- types is an isomorphism (`postcomposition-with-pr₁`), whose fiber over
-- the identity retracts onto the dependent functions, so these form a
-- contractible type (`Π-of-contractible-types-is-contractible`). Two
-- functions that agree at every point give two dependent functions into
-- based path spaces, identified in that contractible type
-- (`funext-from-univalence`, `univalence-gives-funext`):
--
--   is-univalent (ℓ ⊔ κ) → is-univalent ℓ → FunExt A B.
--
-- After TypeTopology (UF.Univalence: is-univalent, Univalence, idtoeq;
-- UF.UA-FunExt: naive-univalence-gives-funext, univalence-gives-funext';
-- UF.FunExt-from-Naive-FunExt: equiv-post-gives-funext'), restated over
-- SPT's identity with equivalences as maps with contractible fibers, and
-- Gambino, Kapulkin and Lumsdaine's notes on Voevodsky's proof. Left
-- cancellation of precomposition is read off transport here, so the
-- equivalence's own left cancellation is not used.

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Extensionality using (FunExt)
open import SPT.Cubical.Foundation.Contractible using
  (is-contractible; based-path-spaces-are-contractible)
open import SPT.Cubical.Foundation.Fibers using (fiber; has-contractible-fibers)
open import SPT.Cubical.Foundation.Happly using
  (happly; funext; happly-funext; transport-at)
open import SPT.Cubical.Foundation.Isomorphisms using
  (_≅_; forward; backward; backward-forward; forward-backward;
   transport-is-isomorphism)
open import SPT.Cubical.Foundation.HalfAdjoint using
  (coherent-forward-backward; half-adjoint-condition)

------------------------------------------------------------------------
-- Equivalences

-- A map with contractible fibers.
Equivalence : {ℓ κ : Level} → Set ℓ → Set κ → Set (ℓ ⊔ κ)
Equivalence A B = Σ (A → B) (λ f → has-contractible-fibers f)

module _ {ℓ κ : Level} {A : Set ℓ} {B : Set κ} where

  -- The fiber of the forward map over b is centered at the backward image
  -- of b; the half-adjoint coherence contracts it.
  isomorphisms-have-contractible-fibers : (E : A ≅ B) →
    has-contractible-fibers (forward E)
  isomorphisms-have-contractible-fibers E b =
    (backward E b , coherent-forward-backward E b) , contraction b
    where
    contraction : (b′ : B) (u : fiber (forward E) b′) →
      (backward E b′ , coherent-forward-backward E b′) ＝ u
    contraction .(forward E a) (a , refl) =
      let c = coherent-forward-backward E (forward E a)
      in to-Σ-＝ (backward-forward E a)
           (transport-fiber (forward E) (backward-forward E a) c
            ∙ (ap (λ q → q ⁻¹ ∙ c) (half-adjoint-condition E a)
               ∙ left-inverse c))

  isomorphism-to-equivalence : A ≅ B → Equivalence A B
  isomorphism-to-equivalence E =
    forward E , isomorphisms-have-contractible-fibers E

  -- The center of each fiber gives the inverse.
  equivalence-to-isomorphism : Equivalence A B → A ≅ B
  equivalence-to-isomorphism (f , c) = record
    { forward = f
    ; backward = λ b → pr₁ (pr₁ (c b))
    ; backward-forward = λ a → ap pr₁ (pr₂ (c (f a)) (a , refl))
    ; forward-backward = λ b → pr₂ (pr₁ (c b))
    }

------------------------------------------------------------------------
-- Univalence

module _ {ℓ : Level} (A B : Set ℓ) where

  -- Transport along an identification of types is an equivalence.
  idtoeq : A ＝ B → Equivalence A B
  idtoeq e =
    isomorphism-to-equivalence (transport-is-isomorphism (λ X → X) e)

  -- Univalence at A and B: every equivalence comes from an identification,
  -- uniquely up to identification.
  is-univalent-at : Set (lsuc ℓ)
  is-univalent-at = has-contractible-fibers idtoeq

-- Univalence at one level.
is-univalent : (ℓ : Level) → Set (lsuc ℓ)
is-univalent ℓ = (A B : Set ℓ) → is-univalent-at A B

-- Univalence at every level.
Univalence : Setω
Univalence = (ℓ : Level) → is-univalent ℓ

------------------------------------------------------------------------
-- Identifications from isomorphisms

module _ {ℓ : Level} {A B : Set ℓ} where

  -- The identification of an isomorphism: the center of its fiber.
  isotoid : is-univalent-at A B → A ≅ B → A ＝ B
  isotoid u E = pr₁ (pr₁ (u (isomorphism-to-equivalence E)))

  idtoeq-isotoid : (u : is-univalent-at A B) (E : A ≅ B) →
    idtoeq A B (isotoid u E) ＝ isomorphism-to-equivalence E
  idtoeq-isotoid u E = pr₂ (pr₁ (u (isomorphism-to-equivalence E)))

  -- Transport along it is the forward map.
  transport-isotoid : (u : is-univalent-at A B) (E : A ≅ B) (a : A) →
    transport (λ X → X) (isotoid u E) a ＝ forward E a
  transport-isotoid u E a = happly (ap pr₁ (idtoeq-isotoid u E)) a

  -- Transport back along it is the backward map.
  transport-isotoid-⁻¹ : (u : is-univalent-at A B) (E : A ≅ B) (b : B) →
    transport (λ X → X) (isotoid u E ⁻¹) b ＝ backward E b
  transport-isotoid-⁻¹ u E b =
    ap (transport (λ X → X) (isotoid u E ⁻¹))
      (forward-backward E b ⁻¹
       ∙ transport-isotoid u E (backward E b) ⁻¹)
    ∙ forth-and-back-transport (λ X → X) (isotoid u E) (backward E b)

------------------------------------------------------------------------
-- Families identified pointwise

-- The identity of a total space, transported along an identification of
-- its family, moves the second component along the identification at the
-- first; at refl both are the identity. Two families with an isomorphism
-- at every point are identified by extensionality applied to the
-- identifications of the isomorphisms, and along that identification a
-- section, and the identity of the total space, are carried by the
-- forward maps.

module _ {ℓ μ : Level} {X : Set μ} where

  transport-total-identity : {T₁ T₂ : X → Set ℓ} (e : T₁ ＝ T₂)
    (w : Σ X T₁) →
    transport (λ T → Σ X T₁ → Σ X T) e (λ v → v) w
      ＝ (pr₁ w , transport (λ Y → Y) (happly e (pr₁ w)) (pr₂ w))
  transport-total-identity refl w = refl

module _ {ℓ μ : Level} {X : Set μ} (T₁ T₂ : X → Set ℓ) where

  pointwise-isotoid : FunExt X (λ x → Set ℓ) →
    ((x : X) → is-univalent-at (T₁ x) (T₂ x)) →
    ((x : X) → T₁ x ≅ T₂ x) → T₁ ＝ T₂
  pointwise-isotoid extensionality u E =
    funext extensionality T₁ T₂ (λ x → isotoid (u x) (E x))

  -- At each point, happly of it is the identification of the fibers.
  happly-pointwise-isotoid : (extensionality : FunExt X (λ x → Set ℓ))
    (extensionality′ : (T : X → Set ℓ) →
      FunExt X (λ x → Σ (Set ℓ) (λ Y → T x ＝ Y)))
    (u : (x : X) → is-univalent-at (T₁ x) (T₂ x))
    (E : (x : X) → T₁ x ≅ T₂ x) (x : X) →
    happly (pointwise-isotoid extensionality u E) x ＝ isotoid (u x) (E x)
  happly-pointwise-isotoid extensionality extensionality′ u E x =
    happly
      (happly-funext extensionality extensionality′ T₁ T₂
        (λ y → isotoid (u y) (E y)))
      x

  -- A section, transported along it, is the forward maps applied.
  transport-pointwise-isotoid : (extensionality : FunExt X (λ x → Set ℓ))
    (extensionality′ : (T : X → Set ℓ) →
      FunExt X (λ x → Σ (Set ℓ) (λ Y → T x ＝ Y)))
    (u : (x : X) → is-univalent-at (T₁ x) (T₂ x))
    (E : (x : X) → T₁ x ≅ T₂ x) (t : (x : X) → T₁ x) (x : X) →
    transport (λ T → (y : X) → T y) (pointwise-isotoid extensionality u E)
      t x
      ＝ forward (E x) (t x)
  transport-pointwise-isotoid extensionality extensionality′ u E t x =
    transport-at (λ Y → Y) (pointwise-isotoid extensionality u E) t x
    ∙ (ap (λ e → transport (λ Y → Y) e (t x))
         (happly-pointwise-isotoid extensionality extensionality′ u E x)
       ∙ transport-isotoid (u x) (E x) (t x))

  -- The identity of the total space, transported along it, is the forward
  -- map in the fiber.
  retype-pointwise-isotoid : (extensionality : FunExt X (λ x → Set ℓ))
    (extensionality′ : (T : X → Set ℓ) →
      FunExt X (λ x → Σ (Set ℓ) (λ Y → T x ＝ Y)))
    (u : (x : X) → is-univalent-at (T₁ x) (T₂ x))
    (E : (x : X) → T₁ x ≅ T₂ x) (w : Σ X T₁) →
    transport (λ T → Σ X T₁ → Σ X T)
      (pointwise-isotoid extensionality u E) (λ v → v) w
      ＝ (pr₁ w , forward (E (pr₁ w)) (pr₂ w))
  retype-pointwise-isotoid extensionality extensionality′ u E w =
    transport-total-identity (pointwise-isotoid extensionality u E) w
    ∙ (ap (λ e → pr₁ w , transport (λ Y → Y) e (pr₂ w))
         (happly-pointwise-isotoid extensionality extensionality′ u E
           (pr₁ w))
       ∙ ap (λ b → pr₁ w , b)
           (transport-isotoid (u (pr₁ w)) (E (pr₁ w)) (pr₂ w)))

------------------------------------------------------------------------
-- Precomposition with an equivalence

module _ {ℓ μ : Level} {Z : Set μ} where

  -- Precomposition with transport along an identification of types is
  -- left-cancellable: at refl it is the identity.
  precomposition-with-transport-is-left-cancellable : {A B : Set ℓ}
    (p : A ＝ B) (g h : B → Z) →
    g ∘ transport (λ X → X) p ＝ h ∘ transport (λ X → X) p →
    g ＝ h
  precomposition-with-transport-is-left-cancellable refl g h e = e

module _ {ℓ μ : Level} (A B : Set ℓ) {Z : Set μ} where

  -- Under univalence at A and B an equivalence is transport along an
  -- identification, so precomposition with it is left-cancellable.
  precomposition-is-left-cancellable : is-univalent-at A B →
    (e : Equivalence A B) (g h : B → Z) →
    g ∘ pr₁ e ＝ h ∘ pr₁ e → g ＝ h
  precomposition-is-left-cancellable u e g h q =
    let p = pr₁ (pr₁ (u e))
        t = ap pr₁ (pr₂ (pr₁ (u e)))
    in precomposition-with-transport-is-left-cancellable p g h
         (transport (λ k → g ∘ k ＝ h ∘ k) (t ⁻¹) q)

------------------------------------------------------------------------
-- Function extensionality into one type

module _ {ℓ : Level} (Y : Set ℓ) where

  -- Pairs of points of Y with an identification between them.
  Path-Space : Set ℓ
  Path-Space = Σ Y (λ y₀ → Σ Y (λ y₁ → y₀ ＝ y₁))

  -- Every path is identified with the constant path at its source.
  paths-are-constant : (d : Path-Space) → (pr₁ d , pr₁ d , refl) ＝ d
  paths-are-constant (y₀ , .y₀ , refl) = refl

  -- The diagonal, inverse to the first endpoint.
  diagonal : Y ≅ Path-Space
  diagonal = record
    { forward = λ y → y , y , refl
    ; backward = pr₁
    ; backward-forward = λ y → refl
    ; forward-backward = paths-are-constant
    }

module _ {ℓ κ : Level} {X : Set κ} {Y : Set ℓ} where

  -- The two endpoint projections agree after the diagonal, so they agree;
  -- read at the paths of two maps, the maps agree.
  funext-into : is-univalent-at Y (Path-Space Y) → (f g : X → Y) →
    ((x : X) → f x ＝ g x) → f ＝ g
  funext-into u f g h =
    ap (λ π x → π (f x , g x , h x))
      (precomposition-is-left-cancellable Y (Path-Space Y) u
        (isomorphism-to-equivalence (diagonal Y))
        pr₁ (λ d → pr₁ (pr₂ d)) refl)

------------------------------------------------------------------------
-- Dependent function extensionality

module _ {ℓ κ : Level} {A : Set ℓ} (P : A → Set κ) where

  -- The first projection is an equivalence when every P x is contractible.
  pr₁-has-contractible-fibers : ((x : A) → is-contractible (P x)) →
    has-contractible-fibers (pr₁ {A = A} {B = P})
  pr₁-has-contractible-fibers c a =
    ((a , pr₁ (c a)) , refl) , contraction a
    where
    contraction : (b : A) (w : fiber (pr₁ {A = A} {B = P}) b) →
      ((b , pr₁ (c b)) , refl) ＝ w
    contraction .x ((x , p) , refl) =
      ap (λ v → (x , v) , refl) (pr₂ (c x) p)

  pr₁-isomorphism : ((x : A) → is-contractible (P x)) → Σ A P ≅ A
  pr₁-isomorphism c =
    equivalence-to-isomorphism (pr₁ , pr₁-has-contractible-fibers c)

  -- Postcomposition with the first projection, inverted by
  -- postcomposition with its inverse; extensionality into A and into Σ A P
  -- gives both laws.
  postcomposition-with-pr₁ : is-univalent-at A (Path-Space A) →
    is-univalent-at (Σ A P) (Path-Space (Σ A P)) →
    ((x : A) → is-contractible (P x)) → (A → Σ A P) ≅ (A → A)
  postcomposition-with-pr₁ u v c = record
    { forward = λ h → pr₁ ∘ h
    ; backward = λ k → backward (pr₁-isomorphism c) ∘ k
    ; backward-forward = λ h →
        funext-into v (backward (pr₁-isomorphism c) ∘ (pr₁ ∘ h)) h
          (λ a → backward-forward (pr₁-isomorphism c) (h a))
    ; forward-backward = λ k →
        funext-into u (pr₁ ∘ (backward (pr₁-isomorphism c) ∘ k)) k
          (λ a → forward-backward (pr₁-isomorphism c) (k a))
    }

  -- A section of the first projection gives a dependent function, by
  -- transport along the identification with the identity.
  section-to-function : (Σ (A → Σ A P) (λ h → pr₁ ∘ h ＝ id)) →
    (x : A) → P x
  section-to-function (h , q) x = transport P (happly q x) (pr₂ (h x))

  -- The fiber of postcomposition over the identity is contractible, and
  -- the dependent functions are its retract.
  Π-of-contractible-types-is-contractible :
    is-univalent-at A (Path-Space A) →
    is-univalent-at (Σ A P) (Path-Space (Σ A P)) →
    ((x : A) → is-contractible (P x)) → is-contractible ((x : A) → P x)
  Π-of-contractible-types-is-contractible u v c =
    let fibers = isomorphisms-have-contractible-fibers
                   (postcomposition-with-pr₁ u v c) id
    in section-to-function (pr₁ fibers) ,
       (λ φ → ap section-to-function
         (pr₂ fibers ((λ x → x , φ x) , refl)))

module _ {ℓ κ : Level} (A : Set ℓ) (B : A → Set κ) where

  -- Two functions that agree at every point give two dependent functions
  -- into based path spaces, identified in that contractible type.
  funext-from-univalence : is-univalent (ℓ ⊔ κ) → is-univalent ℓ →
    FunExt A B
  funext-from-univalence v u f g h =
    let P = λ x → Σ (B x) (λ y → f x ＝ y)
        c = Π-of-contractible-types-is-contractible P
              (u A (Path-Space A))
              (v (Σ A P) (Path-Space (Σ A P)))
              (λ x → based-path-spaces-are-contractible (f x))
    in ap (λ k x → pr₁ (k x))
         (pr₂ c (λ x → f x , refl) ⁻¹ ∙ pr₂ c (λ x → g x , h x))

-- Univalence at every level gives extensionality for every function type.
univalence-gives-funext : Univalence → {ℓ κ : Level} (A : Set ℓ)
  (B : A → Set κ) → FunExt A B
univalence-gives-funext ua {ℓ} {κ} A B =
  funext-from-univalence A B (ua (ℓ ⊔ κ)) (ua ℓ)
