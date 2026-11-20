{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.HalfAdjoint where

-- The half-adjoint condition of an isomorphism. For `E : A ≅ B` with
-- forward map `f`, backward map `g`, backward-forward law `η` and
-- forward-backward law `ε`, the forward-backward law adjusted by
-- (`coherent-forward-backward`)
--
--   ε′ b = ε (f (g b)) ⁻¹ ∙ (ap f (η (g b)) ∙ ε b)
--
-- makes the triangle commute with `η` (`half-adjoint-condition`):
--
--   ap f (η a) ＝ ε′ (f a).
--
-- Applied to the inverse isomorphism (`≅-sym E`), it adjusts the
-- backward-forward law instead, against the forward-backward law. So every
-- isomorphism, a quasi-inverse, carries the coherence of a half-adjoint
-- equivalence, with no further hypothesis.
--
-- So an isomorphism acts on identifications by an isomorphism
-- (`ap-is-isomorphism`): the backward map conjugates by `η`,
--
--   q ↦ η a ⁻¹ ∙ (ap g q ∙ η a′),
--
-- and the triangle gives the forward-backward law.
--
-- And dependent pairs over an isomorphism of their indices are isomorphic,
-- given an isomorphism of each fiber with the fiber over its image
-- (`Σ-bicong`): the backward map reads the second component along `ε′`, and
-- the triangle turns `ε′` back into `ap f η`, which path induction undoes.
--
--   ((a : A) → C a ≅ D (f a)) → Σ A C ≅ Σ B D.
--
-- Dependent functions over it are isomorphic too, under extensionality for
-- both function types, passed explicitly (`Π-bicong`): the forward map
-- evaluates at the backward image and carries the value along `ε′`, and the
-- triangle and path induction give its pointwise inverse laws
-- (`Π-bicong-backward-forward`, `Π-bicong-forward-backward`).
--
--   ((a : A) → C a ≅ D (f a)) → ((a : A) → C a) ≅ ((b : B) → D b).
--
-- After TypeTopology (UF.Equiv: half-adjoint-condition, qinvs-are-haes;
-- UF.EquivalenceExamples: Σ-bicong, Π-bicong), restated over SPT's
-- isomorphisms, and the HoTT book, Theorem 2.11.1.

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Isomorphisms using
  (_≅_; forward; backward; backward-forward; forward-backward)
open import SPT.Cubical.Foundation.Extensionality using (FunExt)

------------------------------------------------------------------------
-- The adjusted law and the triangle

module _ {ℓ κ : Level} {A : Set ℓ} {B : Set κ} where

  coherent-forward-backward : (E : A ≅ B) (b : B) →
    forward E (backward E b) ＝ b
  coherent-forward-backward E b =
    forward-backward E (forward E (backward E b)) ⁻¹
      ∙ (ap (forward E) (backward-forward E (backward E b))
        ∙ forward-backward E b)

  half-adjoint-condition : (E : A ≅ B) (a : A) →
    ap (forward E) (backward-forward E a)
      ＝ coherent-forward-backward E (forward E a)
  half-adjoint-condition E a =
    let f = forward E
        g = backward E
        η = backward-forward E
        ε = forward-backward E
        c = ε (f (g (f a)))
        -- η is natural with respect to g ∘ f.
        twice : η (g (f a)) ＝ ap g (ap f (η a))
        twice = identity-homotopies-are-natural (g ∘ f) η a
          ∙ ap-∘ f g (η a)
        -- ε is natural along ap f (η a).
        square : ap f (η (g (f a))) ∙ ε (f a) ＝ c ∙ ap f (η a)
        square =
          ap f (η (g (f a))) ∙ ε (f a)
            ＝⟨ ap (λ q → ap f q ∙ ε (f a)) twice ⟩
          ap f (ap g (ap f (η a))) ∙ ε (f a)
            ＝⟨ ap (λ q → q ∙ ε (f a)) (ap-∘ g f (ap f (η a)) ⁻¹) ⟩
          ap (f ∘ g) (ap f (η a)) ∙ ε (f a)
            ＝⟨ homotopies-are-natural (f ∘ g) id ε (ap f (η a)) ⁻¹ ⟩
          c ∙ ap id (ap f (η a))
            ＝⟨ ap (λ q → c ∙ q) (ap-id (ap f (η a))) ⟩
          c ∙ ap f (η a) ∎
    in
    ap f (η a)
      ＝⟨ ap (λ q → q ∙ ap f (η a)) (left-inverse c ⁻¹) ⟩
    (c ⁻¹ ∙ c) ∙ ap f (η a)
      ＝⟨ ∙assoc (c ⁻¹) c (ap f (η a)) ⟩
    c ⁻¹ ∙ (c ∙ ap f (η a))
      ＝⟨ ap (λ q → c ⁻¹ ∙ q) (square ⁻¹) ⟩
    c ⁻¹ ∙ (ap f (η (g (f a))) ∙ ε (f a)) ∎

------------------------------------------------------------------------
-- The action on identifications

-- Along an identification p, the backward map undoes the action of the
-- forward one, by path induction. In the other direction the action of
-- `η` is replaced by the adjusted law through the triangle, and the
-- adjusted law, conjugating the action of `f ∘ g`, gives the
-- identification back, by path induction again.

module _ {ℓ κ : Level} {A : Set ℓ} {B : Set κ} where

  private
    backward-forward-ap : (E : A ≅ B) (a a′ : A) (p : a ＝ a′) →
      backward-forward E a ⁻¹
        ∙ (ap (backward E) (ap (forward E) p) ∙ backward-forward E a′)
        ＝ p
    backward-forward-ap E a a′ refl = left-inverse (backward-forward E a)

    conjugate : (E : A ≅ B) (b b′ : B) (q : b ＝ b′) →
      coherent-forward-backward E b ⁻¹
        ∙ ( ap (forward E ∘ backward E) q
            ∙ coherent-forward-backward E b′)
        ＝ q
    conjugate E b b′ refl = left-inverse (coherent-forward-backward E b)

    forward-backward-ap : (E : A ≅ B) (a a′ : A)
      (q : forward E a ＝ forward E a′) →
      ap (forward E)
        ( backward-forward E a ⁻¹
            ∙ (ap (backward E) q ∙ backward-forward E a′))
        ＝ q
    forward-backward-ap E a a′ q =
      let f = forward E
          g = backward E
          η = backward-forward E
          ε = coherent-forward-backward E
      in
      ap f (η a ⁻¹ ∙ (ap g q ∙ η a′))
        ＝⟨ ap-∙ f (η a ⁻¹) (ap g q ∙ η a′) ⟩
      ap f (η a ⁻¹) ∙ ap f (ap g q ∙ η a′)
        ＝⟨ ap (λ r → ap f (η a ⁻¹) ∙ r) (ap-∙ f (ap g q) (η a′)) ⟩
      ap f (η a ⁻¹) ∙ (ap f (ap g q) ∙ ap f (η a′))
        ＝⟨ ap (λ r → r ∙ (ap f (ap g q) ∙ ap f (η a′))) (ap-⁻¹ f (η a)) ⟩
      ap f (η a) ⁻¹ ∙ (ap f (ap g q) ∙ ap f (η a′))
        ＝⟨ ap₂ (λ u v → u ⁻¹ ∙ (ap f (ap g q) ∙ v))
              (half-adjoint-condition E a) (half-adjoint-condition E a′) ⟩
      ε (f a) ⁻¹ ∙ (ap f (ap g q) ∙ ε (f a′))
        ＝⟨ ap (λ r → ε (f a) ⁻¹ ∙ (r ∙ ε (f a′))) (ap-∘ g f q ⁻¹) ⟩
      ε (f a) ⁻¹ ∙ (ap (f ∘ g) q ∙ ε (f a′))
        ＝⟨ conjugate E (f a) (f a′) q ⟩
      q ∎

  ap-is-isomorphism : (E : A ≅ B) (a a′ : A) →
    (a ＝ a′) ≅ (forward E a ＝ forward E a′)
  ap-is-isomorphism E a a′ = record
    { forward = ap (forward E)
    ; backward = λ q →
        backward-forward E a ⁻¹ ∙ (ap (backward E) q ∙ backward-forward E a′)
    ; backward-forward = backward-forward-ap E a a′
    ; forward-backward = forward-backward-ap E a a′
    }

------------------------------------------------------------------------
-- Dependent pairs over an isomorphism of indices

-- Over E : A ≅ B, isomorphisms of each fiber C a with D (forward E a) give
-- an isomorphism of the dependent pair types. The backward map reads the
-- second component along the adjusted law. Going forward and back, the
-- triangle turns that law into `ap (forward E)` of the backward-forward law
-- at the first component, and path induction along it returns the second.

module _ {ℓ κ μ ν : Level} {A : Set ℓ} {B : Set κ}
  (C : A → Set μ) (D : B → Set ν) where

  private
    fiber-backward-forward : (E : A ≅ B)
      (fibers : (a : A) → C a ≅ D (forward E a)) (a a′ : A) (e : a′ ＝ a)
      (c : C a) →
      transport C e
        (backward (fibers a′)
          (transport D (ap (forward E) e ⁻¹) (forward (fibers a) c)))
        ＝ c
    fiber-backward-forward E fibers a .a refl c =
      backward-forward (fibers a) c

  Σ-bicong : (E : A ≅ B) → ((a : A) → C a ≅ D (forward E a)) →
    Σ A C ≅ Σ B D
  Σ-bicong E fibers = record
    { forward = λ x → forward E (pr₁ x) , forward (fibers (pr₁ x)) (pr₂ x)
    ; backward = λ y →
        backward E (pr₁ y) ,
        backward (fibers (backward E (pr₁ y)))
          (transport D (coherent-forward-backward E (pr₁ y) ⁻¹) (pr₂ y))
    ; backward-forward = λ x →
        to-Σ-＝ (backward-forward E (pr₁ x))
          ( ap
              (λ e →
                transport C (backward-forward E (pr₁ x))
                  (backward (fibers (backward E (forward E (pr₁ x))))
                    (transport D (e ⁻¹) (forward (fibers (pr₁ x)) (pr₂ x)))))
              (half-adjoint-condition E (pr₁ x) ⁻¹)
          ∙ fiber-backward-forward E fibers (pr₁ x)
              (backward E (forward E (pr₁ x))) (backward-forward E (pr₁ x))
              (pr₂ x))
    ; forward-backward = λ y →
        to-Σ-＝ (coherent-forward-backward E (pr₁ y))
          ( ap (transport D (coherent-forward-backward E (pr₁ y)))
              (forward-backward (fibers (backward E (pr₁ y)))
                (transport D (coherent-forward-backward E (pr₁ y) ⁻¹)
                  (pr₂ y)))
          ∙ back-and-forth-transport D (coherent-forward-backward E (pr₁ y))
              (pr₂ y))
    }

------------------------------------------------------------------------
-- Dependent functions over an isomorphism of indices

-- Over E : A ≅ B, isomorphisms of each fiber C a with D (forward E a) give
-- maps between the dependent function types in both directions. The forward
-- map evaluates a section at the backward image and carries the value along
-- the adjusted law; the backward map evaluates at the forward image. Going
-- forward and back, the triangle turns the adjusted law into
-- `ap (forward E)` of the backward-forward law, which path induction
-- undoes; going back and forward is `apd` of the section along the adjusted
-- law. Both inverse laws are pointwise; extensionality for the two function
-- types, passed explicitly, makes them identifications.

module _ {ℓ κ μ ν : Level} {A : Set ℓ} {B : Set κ}
  (C : A → Set μ) (D : B → Set ν) where

  private
    transport-forward-fiber : (E : A ≅ B)
      (fibers : (a : A) → C a ≅ D (forward E a)) (s : (a : A) → C a)
      (a a′ : A) (e : a′ ＝ a) →
      transport D (ap (forward E) e) (forward (fibers a′) (s a′))
        ＝ forward (fibers a) (s a)
    transport-forward-fiber E fibers s a .a refl = refl

  Π-bicong-forward : (E : A ≅ B) → ((a : A) → C a ≅ D (forward E a)) →
    ((a : A) → C a) → (b : B) → D b
  Π-bicong-forward E fibers s b =
    transport D (coherent-forward-backward E b)
      (forward (fibers (backward E b)) (s (backward E b)))

  Π-bicong-backward : (E : A ≅ B) → ((a : A) → C a ≅ D (forward E a)) →
    ((b : B) → D b) → (a : A) → C a
  Π-bicong-backward E fibers s a = backward (fibers a) (s (forward E a))

  Π-bicong-backward-forward : (E : A ≅ B)
    (fibers : (a : A) → C a ≅ D (forward E a)) (s : (a : A) → C a)
    (a : A) →
    Π-bicong-backward E fibers (Π-bicong-forward E fibers s) a ＝ s a
  Π-bicong-backward-forward E fibers s a =
    ap (backward (fibers a))
      ( ap (λ e → transport D e
              (forward (fibers (backward E (forward E a)))
                (s (backward E (forward E a)))))
          (half-adjoint-condition E a ⁻¹)
      ∙ transport-forward-fiber E fibers s a (backward E (forward E a))
          (backward-forward E a))
      ∙ backward-forward (fibers a) (s a)

  Π-bicong-forward-backward : (E : A ≅ B)
    (fibers : (a : A) → C a ≅ D (forward E a)) (s : (b : B) → D b)
    (b : B) →
    Π-bicong-forward E fibers (Π-bicong-backward E fibers s) b ＝ s b
  Π-bicong-forward-backward E fibers s b =
    ap (transport D (coherent-forward-backward E b))
      (forward-backward (fibers (backward E b))
        (s (forward E (backward E b))))
      ∙ apd s (coherent-forward-backward E b)

  Π-bicong : FunExt A C → FunExt B D → (E : A ≅ B) →
    ((a : A) → C a ≅ D (forward E a)) → ((a : A) → C a) ≅ ((b : B) → D b)
  Π-bicong left right E fibers = record
    { forward = Π-bicong-forward E fibers
    ; backward = Π-bicong-backward E fibers
    ; backward-forward = λ s →
        left (Π-bicong-backward E fibers (Π-bicong-forward E fibers s)) s
          (Π-bicong-backward-forward E fibers s)
    ; forward-backward = λ s →
        right (Π-bicong-forward E fibers (Π-bicong-backward E fibers s)) s
          (Π-bicong-forward-backward E fibers s)
    }
