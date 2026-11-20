{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Kripke where

-- Stages for constructions in Kripke style whose restriction laws hold by
-- refl. Stages and their edges are any graph (`Stages`), with no identity,
-- composition or law. An arrow from d to c is a family of maps from the
-- edges into d to the edges into c (`Arrow`), composed as functions
-- (`compose`, written φ ⊚⟨ T ⟩ ψ; `identity`). Data at a stage is read at
-- every edge into it, and restriction along an arrow is precomposition
-- (`restrict`, written x ·⟨ T ⟩ φ). A family stored at every arrow into a
-- stage (`Box`) moves along an arrow by precomposition (`shift`).
-- Composition is associative and unital, and restriction and shifting
-- are functorial, each by refl:
--
--   (φ ⊚ ψ) ⊚ χ ＝ φ ⊚ (ψ ⊚ χ),   identity ⊚ φ ＝ φ ＝ φ ⊚ identity,
--   x · identity ＝ x,   (x · φ) · ψ ＝ x · (φ ⊚ ψ),
--   shift K identity ＝ K,   shift (shift K φ) ψ ＝ shift K (φ ⊚ ψ).
--
-- An arrow need not commute with anything: it is any family of maps of
-- edges, and every construction here reads it pointwise at each edge.

open import SPT.Cubical.Base

------------------------------------------------------------------------
-- Stages and arrows

record Stages (ℓ : Level) : Set (lsuc ℓ) where
  field
    Stage : Set ℓ
    Edge : Stage → Stage → Set ℓ

open Stages public

record Arrow {ℓ : Level} (T : Stages ℓ) (d c : Stage T) : Set ℓ where
  constructor arrow
  field
    apply : (e : Stage T) → Edge T e d → Edge T e c

open Arrow public

infixr 15 compose
infixl 15 restrict

compose :
  {ℓ : Level} (T : Stages ℓ) {c d d′ : Stage T}
  → Arrow T d c → Arrow T d′ d → Arrow T d′ c
compose T φ ψ = arrow (λ e g → apply φ e (apply ψ e g))

syntax compose T φ ψ = φ ⊚⟨ T ⟩ ψ

identity : {ℓ : Level} (T : Stages ℓ) {c : Stage T} → Arrow T c c
identity T = arrow (λ e g → g)

------------------------------------------------------------------------
-- Data read at every edge, and families stored at every arrow

restrict :
  {ℓ ν : Level} (T : Stages ℓ) {c d : Stage T}
  {X : (e : Stage T) → Edge T e c → Set ν}
  → ((e : Stage T) (g : Edge T e c) → X e g) → (φ : Arrow T d c)
  → (e : Stage T) (g : Edge T e d) → X e (apply φ e g)
restrict T x φ = λ e g → x e (apply φ e g)

syntax restrict T x φ = x ·⟨ T ⟩ φ

Box :
  {ℓ ν : Level} (T : Stages ℓ) (c : Stage T)
  → ((d : Stage T) → Arrow T d c → Set ν) → Set (ℓ ⊔ ν)
Box T c X = (d : Stage T) (φ : Arrow T d c) → X d φ

shift :
  {ℓ ν : Level} (T : Stages ℓ) {c d : Stage T}
  {X : (d′ : Stage T) → Arrow T d′ c → Set ν}
  → ((d′ : Stage T) (φ : Arrow T d′ c) → X d′ φ) → (ψ : Arrow T d c)
  → (d′ : Stage T) (φ : Arrow T d′ d) → X d′ (ψ ⊚⟨ T ⟩ φ)
shift T K ψ = λ d′ φ → K d′ (ψ ⊚⟨ T ⟩ φ)

------------------------------------------------------------------------
-- The laws, by refl

compose-associative :
  {ℓ : Level} (T : Stages ℓ) {c d d′ d″ : Stage T}
  (φ : Arrow T d c) (ψ : Arrow T d′ d) (χ : Arrow T d″ d′)
  → (φ ⊚⟨ T ⟩ ψ) ⊚⟨ T ⟩ χ ＝ φ ⊚⟨ T ⟩ (ψ ⊚⟨ T ⟩ χ)
compose-associative T φ ψ χ = refl

identity-left :
  {ℓ : Level} (T : Stages ℓ) {c d : Stage T} (φ : Arrow T d c)
  → identity T ⊚⟨ T ⟩ φ ＝ φ
identity-left T φ = refl

identity-right :
  {ℓ : Level} (T : Stages ℓ) {c d : Stage T} (φ : Arrow T d c)
  → φ ⊚⟨ T ⟩ identity T ＝ φ
identity-right T φ = refl

restrict-identity :
  {ℓ ν : Level} (T : Stages ℓ) {c : Stage T}
  {X : (e : Stage T) → Edge T e c → Set ν}
  (x : (e : Stage T) (g : Edge T e c) → X e g)
  → x ·⟨ T ⟩ identity T ＝ x
restrict-identity T x = refl

restrict-compose :
  {ℓ ν : Level} (T : Stages ℓ) {c d d′ : Stage T}
  {X : (e : Stage T) → Edge T e c → Set ν}
  (x : (e : Stage T) (g : Edge T e c) → X e g)
  (φ : Arrow T d c) (ψ : Arrow T d′ d)
  → (x ·⟨ T ⟩ φ) ·⟨ T ⟩ ψ ＝ x ·⟨ T ⟩ (φ ⊚⟨ T ⟩ ψ)
restrict-compose T x φ ψ = refl

shift-identity :
  {ℓ ν : Level} (T : Stages ℓ) {c : Stage T}
  {X : (d′ : Stage T) → Arrow T d′ c → Set ν}
  (K : (d′ : Stage T) (φ : Arrow T d′ c) → X d′ φ)
  → shift T K (identity T) ＝ K
shift-identity T K = refl

shift-compose :
  {ℓ ν : Level} (T : Stages ℓ) {c d d′ : Stage T}
  {X : (d″ : Stage T) → Arrow T d″ c → Set ν}
  (K : (d″ : Stage T) (φ : Arrow T d″ c) → X d″ φ)
  (φ : Arrow T d c) (ψ : Arrow T d′ d)
  → shift T (shift T K φ) ψ ＝ shift T K (φ ⊚⟨ T ⟩ ψ)
shift-compose T K φ ψ = refl
