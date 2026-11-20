{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Universe.Formation where

-- The spaces of a reflected child (Mahlo.Child) use the generated universe
-- literally: its carrier, decoding and formers are the universe's (`code-β`,
-- `decode-β`, `formers-β`), and the seed space U is recovered (`ambient-β`,
-- `point-β`). A nonconstant operator retains the complete input family and
-- returns point-dependent fibers; selecting a different result point changes
-- subsequent total formation (`no-selection-loss`). Coded boundary families of
-- Universe.Boundary and their fills also feed later formation: complete fills,
-- not boundaries alone, determine the next total (`Boundary.no-filler-loss`),
-- and a generated carrier can be the index type of a further formation
-- (`Boundary.next`).

open import SPT.Base
open import SPT.Foundation.Spaces using (DΣ; Total)
open import SPT.Mahlo.Universe.Boundary using
  (RetainedFill; retained-seed; filler-indexed-fan)
import SPT.Mahlo.Ambient as Ambient
import SPT.Mahlo.Child as Child
open import SPT.Foundation.Tree.W using (sup)
open import SPT.Mahlo.Decoding using (reflect; child-formers)
open import SPT.Mahlo.Specification using (Decode; Closure; Reflection)
import SPT.Mahlo.Universe as Universe

------------------------------------------------------------------------
-- The reflected child is the generated universe

code-β : {ℓ : Level} (U : DΣ ℓ ℓ) (Ψ : Ambient.Operator ℓ) →
  Reflection.carrier (reflect (Universe.reflection U) Ψ) ＝ Universe.Code U Ψ
code-β U Ψ = refl

decode-β : {ℓ : Level} (U : DΣ ℓ ℓ) (Ψ : Ambient.Operator ℓ)
  (a : Universe.Code U Ψ) →
  Decode (λ (A : Set ℓ) → A)
    ( Closure.interpret
        ( Reflection.closure (reflect (Universe.reflection U) Ψ)))
    a
    ＝ Universe.decode a
decode-β U Ψ a = refl

formers-β : {ℓ : Level} (U : DΣ ℓ ℓ)
  (Ψ : Ambient.Operator ℓ) →
  child-formers (Reflection.closure (reflect (Universe.reflection U) Ψ))
    ＝ Universe.formers U Ψ
formers-β U Ψ = refl

ambient : {ℓ : Level} (U : DΣ ℓ ℓ) (Ψ : Ambient.Operator ℓ) →
  Child.Mahlo-Space (Universe.reflection U) Ψ
ambient U Ψ = Child.space Universe.codes Universe.old

ambient-β : {ℓ : Level} (U : DΣ ℓ ℓ) (Ψ : Ambient.Operator ℓ) →
  Child.display (Universe.reflection U) Ψ (ambient U Ψ) ＝ U
ambient-β U Ψ = refl

point-β : {ℓ : Level} (U : DΣ ℓ ℓ) (Ψ : Ambient.Operator ℓ) →
  Total (Child.display (Universe.reflection U) Ψ (ambient U Ψ)) ＝ Total U
point-β U Ψ = refl

------------------------------------------------------------------------
-- A nonconstant operator, and the selected result point

U : DΣ lzero lzero
U = record { Base = Lift lzero 𝟙 ; Fiber = λ _ → 𝟚 }

-- The true branch retains the input fiber; the false branch is empty.
-- The result domain retains both a choice and a complete input point.
selection : (A : Set) (B : A → Set) → Σ 𝟚 (λ _ → Σ A B) → Set
selection A B (₀ , p) = Lift lzero 𝟘
selection A B (₁ , p) = B (pr₁ p)

Ψ : Ambient.Operator lzero
Ψ (A , B) = Σ 𝟚 (λ _ → Σ A B) , selection A B

Code : Set
Code = Universe.Code U Ψ

decode : Code → Set
decode = Universe.decode

Space : Set
Space = Child.Mahlo-Space (Universe.reflection U) Ψ

acted : Space
acted = Child.action (Universe.reflection U) Ψ (ambient U Ψ)

acted-β : acted ＝ Child.space
  (Universe.result Universe.codes Universe.old)
  (Universe.branch Universe.codes Universe.old)
acted-β = refl

acted-parent-β : Child.parent-family (Universe.reflection U) Ψ acted ＝
  Ψ (Universe.map (Universe.ambient U Ψ))
acted-parent-β = refl

selected : 𝟚 → Code
selected c = Child.fiber acted (c , (lift ⋆ , ₀))

continued : 𝟚 → Code
continued c = Universe.sum (selected c) (λ _ → Universe.unit)

absent : decode (continued ₀) → Lift lzero 𝟘
absent (() , _)

present : decode (continued ₁)
present = ₁ , lift ⋆

no-selection-loss : decode (continued ₀) ＝ decode (continued ₁) →
  Lift lzero 𝟘
no-selection-loss p = absent (transport (λ A → A) (p ⁻¹) present)

twice : Space
twice = Child.action (Universe.reflection U) Ψ acted

twice-parent-β : Child.parent-family (Universe.reflection U) Ψ twice ＝
  Ψ (Ψ (Universe.map (Universe.ambient U Ψ)))
twice-parent-β = refl

self-equalities : decode (Universe.product Universe.natural
  (λ n → Universe.identity Universe.natural n n))
self-equalities n = refl

leaf : decode (Universe.tree Universe.two (λ _ → Universe.empty))
leaf = sup (lift ₀) (λ x → 𝟘-elim (lower x))

methods : Universe.Methods U Ψ (λ _ → ℕ)
methods = record
  { on-codes = zero
  ; on-old = λ c → zero
  ; on-empty = zero
  ; on-unit = zero
  ; on-two = zero
  ; on-natural = zero
  ; on-product = λ a b n f → suc n
  ; on-sum = λ a b n f → suc n
  ; on-tree = λ a b n f → suc n
  ; on-identity = λ a x y n → suc n
  ; on-result = λ a b n f → suc n
  ; on-branch = λ a b y n f → suc n
  ; on-boundary = λ S i h → suc (Universe.All.on-index h)
  ; on-filling = λ S i r h → suc (Universe.All.on-index h)
  }

spine : Code → ℕ
spine = Universe.ind methods

spine-β : (c : 𝟚) → spine (continued c) ＝ suc (suc zero)
spine-β c = refl

------------------------------------------------------------------------
-- Coded boundary families and their fills

-- The index selects a seed type, and each seed selects its exact filler.
-- These codes belong to the same universe as the resulting carrier.
module Boundary where

  seed : decode Universe.two → Code
  seed (lift ₀) = Universe.two
  seed (lift ₁) = Universe.unit

  fiber : (i : decode Universe.two) → decode (seed i) → Code
  fiber (lift ₀) (lift ₀) = Universe.empty
  fiber (lift ₀) (lift ₁) = Universe.unit
  fiber (lift ₁) x = Universe.two

  diagram : Universe.Seeds Code decode
  diagram = Universe.seeds Universe.two seed fiber

  carrier : decode Universe.two → Code
  carrier = Universe.boundary diagram

  fill : (i : decode Universe.two) → decode (carrier i) → Code
  fill i = Universe.filling diagram i

  seed₀ seed₁ : decode (carrier (lift ₀))
  seed₀ = retained-seed (lift ₀)
  seed₁ = retained-seed (lift ₁)

  fan blocked : decode (carrier (lift ₀))
  fan = filler-indexed-fan seed₁ (λ _ → seed₁)
  blocked = filler-indexed-fan seed₁ (λ _ → seed₀)

  filled : decode (fill (lift ₀) fan)
  filled _ = lift ⋆

  blocked-empty : decode (fill (lift ₀) blocked) → Lift lzero 𝟘
  blocked-empty f = f (lift ⋆)

  -- Complete fillers, rather than boundaries alone, determine the next
  -- total. The same fan domain can have fillable or unfillable children.
  total : decode (carrier (lift ₀)) → Code
  total r = Universe.sum (fill (lift ₀) r) (λ _ → Universe.unit)

  point : decode (total fan)
  point = filled , lift ⋆

  unfilled : decode (total blocked) → Lift lzero 𝟘
  unfilled (f , _) = blocked-empty f

  no-filler-loss : decode (total blocked) ＝ decode (total fan) →
    Lift lzero 𝟘
  no-filler-loss p = unfilled (transport (λ A → A) (p ⁻¹) point)

  -- The other index has a different seed type and different fillers.
  other : decode (carrier (lift ₁))
  other = retained-seed (lift ⋆)

  other-filler : decode (fill (lift ₁) other)
  other-filler = lift ₁

  space : Space
  space = Child.from-family (Universe.reflection U) Ψ
    (Universe.formed diagram (lift ₀))

  space-β : Child.display (Universe.reflection U) Ψ space ＝ record
    { Base = Universe.Boundary diagram (lift ₀)
    ; Fiber = λ r → RetainedFill r
    }
  space-β = refl

  advanced : Space
  advanced = Child.action (Universe.reflection U) Ψ space

  advanced-point : Total (Child.display (Universe.reflection U) Ψ advanced)
  advanced-point = (₁ , (fan , filled)) , filled

  -- The first generated carrier is now the index type of another
  -- formation. Its exact fillers are the seeds; their identities fill it.
  next : Universe.Seeds Code decode
  next = Universe.seeds (carrier (lift ₀)) (fill (lift ₀))
    (λ r x → Universe.identity (fill (lift ₀) r) x x)

  nested : Code
  nested = Universe.boundary next fan

  nested-seed : decode nested
  nested-seed = retained-seed filled

  nested-filler : decode (Universe.filling next fan nested-seed)
  nested-filler = refl

  nested-filling-β : decode (Universe.filling next fan nested-seed) ＝
    (filled ＝ filled)
  nested-filling-β = refl

  nested-spine-β : spine nested ＝ suc (suc zero)
  nested-spine-β = refl
