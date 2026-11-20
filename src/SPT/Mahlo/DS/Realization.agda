{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Realization where

-- Small algebras of type-valued Dybjer–Setzer descriptions from closures
-- of the ambient family. A closure under the frontier operator of γ
-- (`operator`) names every arity reached by a path (`available`).
-- Readiness passes through σ, and through δ by extending families with
-- the actual assignment (`sigma`, `delta`). `compile` then sends every
-- shape over the whole carrier to a code, with its law (`compile-β`), so
-- every such closure is a small algebra of γ (`algebra`, `law`). A Mahlo
-- reflection supplies the closure (`reflected-algebra`, `reflected-law`).

open import SPT.Base
import SPT.Mahlo.Ambient as Ambient
import SPT.Mahlo.Specification as Specification

open import SPT.IR.Algebra using (Algebra; Law)
open import SPT.IR.Description using
  (Desc; ι; σ; δ; indexed; index; Shape; Mark)
import SPT.Mahlo.DS.Realization.Family as Families
import SPT.Mahlo.DS.Realization.Frontier as Frontier

------------------------------------------------------------------------
-- The frontier operator

-- At a family of types, the operator returns the shapes of the frontier
-- description over it, each with its output: the value of a path, or the
-- output of a complete shape.

operator : {ℓ : Level} → Desc {s = ℓ} (Set ℓ) → Ambient.Operator ℓ
operator γ (A , B) =
  Shape (Frontier.description γ) (indexed A B) ,
  Mark (Frontier.description γ) (indexed A B)

------------------------------------------------------------------------
-- Readiness

-- A closure is ready for S when every path of S, over every family of its
-- codes, ends at a named type. A closure of the frontier operator of γ is
-- ready for γ; readiness for σ A H gives readiness for each H a, and
-- readiness for δ A H gives readiness for H at the decoding of any
-- assignment q into the whole carrier.

Available :
  {ℓ : Level} {Ψ : Ambient.Operator ℓ} {K : Set ℓ}
  (L : Specification.Closure (Ambient.formers ℓ) Ψ K)
  → Desc {s = ℓ} (Set ℓ) → Set (lsuc ℓ)
Available L S =
  (F : Specification.Family
    (Specification.Decode (λ X → X) (Specification.Closure.interpret L)))
  (p : Frontier.Path S (Families.view L F))
  → Specification.Name (Specification.Closure.interpret L)
      (Frontier.value S (Families.view L F) p)

available :
  {ℓ : Level} (γ : Desc {s = ℓ} (Set ℓ)) {K : Set ℓ}
  (L : Specification.Closure (Ambient.formers ℓ) (operator γ) K)
  → Available L γ
available γ L F p =
  pr₁
    ( Families.action L F
        (lift ₀ , Frontier.argument γ (Families.view L F) p)) ,
  ( pr₂
      ( Families.action L F
          (lift ₀ , Frontier.argument γ (Families.view L F) p))
  ∙ Frontier.argument-β γ (Families.view L F) p)

sigma :
  {ℓ : Level} {Ψ : Ambient.Operator ℓ} {K : Set ℓ}
  (L : Specification.Closure (Ambient.formers ℓ) Ψ K) {A : Set ℓ}
  (H : A → Desc {s = ℓ} (Set ℓ))
  → Available L (σ A H) → (a : A) → Available L (H a)
sigma L H ready a F p = ready F (inr (a , p))

-- The arity of δ is named at the root path over the unit family. The
-- assignment q and the given family are joined in one extension; the path
-- is moved into it along the right inclusion and shifted along the left
-- one, and the δ path through the extension names the same type.

delta :
  {ℓ : Level} {Ψ : Ambient.Operator ℓ} {K : Set ℓ}
  (L : Specification.Closure (Ambient.formers ℓ) Ψ K) {A : Set ℓ}
  (H : (A → Set ℓ) → Desc {s = ℓ} (Set ℓ))
  → Available L (δ A H) → (q : A → K)
  → Available L (H (λ x → Specification.Closure.interpret L (q x)))
delta L H ready q F p =
  let arity = ready (Families.unit L) (inl (lift ⋆))
      extension = Families.extend L (pr₁ arity) (pr₂ arity) q F
      enlarged = Families.view L (Families.Extension.family extension)
      changed =
        Frontier.change
          (H (λ x → Specification.Closure.interpret L (q x)))
          (Families.Extension.right-β extension ⁻¹) p
      mapped =
        Frontier.map (H (λ x → Specification.Closure.interpret L (q x)))
          (index enlarged) (Families.Extension.right extension) changed
      moved = ap H (Families.Extension.left-β extension ⁻¹)
      named =
        ready (Families.Extension.family extension)
          ( inr
              ( Families.Extension.left extension ,
                Frontier.shift enlarged moved mapped))
  in
  pr₁ named ,
  ( pr₂ named
  ∙ ( Frontier.shift-β enlarged moved mapped
    ∙ ( Frontier.map-β (H (λ x → Specification.Closure.interpret L (q x)))
          (index enlarged) (Families.Extension.right extension) changed
      ∙ Frontier.change-β
          (H (λ x → Specification.Closure.interpret L (q x)))
          (Families.Extension.right-β extension ⁻¹) p)))

------------------------------------------------------------------------
-- Compilation

-- A shape over the whole carrier is compiled by its description: σ keeps
-- its literal argument, δ passes its assignment to `delta`, and ι takes
-- the name of its output, reached at the unit family.

compile :
  {ℓ : Level} {Ψ : Ambient.Operator ℓ} {K : Set ℓ}
  (L : Specification.Closure (Ambient.formers ℓ) Ψ K)
  (S : Desc {s = ℓ} (Set ℓ)) → Available L S
  → Shape S (indexed K (Specification.Closure.interpret L)) → K
compile L (ι e) ready _ = pr₁ (ready (Families.unit L) (lift ⋆))
compile L (σ A H) ready (a , z) = compile L (H a) (sigma L H ready a) z
compile L (δ A H) ready (q , z) =
  compile L (H (λ x → Specification.Closure.interpret L (q x)))
    (delta L H ready q) z

compile-β :
  {ℓ : Level} {Ψ : Ambient.Operator ℓ} {K : Set ℓ}
  (L : Specification.Closure (Ambient.formers ℓ) Ψ K)
  (S : Desc {s = ℓ} (Set ℓ)) (ready : Available L S)
  (z : Shape S (indexed K (Specification.Closure.interpret L)))
  → Specification.Closure.interpret L (compile L S ready z)
    ＝ Mark S (indexed K (Specification.Closure.interpret L)) z
compile-β L (ι e) ready _ = pr₂ (ready (Families.unit L) (lift ⋆))
compile-β L (σ A H) ready (a , z) =
  compile-β L (H a) (sigma L H ready a) z
compile-β L (δ A H) ready (q , z) =
  compile-β L (H (λ x → Specification.Closure.interpret L (q x)))
    (delta L H ready q) z

------------------------------------------------------------------------
-- Small algebras

-- Every closure of the frontier operator of γ is a small algebra of γ on
-- its own carrier, decoding by its interpretation. A Mahlo reflection of
-- the ambient family gives one at every γ.

algebra :
  {ℓ : Level} (γ : Desc {s = ℓ} (Set ℓ)) {K : Set ℓ}
  (L : Specification.Closure (Ambient.formers ℓ) (operator γ) K)
  → Algebra ℓ γ
algebra γ {K} L = record
  { K = K
  ; value = Specification.Closure.interpret L
  ; operation = compile L γ (available γ L)
  }

law :
  {ℓ : Level} (γ : Desc {s = ℓ} (Set ℓ)) {K : Set ℓ}
  (L : Specification.Closure (Ambient.formers ℓ) (operator γ) K)
  → Law (algebra γ L)
law γ L = compile-β L γ (available γ L)

reflected-algebra :
  {ℓ : Level} → Specification.Mahlo (Ambient.formers ℓ)
  → (γ : Desc {s = ℓ} (Set ℓ)) → Algebra ℓ γ
reflected-algebra reflections γ =
  algebra γ
    ( Specification.Reflection.closure
        (Specification.Mahlo.reflect reflections (operator γ)))

reflected-law :
  {ℓ : Level} (reflections : Specification.Mahlo (Ambient.formers ℓ))
  (γ : Desc {s = ℓ} (Set ℓ)) → Law (reflected-algebra reflections γ)
reflected-law reflections γ =
  law γ
    ( Specification.Reflection.closure
        (Specification.Mahlo.reflect reflections (operator γ)))
