{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Sorted.Mahlo where

-- Smallness for outputs in Sort ℓ O and the Mahlo rule for the two-sorted
-- family are interderivable. A reflector gives a small algebra of every
-- description through the realization, with no hypothesis (`smallness`),
-- and so of every description with outputs in O alone (`outputs`).
-- Conversely, the closure under the formers and an operator Ψ is a small
-- algebra of one description (`Tag`, `branch`, `description`, `closure`),
-- so smallness gives a reflection of every operator, under extensionality
-- for families of names over small types (`pair`, `mahlo`). A copy of
-- Ambient for the two-sorted family; for O empty it is the
-- ambient equivalence.

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
import SPT.Mahlo.Specification as Specification

open import SPT.IR.Algebra using (Algebra; Law)
open import SPT.IR.Description using (Desc; ι; σ; δ)
open import SPT.Mahlo.DS.Realization.Family using (cast)
open import SPT.Mahlo.DS.Sorted using (Sort; decode; formers)
import SPT.Mahlo.DS.Sorted.Realization as Realization
open import SPT.Mahlo.DS.Sorted.Smallness using (Smallness)
import SPT.Mahlo.DS.Sorted.Smallness as Sorted

------------------------------------------------------------------------
-- The Mahlo rule gives smallness

smallness :
  {ℓ κ : Level} {O : Set κ} → Specification.Mahlo (formers ℓ O)
  → Smallness ℓ O
smallness reflections = record
  { algebra = Realization.reflected-algebra reflections
  ; law = Realization.reflected-law reflections
  }

-- With outputs in O alone.
outputs :
  {ℓ κ : Level} {O : Set κ} → Specification.Mahlo (formers ℓ O)
  → (γ : Desc {s = ℓ} O) → Algebra ℓ γ
outputs reflections γ =
  Sorted.outputs
    (Realization.reflected-algebra reflections (Sorted.embed γ))
    (Realization.reflected-law reflections (Sorted.embed γ))

outputs-law :
  {ℓ κ : Level} {O : Set κ} (reflections : Specification.Mahlo (formers ℓ O))
  (γ : Desc {s = ℓ} O) → Law (outputs reflections γ)
outputs-law reflections γ =
  Sorted.outputs-law
    (Realization.reflected-algebra reflections (Sorted.embed γ))
    (Realization.reflected-law reflections (Sorted.embed γ))

------------------------------------------------------------------------
-- The closure under the formers and an operator, as one description

data Tag {ℓ : Level} : Set ℓ where
  empty unit two natural : Tag
  product sum tree identity : Tag
  index member : Tag

branch :
  {ℓ κ : Level} {O : Set κ} → Specification.Operator (decode ℓ O)
  → Tag {ℓ} → Desc {s = ℓ} (Sort ℓ O)
branch {ℓ} {κ} {O} Ψ empty =
  ι (Specification.Formers.empty (formers ℓ O))
branch {ℓ} {κ} {O} Ψ unit = ι (Specification.Formers.unit (formers ℓ O))
branch {ℓ} {κ} {O} Ψ two = ι (Specification.Formers.two (formers ℓ O))
branch {ℓ} {κ} {O} Ψ natural =
  ι (Specification.Formers.natural (formers ℓ O))
branch {ℓ} {κ} {O} Ψ product =
  δ (Lift ℓ 𝟙)
    (λ A → δ (decode ℓ O (A (lift ⋆)))
      (λ B →
        ι (Specification.Formers.product (formers ℓ O) (A (lift ⋆) , B))))
branch {ℓ} {κ} {O} Ψ sum =
  δ (Lift ℓ 𝟙)
    (λ A → δ (decode ℓ O (A (lift ⋆)))
      (λ B →
        ι (Specification.Formers.sum (formers ℓ O) (A (lift ⋆) , B))))
branch {ℓ} {κ} {O} Ψ tree =
  δ (Lift ℓ 𝟙)
    (λ A → δ (decode ℓ O (A (lift ⋆)))
      (λ B →
        ι (Specification.Formers.tree (formers ℓ O) (A (lift ⋆) , B))))
branch {ℓ} {κ} {O} Ψ identity =
  δ (Lift ℓ 𝟙)
    (λ A → σ (decode ℓ O (A (lift ⋆)))
      (λ x → σ (decode ℓ O (A (lift ⋆)))
        (λ y →
          ι (Specification.Formers.identity (formers ℓ O)
              (A (lift ⋆)) x y))))
branch {ℓ} {κ} {O} Ψ index =
  δ (Lift ℓ 𝟙)
    (λ A → δ (decode ℓ O (A (lift ⋆)))
      (λ B → ι (pr₁ (Ψ (A (lift ⋆) , B)))))
branch {ℓ} {κ} {O} Ψ member =
  δ (Lift ℓ 𝟙)
    (λ A → δ (decode ℓ O (A (lift ⋆)))
      (λ B →
        σ (decode ℓ O (pr₁ (Ψ (A (lift ⋆) , B))))
          (λ c → ι (pr₂ (Ψ (A (lift ⋆) , B)) c))))

description :
  {ℓ κ : Level} {O : Set κ} → Specification.Operator (decode ℓ O)
  → Desc {s = ℓ} (Sort ℓ O)
description Ψ = σ Tag (branch Ψ)

------------------------------------------------------------------------
-- A small algebra of the description is a closure

pair :
  {ℓ κ : Level} {O : Set κ}
  → ((X : Set ℓ) → FunExt X (λ _ → Sort ℓ O))
  → {X Y : Sort ℓ O} {f : decode ℓ O X → Sort ℓ O}
    {g : decode ℓ O Y → Sort ℓ O}
  → (e : X ＝ Y) → ((x : decode ℓ O X) → f x ＝ g (cast (ap (decode ℓ O) e) x))
  → _＝_ {A = Specification.Family (decode ℓ O)} (X , f) (Y , g)
pair {ℓ} {κ} {O} extensionality {X} {f = f} {g = g} refl h =
  ap (λ k → (X , k)) (extensionality (decode ℓ O X) f g h)

closure :
  {ℓ κ : Level} {O : Set κ}
  → ((X : Set ℓ) → FunExt X (λ _ → Sort ℓ O))
  → (Ψ : Specification.Operator (decode ℓ O))
  (M : Algebra ℓ (description Ψ)) → Law M
  → Specification.Closure (formers ℓ O) Ψ (Algebra.K M)
closure {ℓ} {κ} {O} extensionality Ψ M law =
  let op = Algebra.operation M in
  record
  { interpret = Algebra.value M
  ; empty = op (empty , lift ⋆) , law (empty , lift ⋆)
  ; unit = op (unit , lift ⋆) , law (unit , lift ⋆)
  ; two = op (two , lift ⋆) , law (two , lift ⋆)
  ; natural = op (natural , lift ⋆) , law (natural , lift ⋆)
  ; product = λ F →
      op (product , ((λ _ → pr₁ F) , (pr₂ F , lift ⋆))) ,
      law (product , ((λ _ → pr₁ F) , (pr₂ F , lift ⋆)))
  ; sum = λ F →
      op (sum , ((λ _ → pr₁ F) , (pr₂ F , lift ⋆))) ,
      law (sum , ((λ _ → pr₁ F) , (pr₂ F , lift ⋆)))
  ; tree = λ F →
      op (tree , ((λ _ → pr₁ F) , (pr₂ F , lift ⋆))) ,
      law (tree , ((λ _ → pr₁ F) , (pr₂ F , lift ⋆)))
  ; identity = λ a x y →
      op (identity , ((λ _ → a) , (x , (y , lift ⋆)))) ,
      law (identity , ((λ _ → a) , (x , (y , lift ⋆))))
  ; inner = λ F →
      op (index , ((λ _ → pr₁ F) , (pr₂ F , lift ⋆))) ,
      (λ c →
        op (member ,
          ((λ _ → pr₁ F) ,
            (pr₂ F ,
              ( cast
                  (ap (decode ℓ O)
                    (law (index , ((λ _ → pr₁ F) , (pr₂ F , lift ⋆)))))
                  c
              , lift ⋆)))))
  ; inner-β = λ F →
      pair extensionality
        (law (index , ((λ _ → pr₁ F) , (pr₂ F , lift ⋆))))
        (λ c →
          law (member ,
            ((λ _ → pr₁ F) ,
              (pr₂ F ,
                ( cast
                    (ap (decode ℓ O)
                      (law (index , ((λ _ → pr₁ F) , (pr₂ F , lift ⋆)))))
                    c
                , lift ⋆)))))
  }

------------------------------------------------------------------------
-- Smallness gives the Mahlo rule

-- Each operator's reflection is the small algebra of its description,
-- named on the left.

mahlo :
  {ℓ κ : Level} {O : Set κ}
  → ((X : Set ℓ) → FunExt X (λ _ → Sort ℓ O)) → Smallness ℓ O
  → Specification.Mahlo (formers ℓ O)
mahlo extensionality small = record
  { reflect = λ Ψ → record
      { carrier =
          inl (Algebra.K (Smallness.algebra small (description Ψ)))
      ; closure =
          closure extensionality Ψ (Smallness.algebra small (description Ψ))
            (Smallness.law small (description Ψ))
      }
  }
