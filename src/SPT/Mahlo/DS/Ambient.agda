{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Ambient where

-- Smallness and the Mahlo rule for the ambient family are interderivable.
-- A reflector gives a small algebra of every description through the
-- realization, with no hypothesis (`smallness`). Conversely, the closure
-- under the formers and an operator Ψ is a small algebra of one description
-- (`description`, `closure`), so smallness gives a reflection of every
-- operator, under extensionality for families of types (`mahlo`). Nothing
-- here or below imports induction–recursion.

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
import SPT.Mahlo.Ambient as Ambient
import SPT.Mahlo.Specification as Specification

open import SPT.IR.Algebra using (Algebra; Law)
open import SPT.IR.Description using (Desc; ι; σ; δ)
import SPT.Mahlo.DS.Realization as Realization
open import SPT.Mahlo.DS.Realization.Family using (cast)
open import SPT.IR.Smallness using (Smallness)

------------------------------------------------------------------------
-- The Mahlo rule gives smallness

-- Each description's small algebra is the reflection of its frontier
-- operator, compiled by the realization.

smallness :
  {ℓ : Level} → Specification.Mahlo (Ambient.formers ℓ) → Smallness ℓ
smallness reflections = record
  { algebra = Realization.reflected-algebra reflections
  ; law = Realization.reflected-law reflections
  }

------------------------------------------------------------------------
-- The closure under the formers and an operator, as one description

-- One branch for each former of the ambient family and two for Ψ: the index
-- type of Ψ at a family, and its member at a point of that type. Each output
-- is written through Ambient.formers, so the law of a small algebra is
-- literally the naming equation of a closure.

data Tag {ℓ : Level} : Set ℓ where
  empty unit two natural : Tag
  product sum tree identity : Tag
  index member : Tag

branch : {ℓ : Level} → Ambient.Operator ℓ → Tag {ℓ} → Desc {s = ℓ} (Set ℓ)
branch {ℓ} Ψ empty = ι (Specification.Formers.empty (Ambient.formers ℓ))
branch {ℓ} Ψ unit = ι (Specification.Formers.unit (Ambient.formers ℓ))
branch {ℓ} Ψ two = ι (Specification.Formers.two (Ambient.formers ℓ))
branch {ℓ} Ψ natural =
  ι (Specification.Formers.natural (Ambient.formers ℓ))
branch {ℓ} Ψ product =
  δ (Lift ℓ 𝟙)
    (λ A → δ (A (lift ⋆))
      (λ B →
        ι (Specification.Formers.product (Ambient.formers ℓ)
            (A (lift ⋆) , B))))
branch {ℓ} Ψ sum =
  δ (Lift ℓ 𝟙)
    (λ A → δ (A (lift ⋆))
      (λ B →
        ι (Specification.Formers.sum (Ambient.formers ℓ) (A (lift ⋆) , B))))
branch {ℓ} Ψ tree =
  δ (Lift ℓ 𝟙)
    (λ A → δ (A (lift ⋆))
      (λ B →
        ι (Specification.Formers.tree (Ambient.formers ℓ) (A (lift ⋆) , B))))
branch {ℓ} Ψ identity =
  δ (Lift ℓ 𝟙)
    (λ A → σ (A (lift ⋆))
      (λ x → σ (A (lift ⋆))
        (λ y →
          ι (Specification.Formers.identity (Ambient.formers ℓ)
              (A (lift ⋆)) x y))))
branch {ℓ} Ψ index =
  δ (Lift ℓ 𝟙)
    (λ A → δ (A (lift ⋆)) (λ B → ι (pr₁ (Ψ (A (lift ⋆) , B)))))
branch {ℓ} Ψ member =
  δ (Lift ℓ 𝟙)
    (λ A → δ (A (lift ⋆))
      (λ B →
        σ (pr₁ (Ψ (A (lift ⋆) , B)))
          (λ c → ι (pr₂ (Ψ (A (lift ⋆) , B)) c))))

description : {ℓ : Level} → Ambient.Operator ℓ → Desc {s = ℓ} (Set ℓ)
description Ψ = σ Tag (branch Ψ)

------------------------------------------------------------------------
-- A small algebra of the description is a closure

-- Each former's name is the operation at the former's branch, named by the
-- law there. Ψ's family is the operation at its two branches; a point is
-- read along the law at the index branch, and the two laws, joined by
-- extensionality (`pair`), give the equation of Ψ.

pair :
  {ℓ : Level} → ((X : Set ℓ) → FunExt X (λ _ → Set ℓ))
  → {X Y : Set ℓ} {f : X → Set ℓ} {g : Y → Set ℓ}
  → (e : X ＝ Y) → ((x : X) → f x ＝ g (cast e x))
  → _＝_ {A = Σ (Set ℓ) (λ Z → Z → Set ℓ)} (X , f) (Y , g)
pair extensionality {X} {f = f} {g = g} refl h =
  ap (λ k → (X , k)) (extensionality X f g h)

closure :
  {ℓ : Level} → ((X : Set ℓ) → FunExt X (λ _ → Set ℓ))
  → (Ψ : Ambient.Operator ℓ) (M : Algebra ℓ (description Ψ)) → Law M
  → Specification.Closure (Ambient.formers ℓ) Ψ (Algebra.K M)
closure extensionality Ψ M law =
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
              (cast (law (index , ((λ _ → pr₁ F) , (pr₂ F , lift ⋆)))) c ,
                lift ⋆)))))
  ; inner-β = λ F →
      pair extensionality
        (law (index , ((λ _ → pr₁ F) , (pr₂ F , lift ⋆))))
        (λ c →
          law (member ,
            ((λ _ → pr₁ F) ,
              (pr₂ F ,
                (cast (law (index , ((λ _ → pr₁ F) , (pr₂ F , lift ⋆))))
                  c ,
                  lift ⋆)))))
  }

------------------------------------------------------------------------
-- Smallness gives the Mahlo rule

-- Each operator's reflection is the small algebra of its description.

mahlo :
  {ℓ : Level} → ((X : Set ℓ) → FunExt X (λ _ → Set ℓ)) → Smallness ℓ
  → Specification.Mahlo (Ambient.formers ℓ)
mahlo extensionality small = record
  { reflect = λ Ψ → record
      { carrier = Algebra.K (Smallness.algebra small (description Ψ))
      ; closure =
          closure extensionality Ψ (Smallness.algebra small (description Ψ))
            (Smallness.law small (description Ψ))
      }
  }
