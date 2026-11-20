{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Sets.Ambient where

-- Closures of the parent of small sets as small algebras of one
-- set-valued description, after DS.Ambient. DS.Ambient's tags form a set,
-- read through a retraction onto ℕ (`tag-code`, `tag-of-code`,
-- `tags-form-a-set`). One branch for each former of the parent of sets
-- and two for an operator Ψ (`branch`, `description`), every arity a set
-- (`description-arities`); each output is written through the parent's
-- formers, so the law of a small algebra of the description is literally
-- the naming equation of a closure of Ψ (`closure`).

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Hedberg using (decidable-equality-gives-set)
open import SPT.Foundation.Propositions using (is-set; propositions-are-sets)
import SPT.Mahlo.Specification as Specification
open import SPT.Mahlo.Sets using
  (Small-Set; points; points-form-a-set; Operator; set-formers)

open import SPT.IR.Algebra using (Algebra; Law)
open import SPT.Mahlo.DS.Ambient using
  ( Tag; empty; unit; two; natural; product; sum; tree; identity; index
  ; member )
open import SPT.IR.Description using (Desc; ι; σ; δ)
open import SPT.Mahlo.DS.Naming.Trees using (pair)
open import SPT.Mahlo.DS.Realization.Family using (cast)
open import SPT.Mahlo.DS.Sets.Description using (Set-Arities)

------------------------------------------------------------------------
-- The tags form a set

tag-code : {ℓ : Level} → Tag {ℓ} → ℕ
tag-code empty = 0
tag-code unit = 1
tag-code two = 2
tag-code natural = 3
tag-code product = 4
tag-code sum = 5
tag-code tree = 6
tag-code identity = 7
tag-code index = 8
tag-code member = 9

tag-of-code : {ℓ : Level} → ℕ → Tag {ℓ}
tag-of-code 0 = empty
tag-of-code 1 = unit
tag-of-code 2 = two
tag-of-code 3 = natural
tag-of-code 4 = product
tag-of-code 5 = sum
tag-of-code 6 = tree
tag-of-code 7 = identity
tag-of-code 8 = index
tag-of-code n = member

tag-of-tag-code : {ℓ : Level} (t : Tag {ℓ}) → tag-of-code (tag-code t) ＝ t
tag-of-tag-code empty = refl
tag-of-tag-code unit = refl
tag-of-tag-code two = refl
tag-of-tag-code natural = refl
tag-of-tag-code product = refl
tag-of-tag-code sum = refl
tag-of-tag-code tree = refl
tag-of-tag-code identity = refl
tag-of-tag-code index = refl
tag-of-tag-code member = refl

tags-have-decidable-equality : {ℓ : Level} →
  has-decidable-equality (Tag {ℓ})
tags-have-decidable-equality t t′ =
  cases
    (λ e →
      inl (tag-of-tag-code t ⁻¹ ∙ ap tag-of-code e ∙ tag-of-tag-code t′))
    (λ n → inr (λ e → n (ap tag-code e)))
    (ℕ-has-decidable-equality (tag-code t) (tag-code t′))

tags-form-a-set : {ℓ : Level} → is-set (Tag {ℓ})
tags-form-a-set = decidable-equality-gives-set tags-have-decidable-equality

------------------------------------------------------------------------
-- The description of a closure

module _ {ℓ : Level}
  (functions : (X : Set ℓ) (Y : X → Set ℓ) → FunExt X Y) where

  branch : Operator ℓ → Tag {ℓ} → Desc {s = ℓ} (Small-Set ℓ)
  branch Ψ empty = ι (Specification.Formers.empty (set-formers functions))
  branch Ψ unit = ι (Specification.Formers.unit (set-formers functions))
  branch Ψ two = ι (Specification.Formers.two (set-formers functions))
  branch Ψ natural =
    ι (Specification.Formers.natural (set-formers functions))
  branch Ψ product =
    δ (Lift ℓ 𝟙)
      (λ A → δ (points (A (lift ⋆)))
        (λ B →
          ι (Specification.Formers.product (set-formers functions)
              (A (lift ⋆) , B))))
  branch Ψ sum =
    δ (Lift ℓ 𝟙)
      (λ A → δ (points (A (lift ⋆)))
        (λ B →
          ι (Specification.Formers.sum (set-formers functions)
              (A (lift ⋆) , B))))
  branch Ψ tree =
    δ (Lift ℓ 𝟙)
      (λ A → δ (points (A (lift ⋆)))
        (λ B →
          ι (Specification.Formers.tree (set-formers functions)
              (A (lift ⋆) , B))))
  branch Ψ identity =
    δ (Lift ℓ 𝟙)
      (λ A → σ (points (A (lift ⋆)))
        (λ x → σ (points (A (lift ⋆)))
          (λ y →
            ι (Specification.Formers.identity (set-formers functions)
                (A (lift ⋆)) x y))))
  branch Ψ index =
    δ (Lift ℓ 𝟙)
      (λ A → δ (points (A (lift ⋆))) (λ B → ι (pr₁ (Ψ (A (lift ⋆) , B)))))
  branch Ψ member =
    δ (Lift ℓ 𝟙)
      (λ A → δ (points (A (lift ⋆)))
        (λ B →
          σ (points (pr₁ (Ψ (A (lift ⋆) , B))))
            (λ c → ι (pr₂ (Ψ (A (lift ⋆) , B)) c))))

  description : Operator ℓ → Desc {s = ℓ} (Small-Set ℓ)
  description Ψ = σ Tag (branch Ψ)

  -- Every arity is the unit type, the tags or the points of a small set.

  branch-arities : (Ψ : Operator ℓ) (t : Tag {ℓ}) → Set-Arities (branch Ψ t)
  branch-arities Ψ empty = lift ⋆
  branch-arities Ψ unit = lift ⋆
  branch-arities Ψ two = lift ⋆
  branch-arities Ψ natural = lift ⋆
  branch-arities Ψ product =
    propositions-are-sets (λ x y → refl) ,
    (λ A → points-form-a-set (A (lift ⋆)) , (λ B → lift ⋆))
  branch-arities Ψ sum =
    propositions-are-sets (λ x y → refl) ,
    (λ A → points-form-a-set (A (lift ⋆)) , (λ B → lift ⋆))
  branch-arities Ψ tree =
    propositions-are-sets (λ x y → refl) ,
    (λ A → points-form-a-set (A (lift ⋆)) , (λ B → lift ⋆))
  branch-arities Ψ identity =
    propositions-are-sets (λ x y → refl) ,
    (λ A →
      points-form-a-set (A (lift ⋆)) ,
      (λ x → points-form-a-set (A (lift ⋆)) , (λ y → lift ⋆)))
  branch-arities Ψ index =
    propositions-are-sets (λ x y → refl) ,
    (λ A → points-form-a-set (A (lift ⋆)) , (λ B → lift ⋆))
  branch-arities Ψ member =
    propositions-are-sets (λ x y → refl) ,
    (λ A →
      points-form-a-set (A (lift ⋆)) ,
      (λ B →
        points-form-a-set (pr₁ (Ψ (A (lift ⋆) , B))) , (λ c → lift ⋆)))

  description-arities : (Ψ : Operator ℓ) → Set-Arities (description Ψ)
  description-arities Ψ = tags-form-a-set , branch-arities Ψ

------------------------------------------------------------------------
-- A small algebra of the description is a closure

-- Each former's name is the operation at its branch, named by the law
-- there. Ψ's family is the operation at its two branches; a point is read
-- along the law at the index branch, and the two laws, joined by
-- extensionality for families of small sets (`pair`), give the equation
-- of Ψ.

module _ {ℓ : Level}
  (functions : (X : Set ℓ) (Y : X → Set ℓ) → FunExt X Y)
  (code-families : (X : Set ℓ) → FunExt X (λ _ → Small-Set ℓ))
  where

  closure : (Ψ : Operator ℓ) (M : Algebra ℓ (description functions Ψ)) →
    Law M → Specification.Closure (set-formers functions) Ψ (Algebra.K M)
  closure Ψ M law =
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
                    (ap points
                      (law (index , ((λ _ → pr₁ F) , (pr₂ F , lift ⋆)))))
                    c
                , lift ⋆)))))
    ; inner-β = λ F →
        pair points code-families
          (law (index , ((λ _ → pr₁ F) , (pr₂ F , lift ⋆))))
          (λ c →
            law (member ,
              ((λ _ → pr₁ F) ,
                (pr₂ F ,
                  ( cast
                      (ap points
                        (law (index , ((λ _ → pr₁ F) , (pr₂ F , lift ⋆)))))
                      c
                  , lift ⋆)))))
    }
