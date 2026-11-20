{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Clauses where

-- A clause of a description on an indexed family is an operation on its
-- shapes with its law (`Clause`), and finitely many descriptions have one
-- clause each on one family (`Clauses`). The closure of a Tarski family (C
-- , D) under formers Q and an operator Ψ is finitely many clauses of
-- descriptions whose arities are the decodings and the one-point type
-- (`closure-clauses`, `closure-of-clauses`): one description for each
-- former and two for Ψ, its index and its member. This is
-- `Ambient.description` without the σ over its tags, for a family with no
-- code of a type of tags. The branches of `Ambient.description` are these
-- descriptions at the ambient family.

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Mahlo.Specification using
  (Family; Operator; Formers; Decode; Closure)
import SPT.Mahlo.Specification as Specification

open import SPT.IR.Description using
  (Desc; ι; σ; δ; Indexed; carrier; index; Shape; Mark)

------------------------------------------------------------------------
-- Clauses

module _ {s κ d : Level} {D : Set d} where

  -- Mathematical shape:
  -- Σ (o : Shape S Z → carrier Z). Π z. index Z (o z) ＝ Mark S Z z.
  Clause : Desc {s = s} D → Indexed κ D → Set (s ⊔ κ ⊔ d)
  Clause S Z =
    Σ (Shape S Z → carrier Z)
      (λ o → (z : Shape S Z) → index Z (o z) ＝ Mark S Z z)

  Clauses : List (Desc {s = s} D) → Indexed κ D → Set (s ⊔ κ ⊔ d)
  Clauses [] Z = Lift (s ⊔ κ ⊔ d) 𝟙
  Clauses (S ∷ L) Z = Clause S Z × Clauses L Z

------------------------------------------------------------------------
-- The descriptions of a closure

-- An input is a recursive input of arity one, read at its one point.

module _ {κ ℓ : Level} {C : Set κ} (D : C → Set ℓ) where

  -- Mathematical shape: from a and b : D a → carrier, the output
  -- former (a , b).
  family-clause : (Family D → C) → Desc {s = ℓ} C
  family-clause former =
    δ (Lift ℓ 𝟙)
      (λ A → δ (D (A (lift ⋆))) (λ B → ι (former (A (lift ⋆) , B))))

  identity-clause : ((a : C) → D a → D a → C) → Desc {s = ℓ} C
  identity-clause identity =
    δ (Lift ℓ 𝟙)
      ( λ A →
          σ (D (A (lift ⋆)))
            (λ x → σ (D (A (lift ⋆))) (λ y → ι (identity (A (lift ⋆)) x y))))

  -- Mathematical shape: from a family F and x in the index of Ψ F, its member.
  member-clause : Operator D → Desc {s = ℓ} C
  member-clause Ψ =
    δ (Lift ℓ 𝟙)
      ( λ A →
          δ (D (A (lift ⋆)))
            ( λ B →
                σ (D (pr₁ (Ψ (A (lift ⋆) , B))))
                  (λ x → ι (pr₂ (Ψ (A (lift ⋆) , B)) x))))

  closure-clauses : Formers C D → Operator D → List (Desc {s = ℓ} C)
  closure-clauses Q Ψ =
    ι (Formers.empty Q)
    ∷ ι (Formers.unit Q)
    ∷ ι (Formers.two Q)
    ∷ ι (Formers.natural Q)
    ∷ family-clause (Formers.product Q)
    ∷ family-clause (Formers.sum Q)
    ∷ family-clause (Formers.tree Q)
    ∷ identity-clause (Formers.identity Q)
    ∷ family-clause (λ F → pr₁ (Ψ F))
    ∷ member-clause Ψ
    ∷ []

------------------------------------------------------------------------
-- A closure from its clauses

-- Each former's name is the operation of its clause, named by the law there.
-- Ψ's family is the operation of its two clauses; a point is read along the
-- law of the index, and the two laws, joined by extensionality
-- (`family-identified`), give the equation of Ψ.

module _ {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ}
  (extensionality : (a : C) → FunExt (D a) (λ _ → C)) where

  family-identified : {X Y : C} {f : D X → C} {g : D Y → C} (e : X ＝ Y) →
    ((x : D X) → f x ＝ g (transport D e x)) →
    _＝_ {A = Family D} (X , f) (Y , g)
  family-identified {X} {f = f} {g = g} refl h =
    ap (λ k → (X , k)) (extensionality X f g h)

  family-input : (Z : Indexed ℓ C) (former : Family D → C)
    (F : Family (Decode D (index Z))) → Shape (family-clause D former) Z
  family-input Z former F = (λ _ → pr₁ F) , (pr₂ F , lift ⋆)

  member-input : (Z : Indexed ℓ C) (Ψ : Operator D)
    (F : Family (Decode D (index Z))) →
    D (pr₁ (Ψ (Specification.map D (index Z) F))) →
    Shape (member-clause D Ψ) Z
  member-input Z Ψ F x = (λ _ → pr₁ F) , (pr₂ F , (x , lift ⋆))

  closure-of-clauses : (Q : Formers C D) (Ψ : Operator D) (Z : Indexed ℓ C) →
    Clauses (closure-clauses D Q Ψ) Z → Closure Q Ψ (carrier Z)
  closure-of-clauses Q Ψ Z
    (e , (u , (t , (n , (p , (s , (w , (i , (m₀ , (m₁ , _)))))))))) =
    let input = family-input Z (λ F → pr₁ (Ψ F))
    in record
      { interpret = index Z
      ; empty = pr₁ e (lift ⋆) , pr₂ e (lift ⋆)
      ; unit = pr₁ u (lift ⋆) , pr₂ u (lift ⋆)
      ; two = pr₁ t (lift ⋆) , pr₂ t (lift ⋆)
      ; natural = pr₁ n (lift ⋆) , pr₂ n (lift ⋆)
      ; product = λ F →
          pr₁ p (family-input Z (Formers.product Q) F) ,
          pr₂ p (family-input Z (Formers.product Q) F)
      ; sum = λ F →
          pr₁ s (family-input Z (Formers.sum Q) F) ,
          pr₂ s (family-input Z (Formers.sum Q) F)
      ; tree = λ F →
          pr₁ w (family-input Z (Formers.tree Q) F) ,
          pr₂ w (family-input Z (Formers.tree Q) F)
      ; identity = λ a x y →
          pr₁ i ((λ _ → a) , (x , (y , lift ⋆))) ,
          pr₂ i ((λ _ → a) , (x , (y , lift ⋆)))
      ; inner = λ F →
          pr₁ m₀ (input F) ,
          ( λ x →
              pr₁ m₁
                (member-input Z Ψ F (transport D (pr₂ m₀ (input F)) x)))
      ; inner-β = λ F →
          family-identified
            (pr₂ m₀ (input F))
            ( λ x →
                pr₂ m₁
                  (member-input Z Ψ F (transport D (pr₂ m₀ (input F)) x)))
      }
