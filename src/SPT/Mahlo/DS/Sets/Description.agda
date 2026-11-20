{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Sets.Description where

-- Set-valued Dybjer–Setzer descriptions and their type-valued readings. A
-- set-valued description has small sets as indices and outputs
-- (`Desc (Small-Set ℓ)`); its arities are sets when the arity of every σ
-- and δ node is (`Set-Arities`). Each reads as a type-valued description
-- (`translate`): outputs by their points, and after each δ node a σ over
-- the sethood of the inputs' decodings. At a family of small sets that σ is
-- the family's own proofs, so shapes read literally, by the η-law of small
-- sets (`translate-shape`), with the points of their outputs
-- (`translate-mark`).
--
-- A type-valued description is set-valued when its arities and outputs
-- are sets at every family (`Set-Valued`). The reading of a description
-- with set arities is, under extensionality (`translated-is-set-valued`),
-- and so are its paths and frontier (`paths-are-set-valued`,
-- `frontier-is-set-valued`). Over a set the shapes of a set-valued
-- description form a set (`shapes-are-sets`), and every output is a set
-- (`marks-are-sets`).

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt; Π-is-proposition)
open import SPT.Foundation.Hedberg using (decidable-equality-gives-set)
open import SPT.Foundation.Propositions using (is-set; propositions-are-sets)
open import SPT.Foundation.Sets using
  ( being-a-set-is-a-proposition; products-of-sets-are-sets
  ; sums-of-sets-are-sets; lifts-of-sets-are-sets )
open import SPT.Mahlo.Sets using
  (Small-Set; small-set; points; points-form-a-set)

open import SPT.IR.Description using
  (Desc; ι; σ; δ; Indexed; indexed; carrier; index; Shape; Mark)
import SPT.Mahlo.DS.Realization.Frontier as Frontier

------------------------------------------------------------------------
-- Set arities

Set-Arities : {ℓ : Level} → Desc {s = ℓ} (Small-Set ℓ) → Set (lsuc ℓ)
Set-Arities {ℓ} (ι e) = Lift (lsuc ℓ) 𝟙
Set-Arities (σ A H) = is-set A × ((a : A) → Set-Arities (H a))
Set-Arities {ℓ} (δ A H) =
  is-set A × ((X : A → Small-Set ℓ) → Set-Arities (H X))

------------------------------------------------------------------------
-- The type-valued reading

translate : {ℓ : Level} → Desc {s = ℓ} (Small-Set ℓ) → Desc {s = ℓ} (Set ℓ)
translate (ι e) = ι (points e)
translate (σ A H) = σ A (λ a → translate (H a))
translate (δ A H) =
  δ A (λ X →
    σ ((a : A) → is-set (X a))
      (λ s → translate (H (λ a → small-set (X a) (s a)))))

-- A shape over a family of small sets, read in the reading: at δ the
-- sethood is the family's own.

module _ {ℓ κ : Level} {K : Set κ} (v : K → Small-Set ℓ) where

  translate-shape : (S : Desc {s = ℓ} (Small-Set ℓ)) →
    Shape S (indexed K v) →
    Shape (translate S) (indexed K (λ k → points (v k)))
  translate-shape (ι e) z = z
  translate-shape (σ A H) (a , z) = a , translate-shape (H a) z
  translate-shape (δ A H) (f , z) =
    f ,
    (λ a → points-form-a-set (v (f a))) ,
    translate-shape (H (λ a → v (f a))) z

  translate-mark : (S : Desc {s = ℓ} (Small-Set ℓ))
    (z : Shape S (indexed K v)) →
    Mark (translate S) (indexed K (λ k → points (v k)))
      (translate-shape S z)
    ＝ points (Mark S (indexed K v) z)
  translate-mark (ι e) z = refl
  translate-mark (σ A H) (a , z) = translate-mark (H a) z
  translate-mark (δ A H) (f , z) = translate-mark (H (λ a → v (f a))) z

------------------------------------------------------------------------
-- Set-valued descriptions

Set-Valued : {ℓ : Level} → Desc {s = ℓ} (Set ℓ) → Set (lsuc ℓ)
Set-Valued {ℓ} (ι e) = Lift (lsuc ℓ) (is-set e)
Set-Valued (σ A H) = is-set A × ((a : A) → Set-Valued (H a))
Set-Valued {ℓ} (δ A H) = is-set A × ((X : A → Set ℓ) → Set-Valued (H X))

two-is-set : (ℓ : Level) → is-set (Lift ℓ 𝟚)
two-is-set ℓ =
  lifts-of-sets-are-sets ℓ
    (decidable-equality-gives-set 𝟚-has-decidable-equality)

-- The sethood of a family of types is a proposition, hence a set.

module _ {ℓ : Level}
  (extensionality : (X : Set ℓ) (Y : X → Set ℓ) → FunExt X Y) where

  sethood-forms-a-set : {A : Set ℓ} (X : A → Set ℓ) →
    is-set ((a : A) → is-set (X a))
  sethood-forms-a-set {A} X =
    propositions-are-sets
      (Π-is-proposition (extensionality A (λ a → is-set (X a)))
        (λ a → being-a-set-is-a-proposition extensionality (X a)))

  translated-is-set-valued : (S : Desc {s = ℓ} (Small-Set ℓ)) →
    Set-Arities S → Set-Valued (translate S)
  translated-is-set-valued (ι e) _ = lift (points-form-a-set e)
  translated-is-set-valued (σ A H) (s , h) =
    s , (λ a → translated-is-set-valued (H a) (h a))
  translated-is-set-valued (δ A H) (s , h) =
    s ,
    (λ X →
      sethood-forms-a-set X ,
      (λ t →
        translated-is-set-valued (H (λ a → small-set (X a) (t a)))
          (h (λ a → small-set (X a) (t a)))))

-- The two summands of a frontier node.
either-is-set-valued : {ℓ : Level} (S T : Desc {s = ℓ} (Set ℓ)) →
  Set-Valued S → Set-Valued T → (t : Lift ℓ 𝟚) →
  Set-Valued (Frontier.either S T t)
either-is-set-valued S T u w (lift ₀) = u
either-is-set-valued S T u w (lift ₁) = w

paths-are-set-valued : {ℓ : Level} (S : Desc {s = ℓ} (Set ℓ)) →
  Set-Valued S → Set-Valued (Frontier.paths S)
paths-are-set-valued (ι e) u = u
paths-are-set-valued {ℓ} (σ A H) (s , h) =
  two-is-set ℓ ,
  either-is-set-valued (ι A) (σ A (λ a → Frontier.paths (H a))) (lift s)
    (s , (λ a → paths-are-set-valued (H a) (h a)))
paths-are-set-valued {ℓ} (δ A H) (s , h) =
  two-is-set ℓ ,
  either-is-set-valued (ι A) (δ A (λ q → Frontier.paths (H q))) (lift s)
    (s , (λ X → paths-are-set-valued (H X) (h X)))

frontier-is-set-valued : {ℓ : Level} (S : Desc {s = ℓ} (Set ℓ)) →
  Set-Valued S → Set-Valued (Frontier.description S)
frontier-is-set-valued {ℓ} S u =
  two-is-set ℓ ,
  either-is-set-valued (Frontier.paths S) S (paths-are-set-valued S u) u

------------------------------------------------------------------------
-- Shapes and outputs

module _ {ℓ : Level}
  (extensionality : (X : Set ℓ) (Y : X → Set ℓ) → FunExt X Y) where

  shapes-are-sets : (S : Desc {s = ℓ} (Set ℓ)) → Set-Valued S →
    (Z : Indexed ℓ (Set ℓ)) → is-set (carrier Z) → is-set (Shape S Z)
  shapes-are-sets (ι e) u Z c = propositions-are-sets (λ x y → refl)
  shapes-are-sets (σ A H) (s , h) Z c =
    sums-of-sets-are-sets s (λ a → shapes-are-sets (H a) (h a) Z c)
  shapes-are-sets (δ A H) (s , h) Z c =
    sums-of-sets-are-sets
      (products-of-sets-are-sets extensionality A (λ a → carrier Z)
        (λ a → c))
      (λ f →
        shapes-are-sets (H (λ a → index Z (f a)))
          (h (λ a → index Z (f a))) Z c)

marks-are-sets : {ℓ κ : Level} (S : Desc {s = ℓ} (Set ℓ)) →
  Set-Valued S → (Z : Indexed κ (Set ℓ)) (z : Shape S Z) →
  is-set (Mark S Z z)
marks-are-sets (ι e) u Z z = lower u
marks-are-sets (σ A H) (s , h) Z (a , z) = marks-are-sets (H a) (h a) Z z
marks-are-sets (δ A H) (s , h) Z (f , z) =
  marks-are-sets (H (λ a → index Z (f a))) (h (λ a → index Z (f a))) Z z
