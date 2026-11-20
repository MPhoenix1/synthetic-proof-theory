{-# OPTIONS --safe --without-K #-}

module SPT.IR.Polynomial.General where

-- Dybjer–Setzer's rules for general indexed induction–recursion (Indexed
-- induction–recursion, JLAP 2006, §4.7, §4.8) on the generated part of
-- any algebra of a general code. Shapes are the arguments of the code's
-- polynomial, clause by clause, over any family (`to`, `from`,
-- `output-to`), and hypotheses at the positions of an argument give the
-- ordinary ones (`hyp-forward`, `hyp-forward-β`). Under extensionality for
-- families of information over the arities, introduction and induction on
-- literal arguments (Polynomial.Induction) make the generated part an
-- inductive family of the code (`generated-part`), and its computation
-- identity holds under extensionality for the motive
-- (`generated-part-computation`), so IR.General's rules hold on it.

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)

open import SPT.IR.General using (Inductive-Family; Computation)
open import SPT.IR.Description.Indexed using
  (IDS; ι; σ; δ; General; Shape; Mark; IH; map-IH; polynomial; result;
   general)
open import SPT.IR.Polynomial using
  (Family; carrier; readout; Args; info; shape; Scheme; Extensionality)
open import SPT.IR.Polynomial.Algebra using (Algebra)
open import SPT.IR.Polynomial.Generated using (Position; input)
import SPT.IR.Polynomial.Generated as Generated
import SPT.IR.Polynomial.Induction as Induction

------------------------------------------------------------------------
-- Shapes as arguments of the polynomial

-- At every clause the shape over a family and the argument of the
-- polynomial code are the same type.

module _
  {ε ℓ κ : Level} {I : Set ℓ} {D : I → Set (ℓ ⊔ κ)} {E : Set ε}
  (Z : Family ℓ κ D)
  where

  to : (γ : IDS ℓ κ I D E) → Shape γ Z → Args (polynomial γ) Z
  to (ι e) x = x
  to (σ A f) (a , x) = a , to (f a) x
  to (δ A i F) (g , x) = g , to (F (λ a → readout Z (i a) (g a))) x

  from : (γ : IDS ℓ κ I D E) → Args (polynomial γ) Z → Shape γ Z
  from (ι e) y = y
  from (σ A f) (a , y) = a , from (f a) y
  from (δ A i F) (g , y) = g , from (F (λ a → readout Z (i a) (g a))) y

  from-to : (γ : IDS ℓ κ I D E) (x : Shape γ Z) → from γ (to γ x) ＝ x
  from-to (ι e) x = refl
  from-to (σ A f) (a , x) = ap (a ,_) (from-to (f a) x)
  from-to (δ A i F) (g , x) =
    ap (g ,_) (from-to (F (λ a → readout Z (i a) (g a))) x)

  to-from :
    (γ : IDS ℓ κ I D E) (y : Args (polynomial γ) Z) → to γ (from γ y) ＝ y
  to-from (ι e) y = refl
  to-from (σ A f) (a , y) = ap (a ,_) (to-from (f a) y)
  to-from (δ A i F) (g , y) =
    ap (g ,_) (to-from (F (λ a → readout Z (i a) (g a))) y)

  output-to :
    (γ : IDS ℓ κ I D E) (x : Shape γ Z)
    → result γ (info (polynomial γ) Z (to γ x)) ＝ Mark γ Z x
  output-to (ι e) x = refl
  output-to (σ A f) (a , x) = output-to (f a) x
  output-to (δ A i F) (g , x) =
    output-to (F (λ a → readout Z (i a) (g a))) x

------------------------------------------------------------------------
-- Hypotheses

-- A hypothesis at each position of a shape's argument gives the ordinary
-- hypotheses: a recursive input of a δ is its position in the product.

module _
  {ε ℓ κ ν : Level} {I : Set ℓ} {D : I → Set (ℓ ⊔ κ)} {E : Set ε}
  (Z : Family ℓ κ D) (P : (i : I) → carrier Z i → Set ν)
  where

  hyp-forward :
    (γ : IDS ℓ κ I D E) (x : Shape γ Z)
    → ((z : Position (polynomial γ) Z (to Z γ x))
      → P (pr₁ (input (polynomial γ) Z (to Z γ x) z))
          (pr₂ (input (polynomial γ) Z (to Z γ x) z)))
    → IH γ Z P x
  hyp-forward (ι e) x h = lift ⋆
  hyp-forward (σ A f) (a , x) h = hyp-forward (f a) x (λ z → h (inr z))
  hyp-forward (δ A i F) (g , x) h =
    (λ a → h (inl (a , lift ⋆))) ,
    hyp-forward (F (λ a → readout Z (i a) (g a))) x (λ z → h (inr z))

  hyp-forward-β :
    (S : (i : I) (u : carrier Z i) → P i u) (γ : IDS ℓ κ I D E)
    (x : Shape γ Z)
    → hyp-forward γ x
        (λ z →
          S (pr₁ (input (polynomial γ) Z (to Z γ x) z))
            (pr₂ (input (polynomial γ) Z (to Z γ x) z)))
      ＝ map-IH γ Z P S x
  hyp-forward-β S (ι e) x = refl
  hyp-forward-β S (σ A f) (a , x) = hyp-forward-β S (f a) x
  hyp-forward-β S (δ A i F) (g , x) =
    ap ((λ a → S (i a) (g a)) ,_)
      (hyp-forward-β S (F (λ a → readout Z (i a) (g a))) x)

------------------------------------------------------------------------
-- The generated part as an inductive family of a general code

-- Introduction and induction on literal arguments are introduction and
-- induction at located arguments; the hypotheses at a located argument
-- are those at the positions of its argument.

module _
  {ℓ κ : Level} {I : Set ℓ} {D : I → Set (ℓ ⊔ κ)} (γ : General ℓ κ I D)
  (M : Algebra (general γ)) (let G = Generated.generated M)
  (extensionality : Extensionality ℓ κ)
  where

  generated-part : Inductive-Family γ
  generated-part = record
    { family = G
    ; Arguments = Args (polynomial γ) G
    ; information = info (polynomial γ) G
    ; to = to G γ
    ; from = from G γ
    ; from-to = from-to G γ
    ; to-from = to-from G γ
    ; output-to = output-to G γ
    ; make = Generated.make M extensionality
    ; make-β = λ i y e → Generated.make-β M extensionality i (y , e)
    ; Hypotheses = λ P i b →
        Induction.Literal M P (shape (Scheme.rule (general γ) i)) b
    ; induction = λ P → Induction.source M extensionality P
    ; calls = λ P m i b z →
        Induction.source M extensionality P m
          (pr₁ (input (shape (Scheme.rule (general γ) i)) G b z))
          (pr₂ (input (shape (Scheme.rule (general γ) i)) G b z))
    ; hyp-forward = λ P x h → hyp-forward G P γ x (λ z → h (inl z))
    ; calls-forward = λ P m x →
        hyp-forward-β G P (Induction.source M extensionality P m) γ x
    }

  generated-part-computation :
    {ν : Level} (P : (i : I) → Generated.Carrier M i → Set ν)
    → ((A : Set ℓ) (B : A → Set ν) → FunExt A B)
    → Computation generated-part P
  generated-part-computation P motive =
    Induction.source-β M extensionality P motive
