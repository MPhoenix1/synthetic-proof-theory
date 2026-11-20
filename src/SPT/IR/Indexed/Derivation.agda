{-# OPTIONS --safe --without-K #-}

module SPT.IR.Indexed.Derivation where

-- The derivations of the elements of IR.Indexed's universal family, as
-- closed trees of one signature (`signature`). Its judgments are the
-- elements with their indices, with one operation at each. The positions
-- of an argument are its recursive inputs (`Position`, `input`): one at an
-- input, none at a constant, those of either part at a sum and of every
-- component at a product. The positions of an element are those of its
-- root, with the children there (`positions`, `child`). They are the
-- positions of IR.Polynomial.Generated, read at IR.Indexed's own
-- arguments, which compare with the ordinary ones only under
-- extensionality (IR.Indexed.Comparison).
--
-- The element stays the judgment, so no element is rebuilt from a tree.
-- Native hypotheses are read at the positions and tabulated from them
-- (`hypothesis-at`, `tabulate`), and every element has its derivation, by
-- the native induction (`Derivations`, `derivation`). Theorems on trees
-- reach the native induction through these derivations
-- (IR.Indexed.Initiality).

open import SPT.Base
open import SPT.Foundation.Signature using (Signature)
open import SPT.Foundation.Tree using (node; History)

open import SPT.IR.Indexed using (U; Args; info; Hyp; ind; root)
open import SPT.IR.Polynomial using
  (Poly; var; con; sigma; pi; Scheme; shape)

------------------------------------------------------------------------
-- Recursive inputs of an argument

module _ {ℓ κ : Level} (s : Scheme ℓ κ) where

  Position :
    {X : Set (ℓ ⊔ κ)} (p : Poly ℓ κ (Scheme.Data s) X) → Args s p → Set ℓ
  Position (var i) a = Lift ℓ 𝟙
  Position (con A) a = Lift ℓ 𝟘
  Position (sigma p q) (a , b) = Position p a ⊎ Position (q (info s p a)) b
  Position (pi A p) f = Σ A (λ x → Position (p x) (f x))

  input :
    {X : Set (ℓ ⊔ κ)} (p : Poly ℓ κ (Scheme.Data s) X) (a : Args s p)
    → Position p a → Σ (Scheme.Index s) (U s)
  input (var i) a z = i , a
  input (con A) a (lift ())
  input (sigma p q) (a , b) (inl z) = input p a z
  input (sigma p q) (a , b) (inr z) = input (q (info s p a)) b z
  input (pi A p) f (x , z) = input (p x) (f x) z

------------------------------------------------------------------------
-- Hypotheses at positions

-- A native hypothesis holds at every recursive input of an argument, so it
-- is read at a position, and a function on the positions is tabulated as
-- a hypothesis.

module _
  {ℓ κ ν : Level} (s : Scheme ℓ κ)
  (P : (i : Scheme.Index s) → U s i → Set ν)
  where

  hypothesis-at :
    {X : Set (ℓ ⊔ κ)} (p : Poly ℓ κ (Scheme.Data s) X) (a : Args s p)
    → Hyp s P p a
    → (z : Position s p a) → P (pr₁ (input s p a z)) (pr₂ (input s p a z))
  hypothesis-at (var i) a h z = lower h
  hypothesis-at (con A) a h (lift ())
  hypothesis-at (sigma p q) (a , b) (h , h′) (inl z) =
    hypothesis-at p a h z
  hypothesis-at (sigma p q) (a , b) (h , h′) (inr z) =
    hypothesis-at (q (info s p a)) b h′ z
  hypothesis-at (pi A p) f h (x , z) = hypothesis-at (p x) (f x) (h x) z

  tabulate :
    {X : Set (ℓ ⊔ κ)} (p : Poly ℓ κ (Scheme.Data s) X) (a : Args s p)
    → ( (z : Position s p a)
        → P (pr₁ (input s p a z)) (pr₂ (input s p a z)))
    → Hyp s P p a
  tabulate (var i) a k = lift (k (lift ⋆))
  tabulate (con A) a k = lift ⋆
  tabulate (sigma p q) (a , b) k =
    ( tabulate p a (λ z → k (inl z))
    , tabulate (q (info s p a)) b (λ z → k (inr z)))
  tabulate (pi A p) f k = λ x → tabulate (p x) (f x) (λ z → k (x , z))

------------------------------------------------------------------------
-- The signature of the derivations, and every element's derivation

module _ {ℓ κ : Level} (s : Scheme ℓ κ) where

  positions : Σ (Scheme.Index s) (U s) → Set ℓ
  positions (i , u) = Position s (shape (Scheme.rule s i)) (root s i u)

  child :
    (j : Σ (Scheme.Index s) (U s)) → positions j → Σ (Scheme.Index s) (U s)
  child (i , u) z = input s (shape (Scheme.rule s i)) (root s i u) z

  signature : Signature ℓ lzero ℓ
  signature = record
    { Judgment = Σ (Scheme.Index s) (U s)
    ; Op = λ j → 𝟙
    ; Pos = λ {j} o → positions j
    ; boundary = λ {j} o z → child j z
    }

  Derivations : (i : Scheme.Index s) → U s i → Set ℓ
  Derivations i u = History signature (i , u)

  derivation : (i : Scheme.Index s) (u : U s i) → Derivations i u
  derivation =
    ind s Derivations
      (λ i a k →
        node ⋆ (hypothesis-at s Derivations (shape (Scheme.rule s i)) a k))
