{-# OPTIONS --safe --without-K #-}

module SPT.IR.Universal.Derivation where

-- The derivations of the elements of IR.Universal's universal type, as
-- closed trees of one signature (`signature`). Its judgments are the
-- elements of U γ, with one operation at each. The positions of an
-- element are those of its root, a point of the arity of one of the root's
-- δ nodes, and the child at a position is the input there (`positions`,
-- `child`):
--
--   Pos u = Position γ (from (root γ u)),
--   boundary u p = input γ (from (root γ u)) p.
--
-- The element stays the judgment, so no element is rebuilt from a tree, and
-- the signature lives at the level of U γ whatever the level of the
-- decodings. Native hypotheses are read at the positions and tabulated
-- from them (`hypothesis-at`, `tabulate`), and every element has its
-- derivation, by the native induction (`derivation`). Theorems on trees
-- reach the native induction through these derivations
-- (IR.Universal.Initiality).

open import SPT.Base
open import SPT.Foundation.Signature using (Signature)
open import SPT.Foundation.Tree using (node; History)

open import SPT.IR.Universal using
  (U; Args; box; value; from; Hyp; ind; root)
open import SPT.IR.Description using (Desc; ι; σ; δ; indexed)
open import SPT.IR.Restriction using (Position; input)

------------------------------------------------------------------------
-- Hypotheses at positions

-- A native hypothesis has at a δ node one function on the arity; a
-- position of the argument is a point of one such arity, so a hypothesis
-- is read at a position, and a function on the positions is tabulated as
-- a hypothesis.

module _
  {s d ν : Level} {D : Set d} (γ : Desc {s = s} D) (P : U γ → Set ν)
  where

  hypothesis-at :
    (ε : Desc {s = s} D) (a : Args ε (U γ) (value γ))
    → Hyp ε (U γ) (value γ) P a
    → (p : Position ε (indexed (U γ) (value γ))
             (from ε (U γ) (value γ) a))
    → P (input ε (indexed (U γ) (value γ)) (from ε (U γ) (value γ) a) p)
  hypothesis-at (ι e) (box a) h (lift ())
  hypothesis-at (σ A H) (box (a , b)) h p = hypothesis-at (H a) b h p
  hypothesis-at (δ A H) (box (f , b)) (g , h) (inl x) = g x
  hypothesis-at (δ A H) (box (f , b)) (g , h) (inr p) =
    hypothesis-at (H (λ x → value γ (f x))) b h p

  tabulate :
    (ε : Desc {s = s} D) (a : Args ε (U γ) (value γ))
    → ( (p : Position ε (indexed (U γ) (value γ))
               (from ε (U γ) (value γ) a))
        → P (input ε (indexed (U γ) (value γ))
               (from ε (U γ) (value γ) a) p))
    → Hyp ε (U γ) (value γ) P a
  tabulate (ι e) (box a) k = lift ⋆
  tabulate (σ A H) (box (a , b)) k = tabulate (H a) b k
  tabulate (δ A H) (box (f , b)) k =
    ( (λ x → k (inl x))
    , tabulate (H (λ x → value γ (f x))) b (λ p → k (inr p)))

------------------------------------------------------------------------
-- The signature of the derivations, and every element's derivation

module _ {s d : Level} {D : Set d} (γ : Desc {s = s} D) where

  positions : U γ → Set s
  positions u =
    Position γ (indexed (U γ) (value γ)) (from γ (U γ) (value γ) (root γ u))

  child : (u : U γ) → positions u → U γ
  child u p =
    input γ (indexed (U γ) (value γ)) (from γ (U γ) (value γ) (root γ u)) p

  signature : Signature s lzero s
  signature = record
    { Judgment = U γ
    ; Op = λ u → 𝟙
    ; Pos = λ {u} o → positions u
    ; boundary = λ {u} o p → child u p
    }

  derivation : (u : U γ) → History signature u
  derivation =
    ind γ (History signature)
      (λ a k → node ⋆ (hypothesis-at γ (History signature) γ a k))
