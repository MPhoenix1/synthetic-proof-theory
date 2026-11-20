{-# OPTIONS --safe --without-K #-}

module SPT.IR.Universal.Discriminator where

-- The universal type keeps whole child maps. For the description of a
-- leaf or a binary node, with constant output (`γ`, `leaf`, `node`), two
-- different child maps have decodings equal as whole functions (`outputs`,
-- by refl), yet the maps and their parent nodes are distinct
-- (`maps-distinct`, `nodes-distinct`). Root recovery returns the original
-- child map by refl (`recover`, `retains`), and native induction sees the
-- depths (`depth`, `plain-depth`, `nested-depth`, `parent-depth`).
-- Dybjer–Setzer induction builds a family indexed by the actual tree,
-- whose computation equation keeps the literal child map (`Trace`,
-- `trace`, `leaf-β`, `node-β`).

open import SPT.Base

open import SPT.IR.Universal using
  (U; Args; box; value; intro; Method; ind; root; selected)
import SPT.IR.Universal.Induction as Induction
open import SPT.IR.Description using (Desc; ι; σ; δ)

------------------------------------------------------------------------
-- A leaf or a binary family of recursive children

finish : (𝟚 → 𝟙) → Desc {s = lzero} 𝟙
finish q = ι ⋆

branch : 𝟚 → Desc {s = lzero} 𝟙
branch ₀ = ι ⋆
branch ₁ = δ 𝟚 finish

γ : Desc {s = lzero} 𝟙
γ = σ 𝟚 branch

leaf : U γ
leaf = intro (box (₀ , box (lift ⋆)))

node : (𝟚 → U γ) → U γ
node f = intro (box (₁ , box (f , box (lift ⋆))))

plain : 𝟚 → U γ
plain b = leaf

nested : 𝟚 → U γ
nested b = node plain

outputs : (λ b → value γ (plain b)) ＝ (λ b → value γ (nested b))
outputs = refl

------------------------------------------------------------------------
-- The child maps and their parent nodes remain distinct

tag : U γ → 𝟚
tag (intro (box (a , b))) = a

maps-distinct : plain ＝ nested → 𝟘
maps-distinct p = ₀-is-not-₁ (ap (λ f → tag (f ₀)) p)

children : Args γ (U γ) (value γ) → 𝟚 → U γ
children (box (₀ , b)) = plain
children (box (₁ , b)) = selected (U γ) (value γ) 𝟚 finish b

recover : U γ → 𝟚 → U γ
recover t = children (root γ t)

retains : (f : 𝟚 → U γ) → recover (node f) ＝ f
retains f = refl

nodes-distinct : node plain ＝ node nested → 𝟘
nodes-distinct p = maps-distinct (ap recover p)

------------------------------------------------------------------------
-- Native induction observes the recursive depth

Depth : U γ → Set
Depth t = ℕ

step : Method γ Depth
step (box (₀ , b)) h = zero
step (box (₁ , box (f , b))) (h , rest) = suc (h ₀)

depth : U γ → ℕ
depth = ind γ Depth step

plain-depth : depth (plain ₀) ＝ zero
plain-depth = refl

nested-depth : depth (nested ₀) ＝ suc zero
nested-depth = refl

parent-depth : depth (node nested) ＝ suc (suc zero)
parent-depth = refl

------------------------------------------------------------------------
-- Dybjer–Setzer induction into a family indexed by the tree

-- A trace follows the child at ₀ down to a leaf.

data Trace : U γ → Set where
  stop : Trace leaf
  next : (f : 𝟚 → U γ) → Trace (f ₀) → Trace (node f)

traced : Induction.Method γ Trace
traced (₀ , b) h = stop
traced (₁ , (f , b)) (h , rest) = next f (h ₀)

trace : (t : U γ) → Trace t
trace = Induction.ind γ Trace traced

leaf-β : trace leaf ＝ stop
leaf-β = Induction.ind-β γ Trace traced (₀ , lift ⋆)

node-β : (f : 𝟚 → U γ) → trace (node f) ＝ next f (trace (f ₀))
node-β f = Induction.ind-β γ Trace traced (₁ , (f , lift ⋆))
