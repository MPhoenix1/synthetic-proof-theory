{-# OPTIONS --safe --without-K #-}

module SPT.IR.Smallness where

-- The smallness principle of induction–recursion: every small-arity
-- type-valued Dybjer–Setzer description has an algebra whose carrier lies
-- in the universe of its arities, with its law (`Smallness`). It asserts no
-- induction and no leastness. Every rule of induction–recursion follows
-- from it by an ordinary inductive family, the generated part (`G`, `t`,
-- `make`, `make-β`, `ind`, `ind-β`). Nothing here inhabits it: the Mahlo
-- rule for the ambient family gives it (Mahlo.DS.Ambient), and
-- induction–recursion gives that rule (Mahlo.Residence.Inductive's
-- `ambient-absorbs`, with Residence.Absorption). Its form as lowerings of
-- the raised fixed points is Smallness.Lowering.

open import SPT.Base

open import SPT.IR.Algebra using (Algebra; Law)
open import SPT.IR.Description using
  (Desc; indexed; Shape; Mark)
import SPT.IR.Generated as Generated
open import SPT.IR.Restriction using
  (input; heads; children)

------------------------------------------------------------------------
-- The principle

-- Mathematical shape:
--
--   Π(γ : Desc(Set ℓ)). Σ(K : Set ℓ)(v : K → Set ℓ)
--     (op : Shape γ (K, v) → K). Π z. v (op z) ＝ Mark γ (K, v) z.
--
-- Nonclaim: descriptions with outputs outside Set ℓ are not covered.

record Smallness (ℓ : Level) : Set (lsuc ℓ) where
  field
    algebra : (γ : Desc {s = ℓ} (Set ℓ)) → Algebra ℓ γ
    law : (γ : Desc {s = ℓ} (Set ℓ)) → Law (algebra γ)

------------------------------------------------------------------------
-- The rules of induction–recursion from small algebras

-- The generated part of a description's small algebra gives formation and
-- decoding, introduction with its decoding law, and induction into every
-- level with its computation law.

G : {ℓ : Level} → Smallness ℓ → Desc {s = ℓ} (Set ℓ) → Set ℓ
G small γ = Generated.G (Smallness.algebra small γ)

t :
  {ℓ : Level} (small : Smallness ℓ) (γ : Desc {s = ℓ} (Set ℓ))
  → G small γ → Set ℓ
t small γ = Generated.t (Smallness.algebra small γ)

make :
  {ℓ : Level} (small : Smallness ℓ) (γ : Desc {s = ℓ} (Set ℓ))
  → Shape γ (indexed (G small γ) (t small γ)) → G small γ
make small γ = Generated.make (Smallness.algebra small γ)

make-β :
  {ℓ : Level} (small : Smallness ℓ) (γ : Desc {s = ℓ} (Set ℓ))
  (z : Shape γ (indexed (G small γ) (t small γ)))
  → t small γ (make small γ z) ＝ Mark γ (indexed (G small γ) (t small γ)) z
make-β small γ =
  Generated.make-β (Smallness.algebra small γ) (Smallness.law small γ)

Method :
  {ℓ ν : Level} (small : Smallness ℓ) (γ : Desc {s = ℓ} (Set ℓ))
  → (G small γ → Set ν) → Set (ℓ ⊔ ν)
Method small γ = Generated.Method (Smallness.algebra small γ)

ind :
  {ℓ ν : Level} (small : Smallness ℓ) (γ : Desc {s = ℓ} (Set ℓ))
  (P : G small γ → Set ν) → Method small γ P → (g : G small γ) → P g
ind small γ = Generated.ind (Smallness.algebra small γ)

ind-β :
  {ℓ ν : Level} (small : Smallness ℓ) (γ : Desc {s = ℓ} (Set ℓ))
  (P : G small γ → Set ν) (method : Method small γ P)
  (z : Shape γ (indexed (G small γ) (t small γ)))
  → ind small γ P method (make small γ z)
    ＝ method
        (heads (Algebra.value (Smallness.algebra small γ))
          (Generated.Der (Smallness.algebra small γ)) γ z)
        (children (Algebra.value (Smallness.algebra small γ))
          (Generated.Der (Smallness.algebra small γ)) γ z)
        (λ p →
          ind small γ P method
            ( input γ
                (indexed (Algebra.K (Smallness.algebra small γ))
                  (Algebra.value (Smallness.algebra small γ)))
                (heads (Algebra.value (Smallness.algebra small γ))
                  (Generated.Der (Smallness.algebra small γ)) γ z)
                p
            , children (Algebra.value (Smallness.algebra small γ))
                (Generated.Der (Smallness.algebra small γ)) γ z p))
ind-β small γ P method z = refl
