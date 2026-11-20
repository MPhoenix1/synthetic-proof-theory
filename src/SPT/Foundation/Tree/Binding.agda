{-# OPTIONS --safe --without-K #-}

module SPT.Foundation.Tree.Binding where

-- Binding signatures as signatures over binder depths, acted on by the
-- renaming, translation and substitution of Foundation trees. A binding
-- signature gives operation names, their premises, and the number of
-- variables each premise binds (`Binding`). Its signature has the binder
-- depths below an outer scope as judgments: a premise binding e variables
-- of an operation at depth d sits at depth e + d (`over`). At depth d under
-- an outer scope of n variables the variables are Fin (d + n)
-- (`Variable`), and the expressions in scope n are the open trees at depth
-- 0 whose holes are those variables (`Expression`). A renaming acts by
-- `map`, lifted at each depth (`lift`, `rename`). Moving an expression
-- under d binders is `map-lax-tree` along the shift of depths by d, whose
-- boundary coherence is associativity of +, with the variables moved past
-- the new binders (`shift`, `moved`, `under`). The same translation reads
-- an expression of scope d + n as the premise of a binder of depth d, its
-- first d variables bound and every number kept (`rebound`, `bound`). A
-- substitution acts by `bind`: bound variables stay, and what it
-- substitutes moves under the binders above each variable (`replacement`,
-- `substitute`).
-- So the laws are those of trees: of `map` and `bind` (Tree.Relation,
-- Tree.Substitution), and of lax translation (Tree.LaxTranslation).

open import SPT.Base hiding (lift)
import SPT.Foundation.Signature.Sum as Sig
import SPT.Foundation.Signature.LaxTranslation as Lax
import SPT.Foundation.Tree as Tree
import SPT.Foundation.Tree.Map as Map
import SPT.Foundation.Tree.Substitution as Substitution
import SPT.Foundation.Tree.LaxTranslation as LaxTree

------------------------------------------------------------------------
-- Binding signatures

record Binding (ℓo ℓp : Level) : Set (lsuc (ℓo ⊔ ℓp)) where
  field
    Operation : Set ℓo
    Premise : Operation → Set ℓp
    depth : (o : Operation) → Premise o → ℕ

-- The variables at depth d under an outer scope of n.
Variable : ℕ → ℕ → Set
Variable n d = Fin (d + n)

module _ {ℓo ℓp : Level} (B : Binding ℓo ℓp) where

  open Binding B

  -- Binder depths as judgments: a premise binding e variables sits e
  -- deeper.
  over : Sig.Signature-Over ℕ ℓo ℓp
  over = record
    { Operation = λ _ → Operation
    ; Position = Premise
    ; position-boundary = λ {d} o p → depth o p + d
    }

  -- Expressions in scope n: open trees at depth 0 over its variables.
  Expression : ℕ → Set (ℓo ⊔ ℓp)
  Expression n = Tree.Tree (Sig.to-signature over) (Variable n) 0

  ----------------------------------------------------------------------
  -- Renaming, by map

  -- A renaming lifted over d bound variables.
  lift : {n m : ℕ} (d : ℕ) → (Fin n → Fin m) → Fin (d + n) → Fin (d + m)
  lift {n} {m} d ρ i =
    cases (λ j → j ↑ˡ m) (λ k → d ↑ʳ ρ k) (split-at d n i)

  rename : {n m : ℕ} → (Fin n → Fin m) → Expression n → Expression m
  rename ρ e = Map.map (λ d i → lift d ρ i) e

  ----------------------------------------------------------------------
  -- Moving under binders, by lax translation

  -- Depths shift by d; operations and premises stay.
  shift : (d : ℕ) → Lax.Lax-Signature-Translation (λ c → c + d) over over
  shift d = record
    { map-lax-operation = λ o → o
    ; project-lax-position = λ o p → p
    ; lax-boundary-coherence = λ {c} o p → +-assoc (depth o p) c d
    }

  -- A variable at depth c under an outer scope m, moved under d binders:
  -- the c bound ones stay, the others pass the d new ones.
  moved : (m d c : ℕ) → Variable m c → Variable m (c + d)
  moved m d c x = transport Fin (+-assoc c d m ⁻¹) (lift c (λ y → d ↑ʳ y) x)

  -- An expression of scope m moved under d binders.
  under :
    (m d : ℕ) → Expression m
    → Tree.Tree (Sig.to-signature over) (Variable m) d
  under m d e = LaxTree.map-lax-tree (shift d) (Variable m) (moved m d) e

  -- A variable at depth c in scope d + m, read at depth c + d in scope m:
  -- its number stays.
  rebound : (m d c : ℕ) → Variable (d + m) c → Variable m (c + d)
  rebound m d c x = transport Fin (+-assoc c d m ⁻¹) x

  -- An expression of scope d + m with its first d variables bound by the
  -- binders above it: the premise of a binder of depth d.
  bound :
    (m d : ℕ) → Expression (d + m)
    → Tree.Tree (Sig.to-signature over) (Variable m) d
  bound m d e = LaxTree.map-lax-tree (shift d) (Variable m) (rebound m d) e

  ----------------------------------------------------------------------
  -- Substitution, by bind

  -- The replacement of a variable at depth d: a bound one stays, a free
  -- one is replaced by its expression moved under the d binders.
  replacement :
    {n : ℕ} (m : ℕ) → (Fin n → Expression m) → (d : ℕ) → Variable n d
    → Tree.Tree (Sig.to-signature over) (Variable m) d
  replacement {n} m σ d i =
    cases (λ j → Tree.hole (j ↑ˡ m)) (λ k → under m d (σ k)) (split-at d n i)

  substitute :
    {n : ℕ} (m : ℕ) → (Fin n → Expression m) → Expression n → Expression m
  substitute m σ e = Substitution.bind (replacement m σ) e
