{-# OPTIONS --safe --without-K #-}

module SPT.IR.Universal.Source where

-- Induction on source arguments for the universal type of IR.Universal,
-- as Base.Induction specifies it at the source arguments of its
-- description: a step takes its hypotheses as a function on the positions
-- of a source argument. The universal type is
-- an algebra of its description with its law (`algebra`, `law`). Tuple
-- hypotheses are read at positions (`positioned`), and the recursive
-- calls of a function, so read, are that function at the inputs
-- (`positioned-calls`). Dybjer–Setzer's rule then gives source induction
-- (`method`, `source`) with its computation identity (`source-β`), and
-- the sections of every step form a contractible type
-- (`sections-are-contractible`).

open import SPT.Base
open import SPT.Foundation.Contractible using (is-contractible)
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Induction.Initiality using
  (Section; uniform; contractible)

open import SPT.IR.Universal using (U; value; output-to; Std-Hyp; std-calls)
open import SPT.IR.Universal.Induction using (intro; Method; ind; ind-β)
open import SPT.IR.Algebra using (Algebra; Law)
open import SPT.IR.Description using (Desc; ι; σ; δ; indexed; Shape)
open import SPT.IR.Restriction using (Position; input)

------------------------------------------------------------------------
-- Tuple hypotheses at positions

-- A position of a source argument is a point of the arity of one of its
-- δ nodes, and a tuple hypothesis has at that node a function on the
-- arity. At the recursive calls of h the hypothesis at a position is h at
-- the input there: refl at each δ, by induction on the code, with no
-- extensionality.

positioned :
  {s d ν : Level} {D : Set d} (ε : Desc {s = s} D) (X : Set s) (v : X → D)
  (P : X → Set ν) (z : Shape ε (indexed X v))
  → Std-Hyp ε X v P z
  → (p : Position ε (indexed X v) z) → P (input ε (indexed X v) z p)
positioned (ι e) X v P z t (lift ())
positioned (σ A H) X v P (a , z) t p = positioned (H a) X v P z t p
positioned (δ A H) X v P (f , z) (g , t) (inl a) = g a
positioned (δ A H) X v P (f , z) (g , t) (inr p) =
  positioned (H (λ a → v (f a))) X v P z t p

positioned-calls :
  {s d ν : Level} {D : Set d} (ε : Desc {s = s} D) (X : Set s) (v : X → D)
  (P : X → Set ν) (h : (x : X) → P x) (z : Shape ε (indexed X v))
  (p : Position ε (indexed X v) z)
  → positioned ε X v P z (std-calls ε X v P h z) p
    ＝ h (input ε (indexed X v) z p)
positioned-calls (ι e) X v P h z (lift ())
positioned-calls (σ A H) X v P h (a , z) p =
  positioned-calls (H a) X v P h z p
positioned-calls (δ A H) X v P h (f , z) (inl a) = refl
positioned-calls (δ A H) X v P h (f , z) (inr p) =
  positioned-calls (H (λ a → v (f a))) X v P h z p

------------------------------------------------------------------------
-- The universal type as an algebra

-- Its operation is Dybjer–Setzer's introduction on ordinary arguments.
-- Its decoding is the native one, which computes to the output of the
-- argument (`output-β`, by refl), so the law is `output-to`.

algebra : {s d : Level} {D : Set d} (γ : Desc {s = s} D) → Algebra s γ
algebra γ = record
  { K = U γ
  ; value = value γ
  ; operation = intro γ
  }

law : {s d : Level} {D : Set d} (γ : Desc {s = s} D) → Law (algebra γ)
law γ = output-to γ γ

------------------------------------------------------------------------
-- Induction on source arguments

-- A step is a method of Dybjer–Setzer's rule once its tuple hypotheses
-- are read at positions (`method`). The rule's computation identity ends
-- at the positioned calls of the induction, which are its calls at the
-- inputs pointwise; extensionality for functions on positions makes that
-- an identity of hypotheses (`source-β`).

method :
  {s d ν : Level} {D : Set d} (γ : Desc {s = s} D) (P : U γ → Set ν)
  → Argument-Step (input γ (indexed (U γ) (value γ))) (intro γ) P → Method γ P
method γ P m z t = m z (positioned γ (U γ) (value γ) P z t)

source :
  {s d : Level} {D : Set d} (γ : Desc {s = s} D) (ν : Level)
  → Argument-Induction (input γ (indexed (U γ) (value γ))) (intro γ) ν
source γ ν P m = ind γ P (method γ P m)

source-β :
  {s d : Level} {D : Set d} (γ : Desc {s = s} D) (ν : Level)
  → ((A : Set s) (B : A → Set ν) → FunExt A B)
  → Argument-Computation (input γ (indexed (U γ) (value γ))) (intro γ)
      (source γ ν)
source-β γ ν motive P m z =
  ind-β γ P (method γ P m) z
  ∙ ap (m z)
      ( motive (Position γ (indexed (U γ) (value γ)) z)
          (λ p → P (input γ (indexed (U γ) (value γ)) z p))
          ( positioned γ (U γ) (value γ) P z
              (std-calls γ (U γ) (value γ) P (source γ ν P m) z))
          (λ p → source γ ν P m (input γ (indexed (U γ) (value γ)) z p))
          (positioned-calls γ (U γ) (value γ) P (source γ ν P m) z))

------------------------------------------------------------------------
-- The sections of a step

-- The valuations satisfying a step's computation equations form a
-- contractible type (Foundation.Induction.Initiality). The arities, the
-- carrier and the source arguments all have the level s, so one
-- extensionality for functions from types of that level serves for all
-- three.

sections-are-contractible :
  {s d ν : Level} {D : Set d} (γ : Desc {s = s} D)
  → ((A : Set s) (B : A → Set ν) → FunExt A B)
  → (P : U γ → Set ν)
    (m : Argument-Step (input γ (indexed (U γ) (value γ))) (intro γ) P)
  → is-contractible
      (Section (input γ (indexed (U γ) (value γ))) (intro γ) P m)
sections-are-contractible {ν = ν} γ motive P m =
  contractible (input γ (indexed (U γ) (value γ))) (intro γ) (source γ ν)
    (source-β γ ν motive) P m
    ( uniform (input γ (indexed (U γ) (value γ))) (intro γ) (source γ ν) P m
        motive motive motive)
