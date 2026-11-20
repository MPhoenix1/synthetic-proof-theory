{-# OPTIONS --safe --without-K #-}

module SPT.IR.Universal where

-- One induction–recursive type for all Dybjer–Setzer descriptions of
-- SPT.IR.Description: the universal type `U γ` and its decoding
-- `value γ`, defined together. Its constructor takes an argument datatype
-- `Args ε X v` with the subcode ε as a parameter, whose body (`Body`)
-- follows ε; so safe Agda accepts the recursion through the children at a
-- variable code. The realized laws compute at every code, by refl:
--
--   value γ (intro a) = out γ γ a                    (output-β)
--   ind γ P m (intro a) = m a (calls γ P m γ a)       (ind-β)
--   root γ (intro a) = a                             (root-β).
--
-- Arguments compare with the ordinary ones, `Shape` with output `Mark`,
-- with no extensionality: both inverse identities (`to`, `from`,
-- `from-to`, `to-from`), the outputs (`output-to`), the hypothesis types
-- (`hyp-to`) and the recursive calls (`calls-to`). At δ both sides keep
-- the complete child map. The argument constructors compute at an open
-- continuation (`nil`, `sig`, `del`; `out-δ`, `hyp-δ`, `calls-δ`), and
-- root recovery returns the child map itself (`selected`, `retains`).
-- Dybjer–Setzer's own induction rule is Universal.Induction.

open import SPT.Base

open import SPT.IR.Description using
  (Desc; ι; σ; δ; indexed; Shape; Mark)

------------------------------------------------------------------------
-- The universal type and its decoding

-- Mathematical shape:
--
--   intro : Args γ (U γ) (value γ) → U γ
--   Body (ι e) X v = 𝟙
--   Body (σ A H) X v = Σ (a : A). Args (H a) X v
--   Body (δ A H) X v = Σ (f : A → X). Args (H (v ∘ f)) X v.

mutual
  data U {s d : Level} {D : Set d} (γ : Desc {s = s} D) : Set s where
    intro : Args γ (U γ) (value γ) → U γ

  data Args {s d : Level} {D : Set d}
    (ε : Desc {s = s} D) (X : Set s) (v : X → D) : Set s where
    box : Body ε X v → Args ε X v

  Body :
    {s d : Level} {D : Set d} → Desc {s = s} D → (X : Set s) → (X → D)
    → Set s
  Body {s} (ι e) X v = Lift s 𝟙
  Body (σ A H) X v = Σ A (λ a → Args (H a) X v)
  Body (δ A H) X v = Σ (A → X) (λ f → Args (H (λ a → v (f a))) X v)

  value : {s d : Level} {D : Set d} (γ : Desc {s = s} D) → U γ → D
  value γ (intro a) = out γ γ a

  out :
    {s d : Level} {D : Set d} (γ ε : Desc {s = s} D)
    → Args ε (U γ) (value γ) → D
  out γ (ι e) (box a) = e
  out γ (σ A H) (box (a , b)) = out γ (H a) b
  out γ (δ A H) (box (f , b)) = out γ (H (λ a → value γ (f a))) b

output-β :
  {s d : Level} {D : Set d} (γ : Desc {s = s} D)
  (a : Args γ (U γ) (value γ)) → value γ (intro a) ＝ out γ γ a
output-β γ a = refl

------------------------------------------------------------------------
-- Comparison with ordinary arguments

-- The two presentations differ only by the box at each node; at δ both
-- keep the complete child map f.

to :
  {s d : Level} {D : Set d} (ε : Desc {s = s} D) (X : Set s) (v : X → D)
  → Shape ε (indexed X v) → Args ε X v
to (ι e) X v a = box a
to (σ A H) X v (a , b) = box (a , to (H a) X v b)
to (δ A H) X v (f , b) = box (f , to (H (λ a → v (f a))) X v b)

from :
  {s d : Level} {D : Set d} (ε : Desc {s = s} D) (X : Set s) (v : X → D)
  → Args ε X v → Shape ε (indexed X v)
from (ι e) X v (box a) = a
from (σ A H) X v (box (a , b)) = a , from (H a) X v b
from (δ A H) X v (box (f , b)) = f , from (H (λ a → v (f a))) X v b

from-to :
  {s d : Level} {D : Set d} (ε : Desc {s = s} D) (X : Set s) (v : X → D)
  (a : Shape ε (indexed X v)) → from ε X v (to ε X v a) ＝ a
from-to (ι e) X v a = refl
from-to (σ A H) X v (a , b) = ap (a ,_) (from-to (H a) X v b)
from-to (δ A H) X v (f , b) =
  ap (f ,_) (from-to (H (λ a → v (f a))) X v b)

to-from :
  {s d : Level} {D : Set d} (ε : Desc {s = s} D) (X : Set s) (v : X → D)
  (a : Args ε X v) → to ε X v (from ε X v a) ＝ a
to-from (ι e) X v (box a) = refl
to-from (σ A H) X v (box (a , b)) =
  ap (λ b′ → box (a , b′)) (to-from (H a) X v b)
to-from (δ A H) X v (box (f , b)) =
  ap (λ b′ → box (f , b′)) (to-from (H (λ a → v (f a))) X v b)

output-to :
  {s d : Level} {D : Set d} (γ ε : Desc {s = s} D)
  (a : Shape ε (indexed (U γ) (value γ)))
  → out γ ε (to ε (U γ) (value γ) a) ＝ Mark ε (indexed (U γ) (value γ)) a
output-to γ (ι e) a = refl
output-to γ (σ A H) (a , b) = output-to γ (H a) b
output-to γ (δ A H) (f , b) = output-to γ (H (λ a → value γ (f a))) b

------------------------------------------------------------------------
-- Hypotheses

-- Both hypothesis families use the same unit and pair types; at δ their
-- first component is the same function type.

Hyp :
  {s d ν : Level} {D : Set d} (ε : Desc {s = s} D) (X : Set s) (v : X → D)
  → (X → Set ν) → Args ε X v → Set (s ⊔ ν)
Hyp {s} {ν = ν} (ι e) X v P a = Lift (s ⊔ ν) 𝟙
Hyp (σ A H) X v P (box (a , b)) = Hyp (H a) X v P b
Hyp (δ A H) X v P (box (f , b)) =
  Σ ((a : A) → P (f a)) (λ _ → Hyp (H (λ a → v (f a))) X v P b)

Std-Hyp :
  {s d ν : Level} {D : Set d} (ε : Desc {s = s} D) (X : Set s) (v : X → D)
  → (X → Set ν) → Shape ε (indexed X v) → Set (s ⊔ ν)
Std-Hyp {s} {ν = ν} (ι e) X v P a = Lift (s ⊔ ν) 𝟙
Std-Hyp (σ A H) X v P (a , b) = Std-Hyp (H a) X v P b
Std-Hyp (δ A H) X v P (f , b) =
  Σ ((a : A) → P (f a)) (λ _ → Std-Hyp (H (λ a → v (f a))) X v P b)

hyp-to :
  {s d ν : Level} {D : Set d} (ε : Desc {s = s} D) (X : Set s) (v : X → D)
  (P : X → Set ν) (a : Shape ε (indexed X v))
  → Hyp ε X v P (to ε X v a) ＝ Std-Hyp ε X v P a
hyp-to (ι e) X v P a = refl
hyp-to (σ A H) X v P (a , b) = hyp-to (H a) X v P b
hyp-to (δ A H) X v P (f , b) =
  ap (λ R → Σ ((a : A) → P (f a)) (λ _ → R))
    (hyp-to (H (λ a → v (f a))) X v P b)

std-calls :
  {s d ν : Level} {D : Set d} (ε : Desc {s = s} D) (X : Set s) (v : X → D)
  (P : X → Set ν) → ((x : X) → P x) → (a : Shape ε (indexed X v))
  → Std-Hyp ε X v P a
std-calls (ι e) X v P h a = lift ⋆
std-calls (σ A H) X v P h (a , b) = std-calls (H a) X v P h b
std-calls (δ A H) X v P h (f , b) =
  (λ a → h (f a)) , std-calls (H (λ a → v (f a))) X v P h b

------------------------------------------------------------------------
-- Induction and the recursive calls

-- Mathematical shape:
--
--   Method γ P = Π (a : Args γ (U γ) (value γ)). Hyp γ … P a → P (intro a).

Method :
  {s d ν : Level} {D : Set d} (γ : Desc {s = s} D)
  → (U γ → Set ν) → Set (s ⊔ ν)
Method γ P =
  (a : Args γ (U γ) (value γ)) → Hyp γ (U γ) (value γ) P a → P (intro a)

mutual
  ind :
    {s d ν : Level} {D : Set d} (γ : Desc {s = s} D) (P : U γ → Set ν)
    → Method γ P → (u : U γ) → P u
  ind γ P m (intro a) = m a (calls γ P m γ a)

  calls :
    {s d ν : Level} {D : Set d} (γ : Desc {s = s} D) (P : U γ → Set ν)
    → Method γ P → (ε : Desc {s = s} D) (a : Args ε (U γ) (value γ))
    → Hyp ε (U γ) (value γ) P a
  calls γ P m (ι e) (box a) = lift ⋆
  calls γ P m (σ A H) (box (a , b)) = calls γ P m (H a) b
  calls γ P m (δ A H) (box (f , b)) =
    (λ a → ind γ P m (f a)) , calls γ P m (H (λ a → value γ (f a))) b

ind-β :
  {s d ν : Level} {D : Set d} (γ : Desc {s = s} D) (P : U γ → Set ν)
  (m : Method γ P) (a : Args γ (U γ) (value γ))
  → ind γ P m (intro a) ＝ m a (calls γ P m γ a)
ind-β γ P m a = refl

root :
  {s d : Level} {D : Set d} (γ : Desc {s = s} D)
  → U γ → Args γ (U γ) (value γ)
root γ = ind γ (λ _ → Args γ (U γ) (value γ)) (λ a _ → a)

root-β :
  {s d : Level} {D : Set d} (γ : Desc {s = s} D)
  (a : Args γ (U γ) (value γ)) → root γ (intro a) ＝ a
root-β γ a = refl

------------------------------------------------------------------------
-- The recursive calls compared with the ordinary ones

-- The native calls, transported along hyp-to, are the ordinary calls of
-- the induction itself. At δ the call function is literally the same;
-- the transport changes only the continuation.

private
  pair-transport :
    {α β : Level} (A : Set α) {B C : Set β} (e : B ＝ C) (a : A) (b : B)
    → transport id (ap (λ R → Σ A (λ _ → R)) e) (a , b)
      ＝ (a , transport id e b)
  pair-transport A refl a b = refl

calls-to :
  {s d ν : Level} {D : Set d} (γ : Desc {s = s} D) (P : U γ → Set ν)
  (m : Method γ P) (ε : Desc {s = s} D)
  (a : Shape ε (indexed (U γ) (value γ)))
  → transport id (hyp-to ε (U γ) (value γ) P a)
      (calls γ P m ε (to ε (U γ) (value γ) a))
    ＝ std-calls ε (U γ) (value γ) P (ind γ P m) a
calls-to γ P m (ι e) a = refl
calls-to γ P m (σ A H) (a , b) = calls-to γ P m (H a) b
calls-to γ P m (δ A H) (f , b) =
  pair-transport ((a : A) → P (f a))
    (hyp-to (H (λ a → value γ (f a))) (U γ) (value γ) P b)
    (λ a → ind γ P m (f a))
    (calls γ P m (H (λ a → value γ (f a)))
      (to (H (λ a → value γ (f a))) (U γ) (value γ) b))
  ∙ ap ((λ a → ind γ P m (f a)) ,_)
      (calls-to γ P m (H (λ a → value γ (f a))) b)

------------------------------------------------------------------------
-- The argument constructors at an open continuation

nil :
  {s d : Level} {D : Set d} (X : Set s) (v : X → D) (e : D)
  → Args {s = s} (ι e) X v
nil X v e = box (lift ⋆)

sig :
  {s d : Level} {D : Set d} (X : Set s) (v : X → D)
  (A : Set s) (H : A → Desc {s = s} D) (a : A)
  → Args (H a) X v → Args (σ A H) X v
sig X v A H a b = box (a , b)

del :
  {s d : Level} {D : Set d} (X : Set s) (v : X → D)
  (A : Set s) (H : (A → D) → Desc {s = s} D) (f : A → X)
  → Args (H (λ a → v (f a))) X v → Args (δ A H) X v
del X v A H f b = box (f , b)

out-δ :
  {s d : Level} {D : Set d} (γ : Desc {s = s} D)
  (A : Set s) (H : (A → D) → Desc {s = s} D) (f : A → U γ)
  (b : Args (H (λ a → value γ (f a))) (U γ) (value γ))
  → out γ (δ A H) (del (U γ) (value γ) A H f b)
    ＝ out γ (H (λ a → value γ (f a))) b
out-δ γ A H f b = refl

hyp-δ :
  {s d ν : Level} {D : Set d} (γ : Desc {s = s} D) (P : U γ → Set ν)
  (A : Set s) (H : (A → D) → Desc {s = s} D) (f : A → U γ)
  (b : Args (H (λ a → value γ (f a))) (U γ) (value γ))
  → Hyp (δ A H) (U γ) (value γ) P (del (U γ) (value γ) A H f b)
    ＝ Σ ((a : A) → P (f a))
        (λ _ → Hyp (H (λ a → value γ (f a))) (U γ) (value γ) P b)
hyp-δ γ P A H f b = refl

calls-δ :
  {s d ν : Level} {D : Set d} (γ : Desc {s = s} D) (P : U γ → Set ν)
  (m : Method γ P) (A : Set s) (H : (A → D) → Desc {s = s} D)
  (f : A → U γ) (b : Args (H (λ a → value γ (f a))) (U γ) (value γ))
  → calls γ P m (δ A H) (del (U γ) (value γ) A H f b)
    ＝ ((λ a → ind γ P m (f a)) ,
        calls γ P m (H (λ a → value γ (f a))) b)
calls-δ γ P m A H f b = refl

------------------------------------------------------------------------
-- Root recovery keeps the child map

selected :
  {s d : Level} {D : Set d} (X : Set s) (v : X → D)
  (A : Set s) (H : (A → D) → Desc {s = s} D) → Args (δ A H) X v → A → X
selected X v A H (box (f , b)) = f

retains :
  {s d : Level} {D : Set d} (A : Set s) (H : (A → D) → Desc {s = s} D)
  (f : A → U (δ A H))
  (b : Args (H (λ a → value (δ A H) (f a))) (U (δ A H)) (value (δ A H)))
  → selected (U (δ A H)) (value (δ A H)) A H
      (root (δ A H) (intro (del (U (δ A H)) (value (δ A H)) A H f b)))
    ＝ f
retains A H f b = refl
