{-# OPTIONS --safe --without-K #-}

module SPT.IR.Universal.Induction where

-- Dybjer–Setzer's induction rule for the universal type of
-- IR.Universal, from its native induction, with no extensionality.
-- Introduction takes an ordinary argument (`intro`), and a method an
-- ordinary argument with its ordinary hypotheses (`Method`). The argument
-- comparison is an isomorphism (`arguments`), and its half-adjoint
-- coherence carries a method to a native one, transporting the whole
-- dependent method type at once (`Fiber`, `prepared`, `method`,
-- `method-β`). The computation equation holds for every description,
-- motive, method and argument (`ind-β`):
--
--   ind γ P m (intro γ a) ＝ m a (std-calls γ (U γ) (value γ) P (ind γ P m) a).
--
-- Induction recovers the ordinary argument of every element with its
-- identification (`recover`, `recover-β`), so introduction has a section
-- (`root`, `root-β`, `section`).

open import SPT.Base
open import SPT.Foundation.HalfAdjoint.Extension using
  (extension; extension-β)
open import SPT.Foundation.Isomorphisms using (_≅_)

open import SPT.IR.Universal using
  (U; Args; value; to; from; from-to; to-from; Hyp; Std-Hyp; hyp-to;
   std-calls; calls; calls-to)
import SPT.IR.Universal as Universal
open import SPT.IR.Description using (Desc; indexed; Shape)

------------------------------------------------------------------------
-- The comparison of arguments as an isomorphism

arguments :
  {s d : Level} {D : Set d} (ε : Desc {s = s} D) (X : Set s) (v : X → D)
  → Shape ε (indexed X v) ≅ Args ε X v
arguments ε X v = record
  { forward = to ε X v
  ; backward = from ε X v
  ; backward-forward = from-to ε X v
  ; forward-backward = to-from ε X v
  }

------------------------------------------------------------------------
-- Introduction and methods on ordinary arguments

intro :
  {s d : Level} {D : Set d} (γ : Desc {s = s} D)
  → Shape γ (indexed (U γ) (value γ)) → U γ
intro γ a = Universal.intro (to γ (U γ) (value γ) a)

Method :
  {s d ν : Level} {D : Set d} (γ : Desc {s = s} D)
  → (U γ → Set ν) → Set (s ⊔ ν)
Method γ P =
  (a : Shape γ (indexed (U γ) (value γ)))
  → Std-Hyp γ (U γ) (value γ) P a → P (intro γ a)

------------------------------------------------------------------------
-- Transfer to the native method

-- The whole dependent method type at a native argument b is its
-- hypothesis domain with its result. A method is prepared at `to a` by
-- reading the native hypotheses along hyp-to, then carried to every b
-- along the adjusted inverse law; at `to a` the half-adjoint triangle and
-- dependent application return the prepared method.

Fiber :
  {s d ν : Level} {D : Set d} (γ : Desc {s = s} D) (P : U γ → Set ν)
  → Args γ (U γ) (value γ) → Set (s ⊔ ν)
Fiber γ P b = Hyp γ (U γ) (value γ) P b → P (Universal.intro b)

prepared :
  {s d ν : Level} {D : Set d} (γ : Desc {s = s} D) (P : U γ → Set ν)
  → Method γ P → (a : Shape γ (indexed (U γ) (value γ)))
  → Fiber γ P (to γ (U γ) (value γ) a)
prepared γ P m a h = m a (transport id (hyp-to γ (U γ) (value γ) P a) h)

method :
  {s d ν : Level} {D : Set d} (γ : Desc {s = s} D) (P : U γ → Set ν)
  → Method γ P → Universal.Method γ P
method γ P m b =
  extension (arguments γ (U γ) (value γ)) (Fiber γ P) (prepared γ P m) b

method-β :
  {s d ν : Level} {D : Set d} (γ : Desc {s = s} D) (P : U γ → Set ν)
  (m : Method γ P) (a : Shape γ (indexed (U γ) (value γ)))
  → method γ P m (to γ (U γ) (value γ) a) ＝ prepared γ P m a
method-β γ P m a =
  extension-β (arguments γ (U γ) (value γ)) (Fiber γ P) (prepared γ P m) a

------------------------------------------------------------------------
-- Dybjer–Setzer induction and its computation equation

ind :
  {s d ν : Level} {D : Set d} (γ : Desc {s = s} D) (P : U γ → Set ν)
  → Method γ P → (u : U γ) → P u
ind γ P m = Universal.ind γ P (method γ P m)

ind-β :
  {s d ν : Level} {D : Set d} (γ : Desc {s = s} D) (P : U γ → Set ν)
  (m : Method γ P) (a : Shape γ (indexed (U γ) (value γ)))
  → ind γ P m (intro γ a)
    ＝ m a (std-calls γ (U γ) (value γ) P (ind γ P m) a)
ind-β γ P m a =
  ap (λ k → k (calls γ P (method γ P m) γ (to γ (U γ) (value γ) a)))
    (method-β γ P m a)
  ∙ ap (m a) (calls-to γ P (method γ P m) γ a)

------------------------------------------------------------------------
-- Recovery of the ordinary argument

-- The motive pairs an ordinary argument with an identification of its
-- introduction with the element; its method returns the argument itself.

Source :
  {s d : Level} {D : Set d} (γ : Desc {s = s} D) → U γ → Set s
Source γ u = Σ (Shape γ (indexed (U γ) (value γ))) (λ a → intro γ a ＝ u)

recovered :
  {s d : Level} {D : Set d} (γ : Desc {s = s} D) → Method γ (Source γ)
recovered γ a h = a , refl

recover :
  {s d : Level} {D : Set d} (γ : Desc {s = s} D) (u : U γ) → Source γ u
recover γ = ind γ (Source γ) (recovered γ)

recover-β :
  {s d : Level} {D : Set d} (γ : Desc {s = s} D)
  (a : Shape γ (indexed (U γ) (value γ)))
  → recover γ (intro γ a) ＝ (a , refl)
recover-β γ a = ind-β γ (Source γ) (recovered γ) a

root :
  {s d : Level} {D : Set d} (γ : Desc {s = s} D)
  → U γ → Shape γ (indexed (U γ) (value γ))
root γ u = pr₁ (recover γ u)

root-β :
  {s d : Level} {D : Set d} (γ : Desc {s = s} D)
  (a : Shape γ (indexed (U γ) (value γ))) → root γ (intro γ a) ＝ a
root-β γ a = ap pr₁ (recover-β γ a)

section :
  {s d : Level} {D : Set d} (γ : Desc {s = s} D) (u : U γ)
  → intro γ (root γ u) ＝ u
section γ u = pr₂ (recover γ u)
