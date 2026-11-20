{-# OPTIONS --safe --without-K #-}

module SPT.IR.Indexed.General where

-- Dybjer–Setzer's general indexed induction–recursion (Indexed
-- induction–recursion, JLAP 2006, §4.7, §4.8) on the universal family of
-- IR.Indexed, with no extensionality. A general code γ of
-- IR.Description.Indexed is the scheme `general γ`, whose carriers and
-- readouts are U and value. At ι, σ and δ the native arguments of the
-- polynomial code are the ordinary ones, so the comparison is the identity
-- at every clause (`to`, `from`, `from-to`, `to-from`); it keeps outputs
-- (`output-to`) and hypotheses (`hyp-forward`, `calls-to`). A native
-- argument at an index is an argument of the code with an identification of
-- the index it computes, so native introduction and induction make the
-- universal family an inductive family of γ, its readout law and its
-- computation identity by refl (`universal`, `universal-computation`), and
-- IR.General's rules hold on it: introduction at the computed index, with
-- the decoding equation, and the elimination rule with its computation
-- equation,
--
--   value (pr₁ (Mark γ Z x)) (intro x) ＝ pr₂ (Mark γ Z x),
--   ind m (pr₁ (Mark γ Z x)) (intro x) ＝ m x (map-IH γ Z P (ind m) x),
--
-- Z the universal family, `intro`, `ind` those of `universal γ`. Every
-- identification here is built from refl by induction on the code, with no
-- extensionality and no free identification; at closed codes the equations
-- compute (Indexed.General.Discriminator).

open import SPT.Base
open import SPT.IR.General using (Inductive-Family; Computation)
open import SPT.IR.Polynomial using (Scheme; shape)
open import SPT.IR.Description.Indexed using
  (IDS; ι; σ; δ; General; Shape; Mark; IH; map-IH; polynomial; result;
   general)
open import SPT.IR.Indexed using
  (U; Args; info; value; Hyp; calls; family)
import SPT.IR.Indexed as Indexed

------------------------------------------------------------------------
-- Ordinary and native arguments

-- The information of a constant is its lift, and that of a product of
-- inputs is the function of their readouts, both by computation. So at
-- every clause the native argument is the ordinary one.

module _
  {ε ℓ κ : Level} (s : Scheme ℓ κ) {E : Set ε}
  where

  to :
    (γ : IDS ℓ κ (Scheme.Index s) (Scheme.Data s) E)
    → Shape γ (family s) → Args s (polynomial γ)
  to (ι e) x = x
  to (σ A f) (a , x) = a , to (f a) x
  to (δ A i F) (g , x) = g , to (F (λ a → value s (i a) (g a))) x

  from :
    (γ : IDS ℓ κ (Scheme.Index s) (Scheme.Data s) E)
    → Args s (polynomial γ) → Shape γ (family s)
  from (ι e) y = y
  from (σ A f) (a , y) = a , from (f a) y
  from (δ A i F) (g , y) = g , from (F (λ a → value s (i a) (g a))) y

  from-to :
    (γ : IDS ℓ κ (Scheme.Index s) (Scheme.Data s) E)
    (x : Shape γ (family s)) → from γ (to γ x) ＝ x
  from-to (ι e) x = refl
  from-to (σ A f) (a , x) = ap (a ,_) (from-to (f a) x)
  from-to (δ A i F) (g , x) =
    ap (g ,_) (from-to (F (λ a → value s (i a) (g a))) x)

  to-from :
    (γ : IDS ℓ κ (Scheme.Index s) (Scheme.Data s) E)
    (y : Args s (polynomial γ)) → to γ (from γ y) ＝ y
  to-from (ι e) y = refl
  to-from (σ A f) (a , y) = ap (a ,_) (to-from (f a) y)
  to-from (δ A i F) (g , y) =
    ap (g ,_) (to-from (F (λ a → value s (i a) (g a))) y)

  output-to :
    (γ : IDS ℓ κ (Scheme.Index s) (Scheme.Data s) E)
    (x : Shape γ (family s))
    → result γ (info s (polynomial γ) (to γ x)) ＝ Mark γ (family s) x
  output-to (ι e) x = refl
  output-to (σ A f) (a , x) = output-to (f a) x
  output-to (δ A i F) (g , x) =
    output-to (F (λ a → value s (i a) (g a))) x

------------------------------------------------------------------------
-- Hypotheses

-- The native hypotheses at the ordinary argument give the ordinary ones,
-- past the unit of a constant at σ and out of the lift at each input at
-- δ. The native calls go to the ordinary calls of the induction itself.

module _
  {ε ℓ κ ν : Level} (s : Scheme ℓ κ) {E : Set ε}
  (P : (i : Scheme.Index s) → U s i → Set ν)
  where

  hyp-forward :
    (γ : IDS ℓ κ (Scheme.Index s) (Scheme.Data s) E)
    (x : Shape γ (family s))
    → Hyp s P (polynomial γ) (to s γ x) → IH γ (family s) P x
  hyp-forward (ι e) x h = h
  hyp-forward (σ A f) (a , x) (h , k) = hyp-forward (f a) x k
  hyp-forward (δ A i F) (g , x) (h , k) =
    (λ a → lower (h a)) ,
    hyp-forward (F (λ a → value s (i a) (g a))) x k

  calls-to :
    (m : Indexed.Method s P)
    (γ : IDS ℓ κ (Scheme.Index s) (Scheme.Data s) E)
    (x : Shape γ (family s))
    → hyp-forward γ x (calls s P m (polynomial γ) (to s γ x))
      ＝ map-IH γ (family s) P (Indexed.ind s P m) x
  calls-to m (ι e) x = refl
  calls-to m (σ A f) (a , x) = calls-to m (f a) x
  calls-to m (δ A i F) (g , x) =
    ap ((λ a → Indexed.ind s P m (i a) (g a)) ,_)
      (calls-to m (F (λ a → value s (i a) (g a))) x)

------------------------------------------------------------------------
-- The universal family as an inductive family of a general code

-- Native introduction takes an argument of the code with an identification
-- of the index it computes, which is a located argument; native induction
-- is induction on them, and the native hypotheses at a located argument
-- are those at its argument, past the unit at the identification.

module _
  {ℓ κ : Level} {I : Set ℓ} {D : I → Set (ℓ ⊔ κ)} (γ : General ℓ κ I D)
  where

  universal : Inductive-Family γ
  universal = record
    { family = family (general γ)
    ; Arguments = Args (general γ) (polynomial γ)
    ; information = info (general γ) (polynomial γ)
    ; to = to (general γ) γ
    ; from = from (general γ) γ
    ; from-to = from-to (general γ) γ
    ; to-from = to-from (general γ) γ
    ; output-to = output-to (general γ) γ
    ; make = λ i b → Indexed.intro b
    ; make-β = λ i y e → refl
    ; Hypotheses = λ P i b →
        Hyp (general γ) P (shape (Scheme.rule (general γ) i)) b
    ; induction = λ P → Indexed.ind (general γ) P
    ; calls = λ P m i b →
        calls (general γ) P m (shape (Scheme.rule (general γ) i)) b
    ; hyp-forward = λ P x h → hyp-forward (general γ) P γ x (pr₁ h)
    ; calls-forward = λ P m x → calls-to (general γ) P m γ x
    }

  universal-computation :
    {ν : Level} (P : (i : I) → U (general γ) i → Set ν)
    → Computation universal P
  universal-computation P m i b = refl
