{-# OPTIONS --safe --without-K #-}

module SPT.IR.Indexed.Induction where

-- Induction for ordinary arguments over the universal family of
-- IR.Indexed, from its native induction, under extensionality for
-- families of information over the arities. The hypotheses at an ordinary
-- argument are the native hypotheses at its native argument, the pullback
-- of native induction along the comparison (`Hypothesis`). A method on
-- ordinary arguments (`Method`) is carried to a native one through the
-- half-adjoint coherence of the comparison (`Fiber`, `method`,
-- `method-β`), and the computation equation holds as an identity at every
-- scheme, motive, method and argument (`ind`, `hypotheses`, `ind-β`):
--
--   ind m i (make i b) ＝ m i b (hypotheses m i b).

open import SPT.Base
open import SPT.Foundation.HalfAdjoint.Extension using
  (extension; extension-β)
open import SPT.Foundation.Isomorphisms using
  (backward; ≅-sym)

open import SPT.IR.Indexed using (U; Args; intro; Hyp; family)
import SPT.IR.Indexed as Indexed
open import SPT.IR.Indexed.Comparison using (arguments; make)
open import SPT.IR.Polynomial using
  (Scheme; shape; Extensionality)
import SPT.IR.Polynomial as Polynomial

------------------------------------------------------------------------
-- Induction on ordinary arguments

-- Nonclaim: the hypotheses are not recomputed from the ordinary argument.
-- A recursion on it would compare with the native one at products only
-- through extensionality at the level of the motive.

module _
  {ℓ κ ν : Level} (extensionality : Extensionality ℓ κ) (s : Scheme ℓ κ)
  (P : (i : Scheme.Index s) → U s i → Set ν)
  where

  Hypothesis :
    (i : Scheme.Index s)
    → Polynomial.Args (shape (Scheme.rule s i)) (family s) → Set (ℓ ⊔ ν)
  Hypothesis i b =
    Hyp s P (shape (Scheme.rule s i))
      (backward (arguments extensionality s (shape (Scheme.rule s i))) b)

  Method : Set (ℓ ⊔ ν)
  Method =
    (i : Scheme.Index s)
    (b : Polynomial.Args (shape (Scheme.rule s i)) (family s))
    → Hypothesis i b → P i (make extensionality s i b)

  -- The native method type at an argument a is its hypotheses with its
  -- result. An ordinary method gives it at every native image of an
  -- ordinary argument, and is carried to every a along the adjusted
  -- inverse law (Foundation.HalfAdjoint.Extension); at a native image,
  -- the half-adjoint triangle and dependent application return the
  -- ordinary method.

  Fiber :
    (i : Scheme.Index s) → Args s (shape (Scheme.rule s i)) → Set (ℓ ⊔ ν)
  Fiber i a = Hyp s P (shape (Scheme.rule s i)) a → P i (intro a)

  method : Method → Indexed.Method s P
  method m i a =
    extension (≅-sym (arguments extensionality s (shape (Scheme.rule s i))))
      (Fiber i) (m i) a

  method-β :
    (m : Method) (i : Scheme.Index s)
    (b : Polynomial.Args (shape (Scheme.rule s i)) (family s))
    → method m i
        (backward (arguments extensionality s (shape (Scheme.rule s i))) b)
      ＝ m i b
  method-β m i b =
    extension-β
      (≅-sym (arguments extensionality s (shape (Scheme.rule s i))))
      (Fiber i) (m i) b

  -- Induction is native induction at the transferred method, and its
  -- computation equation at an introduced argument is method-β.

  ind : Method → (i : Scheme.Index s) (u : U s i) → P i u
  ind m = Indexed.ind s P (method m)

  hypotheses :
    (m : Method) (i : Scheme.Index s)
    (b : Polynomial.Args (shape (Scheme.rule s i)) (family s))
    → Hypothesis i b
  hypotheses m i b =
    Indexed.calls s P (method m) (shape (Scheme.rule s i))
      (backward (arguments extensionality s (shape (Scheme.rule s i))) b)

  ind-β :
    (m : Method) (i : Scheme.Index s)
    (b : Polynomial.Args (shape (Scheme.rule s i)) (family s))
    → ind m i (make extensionality s i b) ＝ m i b (hypotheses m i b)
  ind-β m i b = ap (λ k → k (hypotheses m i b)) (method-β m i b)
