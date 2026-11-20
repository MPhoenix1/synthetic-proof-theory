{-# OPTIONS --safe --without-K #-}

module SPT.IR.Indexed.Comparison where

-- The arguments of IR.Indexed against the ordinary arguments of
-- IR.Polynomial over the universal family, under extensionality
-- for families of information over the arities. By recursion on the code
-- they are isomorphic, keeping information (`arguments`, `kept`,
-- `from-info`): the identity at inputs and constants, SPT's `Σ-bicong`
-- over the isomorphism of first parts at a sum, and `Π-cong` at a
-- product, where extensionality, lowered to small families (`lowered`),
-- identifies the two informations, separate recursions under one binder.
-- So introduction on ordinary arguments has its
-- decoding equation as an identity (`make`, `make-β`), the universal
-- family is an algebra of every scheme (`algebra`), and introduction is
-- invertible (`root`, `root-β`, `section`).

open import SPT.Base
open import SPT.Foundation.HalfAdjoint using (Σ-bicong)
open import SPT.Foundation.Isomorphisms using
  (_≅_; forward; backward; backward-forward; forward-backward; ≅-refl;
   ≅-trans; transport-is-isomorphism; Π-cong)

open import SPT.IR.Indexed using (U; Args; intro; info; value; family)
import SPT.IR.Indexed as Indexed
open import SPT.IR.Polynomial using
  (Poly; var; con; sigma; pi; Scheme; shape; output; Extensionality;
   lowered)
import SPT.IR.Polynomial as Polynomial
open import SPT.IR.Polynomial.Action using (pair-info)
open import SPT.IR.Polynomial.Algebra using (Algebra)

------------------------------------------------------------------------
-- The comparison of arguments

-- At inputs and constants the two arguments are the same type. At a sum
-- the continuation is read at the native information on one side and at
-- the ordinary information of the image on the other, so the second
-- parts meet along `kept` at the first part. At a product the parts
-- compare pointwise, and the informations are two functions agreeing at
-- every point.

module _
  {ℓ κ : Level} (extensionality : Extensionality ℓ κ) (s : Scheme ℓ κ)
  where

  mutual
    arguments :
      {X : Set (ℓ ⊔ κ)} (p : Poly ℓ κ (Scheme.Data s) X)
      → Args s p ≅ Polynomial.Args p (family s)
    arguments (var i) = ≅-refl
    arguments (con A) = ≅-refl
    arguments (sigma p q) =
      Σ-bicong
        (λ a → Args s (q (info s p a)))
        (λ b →
          Polynomial.Args (q (Polynomial.info p (family s) b)) (family s))
        (arguments p)
        (λ a →
          ≅-trans (arguments (q (info s p a)))
            ( transport-is-isomorphism
                (λ x → Polynomial.Args (q x) (family s)) (kept p a ⁻¹)))
    arguments (pi A p) =
      Π-cong
        (lowered κ extensionality A (λ a → Args s (p a)))
        (lowered κ extensionality A (λ a → Polynomial.Args (p a) (family s)))
        (λ a → arguments (p a))

    kept :
      {X : Set (ℓ ⊔ κ)} (p : Poly ℓ κ (Scheme.Data s) X) (a : Args s p)
      → Polynomial.info p (family s) (forward (arguments p) a) ＝ info s p a
    kept (var i) a = refl
    kept (con A) a = refl
    kept (sigma {X} {Y} p q) (a , b) =
      pair-info (λ x → Polynomial.Args (q x) (family s)) Y
        (λ x → Polynomial.info (q x) (family s)) (kept p a ⁻¹)
        (forward (arguments (q (info s p a))) b)
      ∙ ap (λ y → (info s p a , y)) (kept (q (info s p a)) b)
    kept (pi A {Y} p) f =
      extensionality A Y
        ( λ x →
            Polynomial.info (p x) (family s) (forward (arguments (p x)) (f x)))
        (λ x → info s (p x) (f x))
        (λ x → kept (p x) (f x))

  from-info :
    {X : Set (ℓ ⊔ κ)} (p : Poly ℓ κ (Scheme.Data s) X)
    (b : Polynomial.Args p (family s))
    → info s p (backward (arguments p) b) ＝ Polynomial.info p (family s) b
  from-info p b =
    kept p (backward (arguments p) b) ⁻¹
    ∙ ap (Polynomial.info p (family s)) (forward-backward (arguments p) b)

------------------------------------------------------------------------
-- Introduction on ordinary arguments

-- An ordinary argument is introduced through its native argument. Its
-- decoding equation is an identity, so the universal family is an
-- algebra of every scheme, and root recovery inverts introduction.

module _
  {ℓ κ : Level} (extensionality : Extensionality ℓ κ) (s : Scheme ℓ κ)
  where

  make :
    (i : Scheme.Index s)
    → Polynomial.Args (shape (Scheme.rule s i)) (family s) → U s i
  make i b =
    intro
      (backward (arguments extensionality s (shape (Scheme.rule s i))) b)

  make-β :
    (i : Scheme.Index s)
    (b : Polynomial.Args (shape (Scheme.rule s i)) (family s))
    → value s i (make i b)
      ＝ output (Scheme.rule s i)
          (Polynomial.info (shape (Scheme.rule s i)) (family s) b)
  make-β i b =
    ap (output (Scheme.rule s i))
      (from-info extensionality s (shape (Scheme.rule s i)) b)

  algebra : Algebra s
  algebra = record { family = family s ; operation = make ; law = make-β }

  root :
    (i : Scheme.Index s) → U s i
    → Polynomial.Args (shape (Scheme.rule s i)) (family s)
  root i u =
    forward (arguments extensionality s (shape (Scheme.rule s i)))
      (Indexed.root s i u)

  root-β :
    (i : Scheme.Index s)
    (b : Polynomial.Args (shape (Scheme.rule s i)) (family s))
    → root i (make i b) ＝ b
  root-β i b =
    forward-backward (arguments extensionality s (shape (Scheme.rule s i))) b

  section : (i : Scheme.Index s) (u : U s i) → make i (root i u) ＝ u
  section i (intro a) =
    ap intro
      ( backward-forward
          (arguments extensionality s (shape (Scheme.rule s i))) a)
