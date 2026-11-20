{-# OPTIONS --safe --without-K #-}

module SPT.IR.Indexed.Induction.Initiality where

-- Pointwise initiality of induction on ordinary arguments
-- (IR.Indexed.Induction). Ordinary induction is native induction at the
-- transferred method, so a valuation with the lax law is related to it at
-- every element by Initiality's relational uniqueness there, itself
-- Foundation.Tree.Fold.Initiality's at the derivations (`Lax`,
-- `ind-unique-rel`). The ordinary law is the native law at the images of
-- ordinary arguments, so it holds of the transferred method at every
-- native argument (`Lawful`, `native-law`, by HalfAdjoint.Extension).
-- Instances: the fundamental theorem (`ind-rel`), uniqueness for
-- congruent methods (`ind-unique`, `ind-homomorphic`) and fusion
-- (`ind-fusion`). At a native method it is native induction (`ordinary`,
-- `agrees-with-native`).

open import SPT.Base
open import SPT.Foundation.HalfAdjoint.Extension using
  (extension-preserves-predicates)
open import SPT.Foundation.Isomorphisms using (backward; ≅-sym)

open import SPT.IR.Indexed using (U; family)
import SPT.IR.Indexed as Indexed
open import SPT.IR.Indexed.Comparison using (arguments; make)
open import SPT.IR.Indexed.Induction using
  (Hypothesis; Method; Fiber; method; ind; hypotheses; ind-β)
open import SPT.IR.Indexed.Initiality using
  ( values; Lifted; values-to-calls
  ; Identical; calls-agree; agreement; mapped; Graph; graph-agreement)
import SPT.IR.Indexed.Initiality as Initiality
open import SPT.IR.Polynomial using
  (Scheme; shape; Extensionality)
import SPT.IR.Polynomial as Polynomial

------------------------------------------------------------------------
-- Relational uniqueness

-- The lax law of a valuation v for ordinary methods m: at every ordinary
-- argument, the method at any hypotheses related to v at the children of
-- its native argument is related to v at the introduced element. Ordinary
-- induction is native induction at the transferred method, so the proof
-- is Initiality's relational uniqueness there. Its lax law is a predicate
-- on the fibers at each native argument (`Lawful`); the ordinary law is
-- that predicate at the images of ordinary arguments, and the extension
-- that transfers the method carries it to every native argument
-- (`native-law`, by `extension-preserves-predicates`).

module _
  {ℓ κ ν μ γ : Level} (extensionality : Extensionality ℓ κ)
  (s : Scheme ℓ κ) (Q : (i : Scheme.Index s) → U s i → Set μ)
  (P : (i : Scheme.Index s) → U s i → Set ν)
  (C : (i : Scheme.Index s) (u : U s i) → Q i u → P i u → Set γ)
  where

  Lax :
    ((i : Scheme.Index s) (u : U s i) → Q i u) → Method extensionality s P
    → Set (ℓ ⊔ ν ⊔ γ)
  Lax v m =
    (i : Scheme.Index s)
    (b : Polynomial.Args (shape (Scheme.rule s i)) (family s))
    (k : Hypothesis extensionality s P i b)
    → Lifted s Q P C (shape (Scheme.rule s i))
        (backward (arguments extensionality s (shape (Scheme.rule s i))) b)
        (values s Q v (shape (Scheme.rule s i))
          (backward (arguments extensionality s (shape (Scheme.rule s i))) b))
        k
    → C i (make extensionality s i b) (v i (make extensionality s i b))
        (m i b k)

module _
  {ℓ κ ν μ γ : Level} (extensionality : Extensionality ℓ κ)
  (s : Scheme ℓ κ) (Q : (i : Scheme.Index s) → U s i → Set μ)
  (P : (i : Scheme.Index s) → U s i → Set ν)
  (C : (i : Scheme.Index s) (u : U s i) → Q i u → P i u → Set γ)
  (v : (i : Scheme.Index s) (u : U s i) → Q i u)
  where

  Lawful :
    (i : Scheme.Index s) (a : Indexed.Args s (shape (Scheme.rule s i)))
    → Fiber extensionality s P i a → Set (ℓ ⊔ ν ⊔ γ)
  Lawful i a f =
    (k : Indexed.Hyp s P (shape (Scheme.rule s i)) a)
    → Lifted s Q P C (shape (Scheme.rule s i)) a
        (values s Q v (shape (Scheme.rule s i)) a) k
    → C i (Indexed.intro a) (v i (Indexed.intro a)) (f k)

module _
  {ℓ κ ν μ γ : Level} (extensionality : Extensionality ℓ κ)
  (s : Scheme ℓ κ) (Q : (i : Scheme.Index s) → U s i → Set μ)
  (P : (i : Scheme.Index s) → U s i → Set ν)
  (C : (i : Scheme.Index s) (u : U s i) → Q i u → P i u → Set γ)
  (v : (i : Scheme.Index s) (u : U s i) → Q i u)
  (m : Method extensionality s P) (law : Lax extensionality s Q P C v m)
  where

  native-law : Initiality.Lax s Q P C v (method extensionality s P m)
  native-law i =
    extension-preserves-predicates
      (≅-sym (arguments extensionality s (shape (Scheme.rule s i))))
      (Fiber extensionality s P i) (m i) (Lawful extensionality s Q P C v i)
      (law i)

  ind-unique-rel :
    (i : Scheme.Index s) (u : U s i)
    → C i u (v i u) (ind extensionality s P m i u)
  ind-unique-rel =
    Initiality.ind-unique-rel s Q P C v (method extensionality s P m)
      native-law

------------------------------------------------------------------------
-- The fundamental theorem

-- Methods related at related hypotheses have related inductions: the
-- values of an induction are its calls at every child, and ind-β moves the
-- first method's value to its induction.

module _
  {ℓ κ ν μ γ : Level} (extensionality : Extensionality ℓ κ)
  (s : Scheme ℓ κ) (Q : (i : Scheme.Index s) → U s i → Set μ)
  (P : (i : Scheme.Index s) → U s i → Set ν)
  (C : (i : Scheme.Index s) (u : U s i) → Q i u → P i u → Set γ)
  (n : Method extensionality s Q) (m : Method extensionality s P)
  where

  Relational : Set (ℓ ⊔ ν ⊔ μ ⊔ γ)
  Relational =
    (i : Scheme.Index s)
    (b : Polynomial.Args (shape (Scheme.rule s i)) (family s))
    (h : Hypothesis extensionality s Q i b)
    (k : Hypothesis extensionality s P i b)
    → Lifted s Q P C (shape (Scheme.rule s i))
        (backward (arguments extensionality s (shape (Scheme.rule s i))) b)
        h k
    → C i (make extensionality s i b) (n i b h) (m i b k)

  ind-rel :
    Relational → (i : Scheme.Index s) (u : U s i)
    → C i u (ind extensionality s Q n i u) (ind extensionality s P m i u)
  ind-rel related =
    ind-unique-rel extensionality s Q P C (ind extensionality s Q n) m
      ( λ i b k r →
          transport (λ y → C i (make extensionality s i b) y (m i b k))
            (ind-β extensionality s Q n i b ⁻¹)
            (related i b (hypotheses extensionality s Q n i b) k
              (values-to-calls s Q P C (method extensionality s Q n)
                (shape (Scheme.rule s i))
                (backward
                  (arguments extensionality s (shape (Scheme.rule s i))) b)
                k r)))

------------------------------------------------------------------------
-- Uniqueness

-- Congruence and the computation equations are read at the native
-- argument. A valuation satisfying the equations of congruent methods is
-- their induction at every element; induction satisfies them by ind-β,
-- since its hypotheses agree with its values at every child.

module _
  {ℓ κ ν : Level} (extensionality : Extensionality ℓ κ) (s : Scheme ℓ κ)
  (P : (i : Scheme.Index s) → U s i → Set ν)
  where

  Congruent : Method extensionality s P → Set (ℓ ⊔ ν)
  Congruent m =
    (i : Scheme.Index s)
    (b : Polynomial.Args (shape (Scheme.rule s i)) (family s))
    (h k : Hypothesis extensionality s P i b)
    → Lifted s P P (Identical s P) (shape (Scheme.rule s i))
        (backward (arguments extensionality s (shape (Scheme.rule s i))) b)
        h k
    → m i b h ＝ m i b k

  Homomorphic :
    ((i : Scheme.Index s) (u : U s i) → P i u) → Method extensionality s P
    → Set (ℓ ⊔ ν)
  Homomorphic v m =
    (i : Scheme.Index s)
    (b : Polynomial.Args (shape (Scheme.rule s i)) (family s))
    → v i (make extensionality s i b)
      ＝ m i b
          (values s P v (shape (Scheme.rule s i))
            (backward
              (arguments extensionality s (shape (Scheme.rule s i))) b))

  ind-unique :
    (v : (i : Scheme.Index s) (u : U s i) → P i u)
    (m : Method extensionality s P) → Congruent m → Homomorphic v m
    → (i : Scheme.Index s) (u : U s i) → v i u ＝ ind extensionality s P m i u
  ind-unique v m congruence equations =
    ind-unique-rel extensionality s P P (Identical s P) v m
      ( λ i b k r →
          equations i b
          ∙ congruence i b
              (values s P v (shape (Scheme.rule s i))
                (backward
                  (arguments extensionality s (shape (Scheme.rule s i))) b))
              k r)

  ind-homomorphic :
    (m : Method extensionality s P) → Congruent m
    → Homomorphic (ind extensionality s P m) m
  ind-homomorphic m congruence i b =
    ind-β extensionality s P m i b
    ∙ congruence i b (hypotheses extensionality s P m i b)
        (values s P (ind extensionality s P m) (shape (Scheme.rule s i))
          (backward
            (arguments extensionality s (shape (Scheme.rule s i))) b))
        (calls-agree s P (method extensionality s P m)
          (shape (Scheme.rule s i))
          (backward
            (arguments extensionality s (shape (Scheme.rule s i))) b))

------------------------------------------------------------------------
-- Native methods

-- A native method gives an ordinary one at the native arguments, with the
-- same hypotheses, so its congruence is the native one. For congruent
-- native methods ordinary induction is native induction.

module _
  {ℓ κ ν : Level} (extensionality : Extensionality ℓ κ) (s : Scheme ℓ κ)
  (P : (i : Scheme.Index s) → U s i → Set ν)
  where

  ordinary : Indexed.Method s P → Method extensionality s P
  ordinary m i b =
    m i (backward (arguments extensionality s (shape (Scheme.rule s i))) b)

  agrees-with-native :
    (m : Indexed.Method s P) (congruence : Initiality.Congruent s P m)
    (i : Scheme.Index s) (u : U s i)
    → Indexed.ind s P m i u ＝ ind extensionality s P (ordinary m) i u
  agrees-with-native m congruence =
    ind-unique extensionality s P (Indexed.ind s P m) (ordinary m)
      ( λ i b →
          congruence i
            (backward
              (arguments extensionality s (shape (Scheme.rule s i))) b))
      ( λ i b →
          Initiality.ind-homomorphic s P m congruence i
            (backward
              (arguments extensionality s (shape (Scheme.rule s i))) b))

------------------------------------------------------------------------
-- Congruence under extensionality

-- Under extensionality for the arities at the motive's level, agreeing
-- hypotheses are identical, so every method is congruent.

module _
  {ℓ κ ν : Level} (extensionality : Extensionality ℓ κ)
  (motive : Extensionality ℓ ν) (s : Scheme ℓ κ)
  (P : (i : Scheme.Index s) → U s i → Set ν)
  where

  congruent :
    (m : Method extensionality s P) → Congruent extensionality s P m
  congruent m i b h k r =
    ap (m i b)
      ( agreement motive s P (shape (Scheme.rule s i))
          (backward (arguments extensionality s (shape (Scheme.rule s i))) b)
          h k r)

------------------------------------------------------------------------
-- Fusion

-- A map of motives carrying the methods of one to congruent methods of the
-- other carries induction to induction, through ind-β of the first.

module _
  {ℓ κ ν ν′ : Level} (extensionality : Extensionality ℓ κ)
  (s : Scheme ℓ κ) (P : (i : Scheme.Index s) → U s i → Set ν)
  (P′ : (i : Scheme.Index s) → U s i → Set ν′)
  (f : (i : Scheme.Index s) (u : U s i) → P i u → P′ i u)
  where

  Carries :
    Method extensionality s P → Method extensionality s P′
    → Set (ℓ ⊔ ν ⊔ ν′)
  Carries m m′ =
    (i : Scheme.Index s)
    (b : Polynomial.Args (shape (Scheme.rule s i)) (family s))
    (h : Hypothesis extensionality s P i b)
    → f i (make extensionality s i b) (m i b h)
      ＝ m′ i b
          (mapped s P P′ f (shape (Scheme.rule s i))
            (backward
              (arguments extensionality s (shape (Scheme.rule s i))) b)
            h)

  ind-fusion :
    (m : Method extensionality s P) (m′ : Method extensionality s P′)
    → Congruent extensionality s P′ m′ → Carries m m′
    → (i : Scheme.Index s) (u : U s i)
    → f i u (ind extensionality s P m i u) ＝ ind extensionality s P′ m′ i u
  ind-fusion m m′ congruence carries =
    ind-unique-rel extensionality s P P′ (Graph s P P′ f)
      (ind extensionality s P m) m′
      ( λ i b k r →
          ap (f i (make extensionality s i b)) (ind-β extensionality s P m i b)
          ∙ carries i b (hypotheses extensionality s P m i b)
          ∙ congruence i b
              (mapped s P P′ f (shape (Scheme.rule s i))
                (backward
                  (arguments extensionality s (shape (Scheme.rule s i))) b)
                (hypotheses extensionality s P m i b))
              k
              (graph-agreement s P P′ f (shape (Scheme.rule s i))
                (backward
                  (arguments extensionality s (shape (Scheme.rule s i))) b)
                (hypotheses extensionality s P m i b) k
                (values-to-calls s P P′ (Graph s P P′ f)
                  (method extensionality s P m) (shape (Scheme.rule s i))
                  (backward
                    (arguments extensionality s (shape (Scheme.rule s i))) b)
                  k r)))
