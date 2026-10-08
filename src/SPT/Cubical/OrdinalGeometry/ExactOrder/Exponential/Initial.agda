{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.ExactOrder.Exponential.Initial where

-- Finite-support exponentiation acts on order embeddings and on initial
-- maps of exact countable orders. Exponents are mapped one by one, so the
-- exponents of the image support are the images of the exponents, and a
-- support whose exponents all lie in the image comes from a support. For an
-- initial map, a support below an image support agrees with it up to a
-- first difference; every exponent from there on lies below an image
-- exponent, so it returns through the original lower law. Unlike
-- Embedding.Along, no ceiling is required: identities, isomorphisms, and the
-- edges of countable chains are all preserved.

open import Data.List using (List; []; _∷_)
import Data.List as List
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product using (Σ; _,_; proj₁)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; cong₂; sym; subst)

import SPT.Cubical.OrdinalGeometry.ExactOrder.Base as Order
import SPT.Cubical.OrdinalGeometry.ExactOrder.Maps as Maps
import SPT.Cubical.OrdinalGeometry.ExactOrder.Exponential.Support as Support
import SPT.Cubical.OrdinalGeometry.ExactOrder.Exponential.Boundary as Boundary
import SPT.Cubical.OrdinalGeometry.ExactOrder.Exponential.Order as Exponential

-- Supports over two fixed exact orders, mapped along an embedding of
-- exponents. The lower law of an initial map is used separately below.
private
  module SupportMap {A B : Set} (P : Order.Order A) (Q : Order.Order B)
    (f : Maps.Embedding P Q) where

    module Source = Support.Power P
    module Target = Support.Power Q
    module F = Maps.Embedding f

    raw : Source.Raw → Target.Raw
    raw [] = []
    raw ((a , n) ∷ xs) = (F.map a , n) ∷ raw xs

    valid : (xs : Source.Raw) → Source.Valid xs → Target.Valid (raw xs)
    valid [] tt = tt
    valid (_ ∷ []) tt = tt
    valid (_ ∷ ys@(_ ∷ _)) (p , q) =
      Target.complete (F.strict (Source.sound p)) , valid ys q

    reflected : (xs : Source.Raw) → Target.Valid (raw xs) → Source.Valid xs
    reflected [] tt = tt
    reflected (_ ∷ []) tt = tt
    reflected (_ ∷ ys@(_ ∷ _)) (p , q) =
      Source.complete (F.reflect (Target.sound p)) , reflected ys q

    term : Source.Term → Target.Term
    term (xs , q) = raw xs , valid xs q

    pair : {a b : A} {m n : _}
      → (a , m) Source.Pair.< (b , n)
      → (F.map a , m) Target.Pair.< (F.map b , n)
    pair (Source.Pair.earlier p) = Target.Pair.earlier (F.strict p)
    pair (Source.Pair.within a p) = Target.Pair.within (F.map a) p

    strict : {xs ys : Source.Raw}
      → xs Source.≺ ys → raw xs Target.≺ raw ys
    strict Source.empty = Target.empty
    strict (Source.head p) = Target.head (pair p)
    strict (Source.tail p) = Target.tail (strict p)

    exponents : (xs : Source.Raw)
      → List.map proj₁ (raw xs) ≡ List.map F.map (List.map proj₁ xs)
    exponents [] = refl
    exponents ((a , n) ∷ xs) = cong (F.map a ∷_) (exponents xs)

    -- Exponents with preimages are the images of a raw support.
    preimage : (ys : Target.Raw)
      → All (λ b → Σ A (λ a → F.map a ≡ b)) (List.map proj₁ ys)
      → Σ Source.Raw (λ xs → raw xs ≡ ys)
    preimage [] [] = [] , refl
    preimage ((b , n) ∷ ys) ((a , refl) ∷ ps) with preimage ys ps
    ... | xs , r = (a , n) ∷ xs , cong ((F.map a , n) ∷_) r

    restrict : (y : Target.Term)
      → All (λ b → Σ A (λ a → F.map a ≡ b)) (Target.exponents y)
      → Σ Source.Term (λ x → term x ≡ y)
    restrict (ys , v) ps with preimage ys ps
    ... | xs , r =
      (xs , reflected xs (subst Target.Valid (sym r) v)) , Target.equal r

  -- The lower law of an initial map returns supports below an image.
  module SupportLower {A B : Set} (P : Order.Order A) (Q : Order.Order B)
    (f : Maps.Initial P Q) where

    open SupportMap P Q (Maps.Initial.embedding f)
    module TargetBound = Boundary.Power Q

    -- Exponents all below one image point return through its lower law.
    unmap : (a : A) (ys : Target.Raw)
      → TargetBound.All (Maps.Initial.map f a) ys
      → Σ Source.Raw (λ xs → raw xs ≡ ys)
    unmap a [] tt = [] , refl
    unmap a ((b , n) ∷ ys) (p , q)
      with Maps.Initial.lower f a b p | unmap a ys q
    ... | c , refl | xs , r =
      (c , n) ∷ xs , cong ((Maps.Initial.map f c , n) ∷_) r

    -- In a valid support every later exponent lies below the leading one.
    later : {b : B} {n : _} (ys : Target.Raw)
      → Target.Valid ((b , n) ∷ ys) → TargetBound.All b ys
    later [] tt = tt
    later {b} ((c , m) ∷ ys) (p , q) =
      TargetBound.all b (((c , m) ∷ ys) , q) (Target.sound p)

    back : (xs : Source.Raw) (ys : Target.Raw)
      → Target.Valid ys → ys Target.≺ raw xs
      → Σ Source.Raw (λ zs → raw zs ≡ ys)
    back [] ys v ()
    back ((a , n) ∷ xs) [] v Target.empty = [] , refl
    back ((a , n) ∷ xs) ((b , m) ∷ ys) v
      (Target.head (Target.Pair.earlier p)) =
      unmap a ((b , m) ∷ ys)
        (TargetBound.all (Maps.Initial.map f a) (((b , m) ∷ ys) , v) p)
    back ((a , n) ∷ xs) ((b , m) ∷ ys) v
      (Target.head (Target.Pair.within _ p))
      with unmap a ys (later ys v)
    ... | zs , r = (a , m) ∷ zs , cong ((Maps.Initial.map f a , m) ∷_) r
    back ((a , n) ∷ xs) ((b , m) ∷ ys) v (Target.tail p)
      with back xs ys (Target.tail-valid v) p
    ... | zs , r = (a , n) ∷ zs , cong ((Maps.Initial.map f a , n) ∷_) r

    lower : (x : Source.Term) (y : Target.Term)
      → y Target.< term x → Σ Source.Term (λ z → term z ≡ y)
    lower (xs , q) (ys , v) p with back xs ys v p
    ... | zs , r =
      (zs , reflected zs (subst Target.Valid (sym r) v)) , Target.equal r

  -- A triangle of exponent embeddings gives a triangle of raw supports.
  triangle : {A B C : Set} {P : Order.Order A} {Q : Order.Order B}
    {R : Order.Order C}
    (f : Maps.Embedding P Q) (g : Maps.Embedding Q R) (h : Maps.Embedding P R)
    → ((a : A) → Maps.Embedding.map h a
        ≡ Maps.Embedding.map g (Maps.Embedding.map f a))
    → (xs : Support.Power.Raw P)
    → SupportMap.raw P R h xs ≡ SupportMap.raw Q R g (SupportMap.raw P Q f xs)
  triangle f g h e [] = refl
  triangle f g h e ((a , n) ∷ xs) =
    cong₂ _∷_ (cong (_, n) (e a)) (triangle f g h e xs)

  -- An embedding pointwise equal to the identity fixes raw supports.
  still : {A : Set} {P : Order.Order A} (h : Maps.Embedding P P)
    → ((a : A) → Maps.Embedding.map h a ≡ a)
    → (xs : Support.Power.Raw P) → SupportMap.raw P P h xs ≡ xs
  still h e [] = refl
  still h e ((a , n) ∷ xs) = cong₂ _∷_ (cong (_, n) (e a)) (still h e xs)

-- Mathematical shape: an embedding f : P → Q, with P and Q exact, gives
--
--   ω^f (a₁ⁿ¹ ⋯ aₖⁿᵏ) = f(a₁)ⁿ¹ ⋯ f(aₖ)ⁿᵏ,
--
-- again an embedding.
embedding : {A B : Set} {P : Order.Order A} {Q : Order.Order B}
  → Maps.Embedding P Q
  → Maps.Embedding (Exponential.Power.order P) (Exponential.Power.order Q)
embedding {P = P} {Q = Q} f = record
  { map = SupportMap.term P Q f
  ; strict = SupportMap.strict P Q f
  }

-- For an initial map f the same image supports form an initial map.
initial : {A B : Set} {P : Order.Order A} {Q : Order.Order B}
  → Maps.Initial P Q
  → Maps.Initial (Exponential.Power.order P) (Exponential.Power.order Q)
initial {P = P} {Q = Q} f = record
  { map = SupportMap.term P Q (Maps.Initial.embedding f)
  ; strict = SupportMap.strict P Q (Maps.Initial.embedding f)
  ; lower = SupportLower.lower P Q f
  }

-- ω^ of an initial map is ω^ of its underlying embedding.
initial-embedding : {A B : Set} {P : Order.Order A} {Q : Order.Order B}
  (f : Maps.Initial P Q) (x : Support.Power.Term P)
  → Maps.Initial.map (initial f) x
    ≡ Maps.Embedding.map (embedding (Maps.Initial.embedding f)) x
initial-embedding f x = refl

-- The exponents of ω^f(x) are the images of the exponents of x …
exponents : {A B : Set} {P : Order.Order A} {Q : Order.Order B}
  (f : Maps.Embedding P Q) (x : Support.Power.Term P)
  → Support.Power.exponents Q (Maps.Embedding.map (embedding f) x)
    ≡ List.map (Maps.Embedding.map f) (Support.Power.exponents P x)
exponents {P = P} {Q = Q} f (xs , _) = SupportMap.exponents P Q f xs

-- … and a support whose exponents all lie in the image comes from one.
restrict : {A B : Set} {P : Order.Order A} {Q : Order.Order B}
  (f : Maps.Embedding P Q) (y : Support.Power.Term Q)
  → All (λ b → Σ A (λ a → Maps.Embedding.map f a ≡ b))
      (Support.Power.exponents Q y)
  → Σ (Support.Power.Term P) (λ x → Maps.Embedding.map (embedding f) x ≡ y)
restrict {P = P} {Q = Q} f = SupportMap.restrict P Q f

-- A triangle of embeddings gives a triangle of exponentials.
compose : {A B C : Set} {P : Order.Order A} {Q : Order.Order B}
  {R : Order.Order C}
  (f : Maps.Embedding P Q) (g : Maps.Embedding Q R) (h : Maps.Embedding P R)
  → ((a : A) → Maps.Embedding.map h a
      ≡ Maps.Embedding.map g (Maps.Embedding.map f a))
  → (x : Support.Power.Term P)
  → Maps.Embedding.map (embedding h) x
    ≡ Maps.Embedding.map (embedding g) (Maps.Embedding.map (embedding f) x)
compose {R = R} f g h e (xs , _) = Support.Power.equal R (triangle f g h e xs)

-- An embedding pointwise equal to the identity fixes every support.
identity : {A : Set} {P : Order.Order A} (h : Maps.Embedding P P)
  → ((a : A) → Maps.Embedding.map h a ≡ a)
  → (x : Support.Power.Term P) → Maps.Embedding.map (embedding h) x ≡ x
identity {P = P} h e (xs , _) = Support.Power.equal P (still h e xs)
