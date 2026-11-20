{-# OPTIONS --safe --without-K #-}

module SPT.MartinLof.Model.Subuniverse where

-- A structure of Kubánek's Mahlo subuniverses on a Russell model with Π
-- (`Subuniverse`; Canonicity of the Mahlo Universe, MSc thesis, Chalmers
-- 2025, §3.3). At level i its four parameters are a base U0 : U i with a
-- decoding E0 : U0 → U i, and an operator U+ : Π (A : U i). (A → U i) →
-- U i with a decoding E+ : Π (A : U i) (B : A → U i). U+ A B → U i. Then
-- `subuniverse i U0 E0 U+ E+` is a code at level i, with the codes
-- `inclusion … u` of the base and `closure … A B c` of the operator, the
-- decoding `decoding … a`, and induction `induction i j … M b s a` into a
-- motive M : Ma → U j with a method at each kind of code (`Operations`).
-- Every argument is a term, the motive and the methods functions, as in
-- the syntax, so no operation takes a context extension.
--
-- The types the laws mention are those of MartinLof.Subuniverse
-- read in the model, a weakening read as substitution along p
-- (`family-type`, `operator-type`, `plus-decoding-type`, `family-of-type`,
-- `decoded-plus-type`,
-- `point-type`, the methods' types, and the values `decoding-closure`,
-- `induction-inclusion`, `induction-closure`). The typings of the
-- parameters, of a closure's arguments and of the motive and methods are
-- records (`Parameters`, `Arguments`, `Methods`).
--
-- The laws, a record over the operations (`Subuniverse R products
-- operations`): the formers' types; decoding at both kinds of code;
-- induction at both (β); stability under substitution. Each holds where
-- the arguments have their types.

open import SPT.Base hiding (_∘_; id)
open import SPT.MartinLof.Model.Pi using (Pi)
open import SPT.MartinLof.Model.Russell using (Russell; Code)
open import SPT.MartinLof.Subuniverse using
  (family-level; operation-level; plus-level; fourth-level; third-level
  ; second-level; first-level)

------------------------------------------------------------------------
-- The operations

record Operations {ℓ : Level} (R : Russell ℓ) : Set ℓ where
  open Russell R
  field
    subuniverse : {Γ : Ob} (i : ℕ) (U0 E0 U+ E+ : Tm Γ) → Tm Γ
    inclusion : {Γ : Ob} (i : ℕ) (U0 E0 U+ E+ u : Tm Γ) → Tm Γ
    closure : {Γ : Ob} (i : ℕ) (U0 E0 U+ E+ A B c : Tm Γ) → Tm Γ
    decoding : {Γ : Ob} (i : ℕ) (U0 E0 U+ E+ a : Tm Γ) → Tm Γ
    induction :
      {Γ : Ob} (i j : ℕ) (U0 E0 U+ E+ M b s a : Tm Γ) → Tm Γ

------------------------------------------------------------------------
-- The parameters' types

module _ {ℓ : Level} (R : Russell ℓ) (products : Pi R) where

  open Russell R
  open Pi products

  -- a → U i.
  family-type : {Γ : Ob} (i : ℕ) (a : Tm Γ) → Tm Γ
  family-type {Γ} i a = pi i (suc i) a (universe i [ ε (Γ ▸ a) ])

  -- (A → U i) → U i, over A : U i.
  operation-type : {Γ : Ob} (i : ℕ) → Tm (Γ ▸ universe i [ ε Γ ])
  operation-type {Γ} i =
    pi (family-level i) (suc i) (family-type i (q (universe i [ ε Γ ])))
      (universe i
        [ ε (Γ ▸ universe i [ ε Γ ] ▸ family-type i (q (universe i [ ε Γ ])))
        ])

  -- Π (A : U i). (A → U i) → U i.
  operator-type : {Γ : Ob} (i : ℕ) → Tm Γ
  operator-type {Γ} i =
    pi (suc i) (operation-level i) (universe i [ ε Γ ]) (operation-type i)

  -- f a b, for f an operator.
  operated : {Γ : Ob} (i : ℕ) (f a b : Tm Γ) → Tm Γ
  operated {Γ} i f a b =
    application (family-level i) (suc i) (family-type i a)
      (universe i [ ε (Γ ▸ family-type i a) ])
      (application (suc i) (operation-level i) (universe i [ ε Γ ])
        (operation-type i) f a)
      b

  -- f A B → U i, over A : U i and B : A → U i.
  plus-family-type :
    {Γ : Ob} (i : ℕ) (f : Tm Γ)
    → Tm (Γ ▸ universe i [ ε Γ ] ▸ family-type i (q (universe i [ ε Γ ])))
  plus-family-type {Γ} i f =
    pi i (suc i)
      (operated i (f [ p ] [ p ]) (q (universe i [ ε Γ ]) [ p ])
        (q (family-type i (q (universe i [ ε Γ ])))))
      (universe i
        [ ε (Γ ▸ universe i [ ε Γ ] ▸ family-type i (q (universe i [ ε Γ ]))
             ▸ operated i (f [ p ] [ p ]) (q (universe i [ ε Γ ]) [ p ])
                 (q (family-type i (q (universe i [ ε Γ ])))))
        ])

  -- Π (B : A → U i). f A B → U i, over A : U i.
  plus-operation-type :
    {Γ : Ob} (i : ℕ) (f : Tm Γ) → Tm (Γ ▸ universe i [ ε Γ ])
  plus-operation-type {Γ} i f =
    pi (family-level i) (family-level i)
      (family-type i (q (universe i [ ε Γ ]))) (plus-family-type i f)

  -- Π (A : U i) (B : A → U i). f A B → U i.
  plus-decoding-type : {Γ : Ob} (i : ℕ) (f : Tm Γ) → Tm Γ
  plus-decoding-type {Γ} i f =
    pi (suc i) (plus-level i) (universe i [ ε Γ ]) (plus-operation-type i f)

  -- The parameters with their types.
  record Parameters {Γ : Ob} (i : ℕ) (U0 E0 U+ E+ : Tm Γ) : Set ℓ where
    field
      base-code : Code R i U0
      base-decoding-type : type-of E0 ＝ family-type i U0
      step-type : type-of U+ ＝ operator-type i
      step-decoding-type : type-of E+ ＝ plus-decoding-type i U+

------------------------------------------------------------------------
-- Types over the subuniverse

module _ {ℓ : Level} (R : Russell ℓ) (products : Pi R)
  (operations : Operations R)
  where

  open Russell R
  open Pi products
  open Operations operations

  -- El A → Ma.
  family-of-type : {Γ : Ob} (i : ℕ) (U0 E0 U+ E+ A : Tm Γ) → Tm Γ
  family-of-type i U0 E0 U+ E+ A =
    pi i i (decoding i U0 E0 U+ E+ A)
      (subuniverse i (U0 [ p ]) (E0 [ p ]) (U+ [ p ]) (E+ [ p ]))

  -- B x, over x : El A.
  applied-term :
    {Γ : Ob} (i : ℕ) (U0 E0 U+ E+ A B : Tm Γ)
    → Tm (Γ ▸ decoding i U0 E0 U+ E+ A)
  applied-term i U0 E0 U+ E+ A B =
    application i i
      (decoding i (U0 [ p ]) (E0 [ p ]) (U+ [ p ]) (E+ [ p ]) (A [ p ]))
      (subuniverse i (U0 [ p ] [ p ]) (E0 [ p ] [ p ]) (U+ [ p ] [ p ])
        (E+ [ p ] [ p ]))
      (B [ p ]) (q (decoding i U0 E0 U+ E+ A))

  -- λ x. El (B x).
  decoded-term : {Γ : Ob} (i : ℕ) (U0 E0 U+ E+ A B : Tm Γ) → Tm Γ
  decoded-term {Γ} i U0 E0 U+ E+ A B =
    lambda i (suc i) (decoding i U0 E0 U+ E+ A)
      (universe i [ ε (Γ ▸ decoding i U0 E0 U+ E+ A) ])
      (decoding i (U0 [ p ]) (E0 [ p ]) (U+ [ p ]) (E+ [ p ])
        (applied-term i U0 E0 U+ E+ A B))

  -- U+ (El A) B → U i, over B : El A → U i.
  decoded-plus-type :
    {Γ : Ob} (i : ℕ) (U0 E0 U+ E+ A : Tm Γ)
    → Tm (Γ ▸ family-type R products i (decoding i U0 E0 U+ E+ A))
  decoded-plus-type {Γ} i U0 E0 U+ E+ A =
    pi i (suc i)
      (operated R products i (U+ [ p ])
        (decoding i (U0 [ p ]) (E0 [ p ]) (U+ [ p ]) (E+ [ p ]) (A [ p ]))
        (q (family-type R products i (decoding i U0 E0 U+ E+ A))))
      (universe i
        [ ε (Γ ▸ family-type R products i (decoding i U0 E0 U+ E+ A)
             ▸ operated R products i (U+ [ p ])
                 (decoding i (U0 [ p ]) (E0 [ p ]) (U+ [ p ]) (E+ [ p ])
                   (A [ p ]))
                 (q (family-type R products i (decoding i U0 E0 U+ E+ A))))
        ])

  -- U+ (El A) (λ x. El (B x)).
  point-type : {Γ : Ob} (i : ℕ) (U0 E0 U+ E+ A B : Tm Γ) → Tm Γ
  point-type i U0 E0 U+ E+ A B =
    operated R products i U+ (decoding i U0 E0 U+ E+ A)
      (decoded-term i U0 E0 U+ E+ A B)

  -- Ma → U j, and M a.
  motive-type : {Γ : Ob} (i j : ℕ) (U0 E0 U+ E+ : Tm Γ) → Tm Γ
  motive-type {Γ} i j U0 E0 U+ E+ =
    pi i (suc j) (subuniverse i U0 E0 U+ E+)
      (universe j [ ε (Γ ▸ subuniverse i U0 E0 U+ E+) ])

  motive-at : {Γ : Ob} (i j : ℕ) (U0 E0 U+ E+ M a : Tm Γ) → Tm Γ
  motive-at {Γ} i j U0 E0 U+ E+ M a =
    application i (suc j) (subuniverse i U0 E0 U+ E+)
      (universe j [ ε (Γ ▸ subuniverse i U0 E0 U+ E+) ]) M a

  -- Π (u : U0). M (El0' u).
  inclusion-method-type : {Γ : Ob} (i j : ℕ) (U0 E0 U+ E+ M : Tm Γ) → Tm Γ
  inclusion-method-type i j U0 E0 U+ E+ M =
    pi i j U0
      (motive-at i j (U0 [ p ]) (E0 [ p ]) (U+ [ p ]) (E+ [ p ]) (M [ p ])
        (inclusion i (U0 [ p ]) (E0 [ p ]) (U+ [ p ]) (E+ [ p ]) (q U0)))

  -- b u, and s A (ind A) B (λ x. ind (B x)) c.
  induction-inclusion :
    {Γ : Ob} (i j : ℕ) (U0 E0 U+ E+ M b u : Tm Γ) → Tm Γ
  induction-inclusion i j U0 E0 U+ E+ M b u =
    application i j U0
      (motive-at i j (U0 [ p ]) (E0 [ p ]) (U+ [ p ]) (E+ [ p ]) (M [ p ])
        (inclusion i (U0 [ p ]) (E0 [ p ]) (U+ [ p ]) (E+ [ p ]) (q U0)))
      b u

  -- Sealed, each in its own block with its unfolding as an equation:
  -- a record type that mentions one unfolds it when declared, and an
  -- unfolding that reached the nested ones would copy their repeated
  -- arguments at every level.
  opaque
    -- E+ (El A) (λ x. El (B x)) c.
    decoding-closure : {Γ : Ob} (i : ℕ) (U0 E0 U+ E+ A B c : Tm Γ) → Tm Γ
    decoding-closure {Γ} i U0 E0 U+ E+ A B c =
      application i (suc i) (point-type i U0 E0 U+ E+ A B)
        (universe i [ ε (Γ ▸ point-type i U0 E0 U+ E+ A B) ])
        (application (family-level i) (family-level i)
          (family-type R products i (decoding i U0 E0 U+ E+ A))
          (decoded-plus-type i U0 E0 U+ E+ A)
          (application (suc i) (plus-level i) (universe i [ ε Γ ])
            (plus-operation-type R products i U+) E+
            (decoding i U0 E0 U+ E+ A))
          (decoded-term i U0 E0 U+ E+ A B))
        c

    decoding-closure-unfold :
      {Γ : Ob} (i : ℕ) (U0 E0 U+ E+ A B c : Tm Γ)
      → decoding-closure i U0 E0 U+ E+ A B c
        ＝ application i (suc i) (point-type i U0 E0 U+ E+ A B)
            (universe i [ ε (Γ ▸ point-type i U0 E0 U+ E+ A B) ])
            (application (family-level i) (family-level i)
              (family-type R products i (decoding i U0 E0 U+ E+ A))
              (decoded-plus-type i U0 E0 U+ E+ A)
              (application (suc i) (plus-level i) (universe i [ ε Γ ])
                (plus-operation-type R products i U+) E+
                (decoding i U0 E0 U+ E+ A))
              (decoded-term i U0 E0 U+ E+ A B))
            c
    decoding-closure-unfold i U0 E0 U+ E+ A B c = refl

  opaque
    -- The closure method, Π by Π from inside: Π (c : U+ (El A) …).
    -- M (El+' A B c); Π (x : El A). M (B x); then over k, over B, over h
    -- and over A.
    closure-fourth-type :
      {Γ : Ob} (i j : ℕ) (U0 E0 U+ E+ M A B : Tm Γ) → Tm Γ
    closure-fourth-type i j U0 E0 U+ E+ M A B =
      pi i j (point-type i U0 E0 U+ E+ A B)
        (motive-at i j (U0 [ p ]) (E0 [ p ]) (U+ [ p ]) (E+ [ p ]) (M [ p ])
          (closure i (U0 [ p ]) (E0 [ p ]) (U+ [ p ]) (E+ [ p ]) (A [ p ])
            (B [ p ]) (q (point-type i U0 E0 U+ E+ A B))))

    closure-fourth-type-unfold :
      {Γ : Ob} (i j : ℕ) (U0 E0 U+ E+ M A B : Tm Γ)
      → closure-fourth-type i j U0 E0 U+ E+ M A B
        ＝
        pi i j (point-type i U0 E0 U+ E+ A B)
          (motive-at i j (U0 [ p ]) (E0 [ p ]) (U+ [ p ]) (E+ [ p ]) (M [ p ])
            (closure i (U0 [ p ]) (E0 [ p ]) (U+ [ p ]) (E+ [ p ]) (A [ p ])
              (B [ p ]) (q (point-type i U0 E0 U+ E+ A B))))
    closure-fourth-type-unfold i j U0 E0 U+ E+ M A B = refl

  opaque
    hypotheses-type :
      {Γ : Ob} (i j : ℕ) (U0 E0 U+ E+ M A B : Tm Γ) → Tm Γ
    hypotheses-type i j U0 E0 U+ E+ M A B =
      pi i j (decoding i U0 E0 U+ E+ A)
        (motive-at i j (U0 [ p ]) (E0 [ p ]) (U+ [ p ]) (E+ [ p ]) (M [ p ])
          (applied-term i U0 E0 U+ E+ A B))

    hypotheses-type-unfold :
      {Γ : Ob} (i j : ℕ) (U0 E0 U+ E+ M A B : Tm Γ)
      → hypotheses-type i j U0 E0 U+ E+ M A B
        ＝
        pi i j (decoding i U0 E0 U+ E+ A)
          (motive-at i j (U0 [ p ]) (E0 [ p ]) (U+ [ p ]) (E+ [ p ]) (M [ p ])
            (applied-term i U0 E0 U+ E+ A B))
    hypotheses-type-unfold i j U0 E0 U+ E+ M A B = refl

  opaque
    closure-third-type :
      {Γ : Ob} (i j : ℕ) (U0 E0 U+ E+ M A B : Tm Γ) → Tm Γ
    closure-third-type i j U0 E0 U+ E+ M A B =
      pi (fourth-level i j) (fourth-level i j)
        (hypotheses-type i j U0 E0 U+ E+ M A B)
        (closure-fourth-type i j (U0 [ p ]) (E0 [ p ]) (U+ [ p ]) (E+ [ p ])
          (M [ p ]) (A [ p ]) (B [ p ]))

    closure-third-type-unfold :
      {Γ : Ob} (i j : ℕ) (U0 E0 U+ E+ M A B : Tm Γ)
      → closure-third-type i j U0 E0 U+ E+ M A B
        ＝
        pi (fourth-level i j) (fourth-level i j)
          (hypotheses-type i j U0 E0 U+ E+ M A B)
          (closure-fourth-type i j (U0 [ p ]) (E0 [ p ]) (U+ [ p ]) (E+ [ p ])
            (M [ p ]) (A [ p ]) (B [ p ]))
    closure-third-type-unfold i j U0 E0 U+ E+ M A B = refl

  opaque
    closure-second-type :
      {Γ : Ob} (i j : ℕ) (U0 E0 U+ E+ M A : Tm Γ) → Tm Γ
    closure-second-type i j U0 E0 U+ E+ M A =
      pi (i ⊔ℕ i) (third-level i j) (family-of-type i U0 E0 U+ E+ A)
        (closure-third-type i j (U0 [ p ]) (E0 [ p ]) (U+ [ p ]) (E+ [ p ])
          (M [ p ]) (A [ p ]) (q (family-of-type i U0 E0 U+ E+ A)))

    closure-second-type-unfold :
      {Γ : Ob} (i j : ℕ) (U0 E0 U+ E+ M A : Tm Γ)
      → closure-second-type i j U0 E0 U+ E+ M A
        ＝
        pi (i ⊔ℕ i) (third-level i j) (family-of-type i U0 E0 U+ E+ A)
          (closure-third-type i j (U0 [ p ]) (E0 [ p ]) (U+ [ p ]) (E+ [ p ])
            (M [ p ]) (A [ p ]) (q (family-of-type i U0 E0 U+ E+ A)))
    closure-second-type-unfold i j U0 E0 U+ E+ M A = refl

  opaque
    closure-first-type :
      {Γ : Ob} (i j : ℕ) (U0 E0 U+ E+ M A : Tm Γ) → Tm Γ
    closure-first-type i j U0 E0 U+ E+ M A =
      pi j (second-level i j) (motive-at i j U0 E0 U+ E+ M A)
        (closure-second-type i j (U0 [ p ]) (E0 [ p ]) (U+ [ p ]) (E+ [ p ])
          (M [ p ]) (A [ p ]))

    closure-first-type-unfold :
      {Γ : Ob} (i j : ℕ) (U0 E0 U+ E+ M A : Tm Γ)
      → closure-first-type i j U0 E0 U+ E+ M A
        ＝
        pi j (second-level i j) (motive-at i j U0 E0 U+ E+ M A)
          (closure-second-type i j (U0 [ p ]) (E0 [ p ]) (U+ [ p ]) (E+ [ p ])
            (M [ p ]) (A [ p ]))
    closure-first-type-unfold i j U0 E0 U+ E+ M A = refl

  opaque
    closure-method-type : {Γ : Ob} (i j : ℕ) (U0 E0 U+ E+ M : Tm Γ) → Tm Γ
    closure-method-type i j U0 E0 U+ E+ M =
      pi i (first-level i j) (subuniverse i U0 E0 U+ E+)
        (closure-first-type i j (U0 [ p ]) (E0 [ p ]) (U+ [ p ]) (E+ [ p ])
          (M [ p ]) (q (subuniverse i U0 E0 U+ E+)))

    closure-method-type-unfold :
      {Γ : Ob} (i j : ℕ) (U0 E0 U+ E+ M : Tm Γ)
      → closure-method-type i j U0 E0 U+ E+ M
        ＝ pi i (first-level i j) (subuniverse i U0 E0 U+ E+)
            (closure-first-type i j (U0 [ p ]) (E0 [ p ]) (U+ [ p ])
              (E+ [ p ]) (M [ p ]) (q (subuniverse i U0 E0 U+ E+)))
    closure-method-type-unfold i j U0 E0 U+ E+ M = refl

  opaque
    induction-closure :
      {Γ : Ob} (i j : ℕ) (U0 E0 U+ E+ M b s A B c : Tm Γ) → Tm Γ
    induction-closure i j U0 E0 U+ E+ M b s A B c =
      application i j (point-type i U0 E0 U+ E+ A B)
        (motive-at i j (U0 [ p ]) (E0 [ p ]) (U+ [ p ]) (E+ [ p ]) (M [ p ])
          (closure i (U0 [ p ]) (E0 [ p ]) (U+ [ p ]) (E+ [ p ]) (A [ p ])
            (B [ p ]) (q (point-type i U0 E0 U+ E+ A B))))
        (application (fourth-level i j) (fourth-level i j)
          (hypotheses-type i j U0 E0 U+ E+ M A B)
          (closure-fourth-type i j (U0 [ p ]) (E0 [ p ]) (U+ [ p ])
            (E+ [ p ]) (M [ p ]) (A [ p ]) (B [ p ]))
          (application (i ⊔ℕ i) (third-level i j)
            (family-of-type i U0 E0 U+ E+ A)
            (closure-third-type i j (U0 [ p ]) (E0 [ p ]) (U+ [ p ])
              (E+ [ p ]) (M [ p ]) (A [ p ])
              (q (family-of-type i U0 E0 U+ E+ A)))
            (application j (second-level i j) (motive-at i j U0 E0 U+ E+ M A)
              (closure-second-type i j (U0 [ p ]) (E0 [ p ]) (U+ [ p ])
                (E+ [ p ]) (M [ p ]) (A [ p ]))
              (application i (first-level i j) (subuniverse i U0 E0 U+ E+)
                (closure-first-type i j (U0 [ p ]) (E0 [ p ]) (U+ [ p ])
                  (E+ [ p ]) (M [ p ]) (q (subuniverse i U0 E0 U+ E+)))
                s A)
              (induction i j U0 E0 U+ E+ M b s A))
            B)
          (lambda i j (decoding i U0 E0 U+ E+ A)
            (motive-at i j (U0 [ p ]) (E0 [ p ]) (U+ [ p ]) (E+ [ p ]) (M [ p ])
              (applied-term i U0 E0 U+ E+ A B))
            (induction i j (U0 [ p ]) (E0 [ p ]) (U+ [ p ]) (E+ [ p ]) (M [ p ])
              (b [ p ]) (s [ p ]) (applied-term i U0 E0 U+ E+ A B))))
        c

    induction-closure-unfold :
      {Γ : Ob} (i j : ℕ) (U0 E0 U+ E+ M b s A B c : Tm Γ)
      → induction-closure i j U0 E0 U+ E+ M b s A B c
        ＝
        application i j (point-type i U0 E0 U+ E+ A B)
          (motive-at i j (U0 [ p ]) (E0 [ p ]) (U+ [ p ]) (E+ [ p ]) (M [ p ])
            (closure i (U0 [ p ]) (E0 [ p ]) (U+ [ p ]) (E+ [ p ]) (A [ p ])
              (B [ p ]) (q (point-type i U0 E0 U+ E+ A B))))
          (application (fourth-level i j) (fourth-level i j)
            (hypotheses-type i j U0 E0 U+ E+ M A B)
            (closure-fourth-type i j (U0 [ p ]) (E0 [ p ]) (U+ [ p ])
              (E+ [ p ]) (M [ p ]) (A [ p ]) (B [ p ]))
            (application (i ⊔ℕ i) (third-level i j)
              (family-of-type i U0 E0 U+ E+ A)
              (closure-third-type i j (U0 [ p ]) (E0 [ p ]) (U+ [ p ])
                (E+ [ p ]) (M [ p ]) (A [ p ])
                (q (family-of-type i U0 E0 U+ E+ A)))
              (application j (second-level i j) (motive-at i j U0 E0 U+ E+ M A)
                (closure-second-type i j (U0 [ p ]) (E0 [ p ]) (U+ [ p ])
                  (E+ [ p ]) (M [ p ]) (A [ p ]))
                (application i (first-level i j) (subuniverse i U0 E0 U+ E+)
                  (closure-first-type i j (U0 [ p ]) (E0 [ p ]) (U+ [ p ])
                    (E+ [ p ]) (M [ p ]) (q (subuniverse i U0 E0 U+ E+)))
                  s A)
                (induction i j U0 E0 U+ E+ M b s A))
              B)
            (lambda i j (decoding i U0 E0 U+ E+ A)
              (motive-at i j (U0 [ p ]) (E0 [ p ]) (U+ [ p ]) (E+ [ p ])
                (M [ p ]) (applied-term i U0 E0 U+ E+ A B))
              (induction i j (U0 [ p ]) (E0 [ p ]) (U+ [ p ]) (E+ [ p ])
                (M [ p ]) (b [ p ]) (s [ p ])
                (applied-term i U0 E0 U+ E+ A B))))
          c
    induction-closure-unfold i j U0 E0 U+ E+ M b s A B c = refl

  -- A closure's arguments, and the motive and methods, with their types.
  record Arguments
    {Γ : Ob} (i : ℕ) (U0 E0 U+ E+ A B c : Tm Γ) : Set ℓ where
    field
      code-type : type-of A ＝ subuniverse i U0 E0 U+ E+
      family-type′ : type-of B ＝ family-of-type i U0 E0 U+ E+ A
      point-type′ : type-of c ＝ point-type i U0 E0 U+ E+ A B

  record Methods
    {Γ : Ob} (i j : ℕ) (U0 E0 U+ E+ M b s : Tm Γ) : Set ℓ where
    field
      motive-type′ : type-of M ＝ motive-type i j U0 E0 U+ E+
      inclusion-method-type′ :
        type-of b ＝ inclusion-method-type i j U0 E0 U+ E+ M
      closure-method-type′ : type-of s ＝ closure-method-type i j U0 E0 U+ E+ M

------------------------------------------------------------------------
-- The structure

record Subuniverse {ℓ : Level} (R : Russell ℓ) (products : Pi R)
  (operations : Operations R) : Set ℓ where
  open Russell R
  open Pi products
  open Operations operations
  field
    subuniverse-code :
      {Γ : Ob} (i : ℕ) (U0 E0 U+ E+ : Tm Γ)
      → Parameters R products i U0 E0 U+ E+
      → Code R i (subuniverse i U0 E0 U+ E+)
    inclusion-type :
      {Γ : Ob} (i : ℕ) (U0 E0 U+ E+ u : Tm Γ)
      → Parameters R products i U0 E0 U+ E+ → type-of u ＝ U0
      → type-of (inclusion i U0 E0 U+ E+ u) ＝ subuniverse i U0 E0 U+ E+
    closure-type :
      {Γ : Ob} (i : ℕ) (U0 E0 U+ E+ A B c : Tm Γ)
      → Parameters R products i U0 E0 U+ E+
      → Arguments R products operations i U0 E0 U+ E+ A B c
      → type-of (closure i U0 E0 U+ E+ A B c) ＝ subuniverse i U0 E0 U+ E+
    decoding-code :
      {Γ : Ob} (i : ℕ) (U0 E0 U+ E+ a : Tm Γ)
      → Parameters R products i U0 E0 U+ E+
      → type-of a ＝ subuniverse i U0 E0 U+ E+
      → Code R i (decoding i U0 E0 U+ E+ a)
    induction-type :
      {Γ : Ob} (i j : ℕ) (U0 E0 U+ E+ M b s a : Tm Γ)
      → Parameters R products i U0 E0 U+ E+
      → Methods R products operations i j U0 E0 U+ E+ M b s
      → type-of a ＝ subuniverse i U0 E0 U+ E+
      → type-of (induction i j U0 E0 U+ E+ M b s a)
        ＝ motive-at R products operations i j U0 E0 U+ E+ M a

    inclusion-decoding :
      {Γ : Ob} (i : ℕ) (U0 E0 U+ E+ u : Tm Γ)
      → Parameters R products i U0 E0 U+ E+ → type-of u ＝ U0
      → decoding i U0 E0 U+ E+ (inclusion i U0 E0 U+ E+ u)
        ＝ application i (suc i) U0 (universe i [ ε (Γ ▸ U0) ]) E0 u
    closure-decoding :
      {Γ : Ob} (i : ℕ) (U0 E0 U+ E+ A B c : Tm Γ)
      → Parameters R products i U0 E0 U+ E+
      → Arguments R products operations i U0 E0 U+ E+ A B c
      → decoding i U0 E0 U+ E+ (closure i U0 E0 U+ E+ A B c)
        ＝ decoding-closure R products operations i U0 E0 U+ E+ A B c
    inclusion-computation :
      {Γ : Ob} (i j : ℕ) (U0 E0 U+ E+ M b s u : Tm Γ)
      → Parameters R products i U0 E0 U+ E+
      → Methods R products operations i j U0 E0 U+ E+ M b s
      → type-of u ＝ U0
      → induction i j U0 E0 U+ E+ M b s (inclusion i U0 E0 U+ E+ u)
        ＝ induction-inclusion R products operations i j U0 E0 U+ E+ M b u
    closure-computation :
      {Γ : Ob} (i j : ℕ) (U0 E0 U+ E+ M b s A B c : Tm Γ)
      → Parameters R products i U0 E0 U+ E+
      → Methods R products operations i j U0 E0 U+ E+ M b s
      → Arguments R products operations i U0 E0 U+ E+ A B c
      → induction i j U0 E0 U+ E+ M b s (closure i U0 E0 U+ E+ A B c)
        ＝ induction-closure R products operations i j U0 E0 U+ E+ M b s A B c

    subuniverse-[] :
      {Γ Δ : Ob} (i : ℕ) (U0 E0 U+ E+ : Tm Γ) (σ : Hom Δ Γ)
      → Parameters R products i U0 E0 U+ E+
      → subuniverse i U0 E0 U+ E+ [ σ ]
        ＝ subuniverse i (U0 [ σ ]) (E0 [ σ ]) (U+ [ σ ]) (E+ [ σ ])
    inclusion-[] :
      {Γ Δ : Ob} (i : ℕ) (U0 E0 U+ E+ u : Tm Γ) (σ : Hom Δ Γ)
      → Parameters R products i U0 E0 U+ E+ → type-of u ＝ U0
      → inclusion i U0 E0 U+ E+ u [ σ ]
        ＝ inclusion i (U0 [ σ ]) (E0 [ σ ]) (U+ [ σ ]) (E+ [ σ ]) (u [ σ ])
    closure-[] :
      {Γ Δ : Ob} (i : ℕ) (U0 E0 U+ E+ A B c : Tm Γ) (σ : Hom Δ Γ)
      → Parameters R products i U0 E0 U+ E+
      → Arguments R products operations i U0 E0 U+ E+ A B c
      → closure i U0 E0 U+ E+ A B c [ σ ]
        ＝ closure i (U0 [ σ ]) (E0 [ σ ]) (U+ [ σ ]) (E+ [ σ ]) (A [ σ ])
            (B [ σ ]) (c [ σ ])
    decoding-[] :
      {Γ Δ : Ob} (i : ℕ) (U0 E0 U+ E+ a : Tm Γ) (σ : Hom Δ Γ)
      → Parameters R products i U0 E0 U+ E+
      → type-of a ＝ subuniverse i U0 E0 U+ E+
      → decoding i U0 E0 U+ E+ a [ σ ]
        ＝ decoding i (U0 [ σ ]) (E0 [ σ ]) (U+ [ σ ]) (E+ [ σ ]) (a [ σ ])
    induction-[] :
      {Γ Δ : Ob} (i j : ℕ) (U0 E0 U+ E+ M b s a : Tm Γ) (σ : Hom Δ Γ)
      → Parameters R products i U0 E0 U+ E+
      → Methods R products operations i j U0 E0 U+ E+ M b s
      → type-of a ＝ subuniverse i U0 E0 U+ E+
      → induction i j U0 E0 U+ E+ M b s a [ σ ]
        ＝ induction i j (U0 [ σ ]) (E0 [ σ ]) (U+ [ σ ]) (E+ [ σ ]) (M [ σ ])
            (b [ σ ]) (s [ σ ]) (a [ σ ])
