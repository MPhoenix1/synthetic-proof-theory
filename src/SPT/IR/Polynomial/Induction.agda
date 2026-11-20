{-# OPTIONS --safe --without-K #-}

module SPT.IR.Polynomial.Induction where

-- Indexed polynomial induction–recursion on literal arguments, for the
-- generated part of any algebra. Under extensionality for families of
-- information over the arities, arguments over the generated family are
-- isomorphic to layers (`arguments`, `kept`), with Generated.split as
-- forward map (`presents`, `presented`). So every element is an
-- introduction (`unroll`, `unroll-make`, `make-unroll`), and induction
-- pulls back along split, computing through the half-adjoint coherence
-- (`Method`, `ind`, `ind-β`). Hypotheses at the argument's own positions
-- give the elimination rule on literal arguments (`Literal`, `transfer`,
-- `Step`, `source`, `source-β`).

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.HalfAdjoint using (Σ-bicong)
open import SPT.Foundation.HalfAdjoint.Extension using
  (extension; extension-β)
open import SPT.Foundation.Isomorphisms using
  (_≅_; forward; backward; backward-forward; forward-backward; ≅-trans;
   transport-is-isomorphism; Π-cong)

open import SPT.IR.Polynomial using
  (Poly; var; con; sigma; pi; Family; carrier; readout; Args; info; shape;
   Scheme; Extensionality; lowered)
open import SPT.IR.Polynomial.Action using (pair-info)
open import SPT.IR.Polynomial.Algebra using (Algebra)
open import SPT.IR.Polynomial.Generated using
  (Position; input; both; nowhere)
import SPT.IR.Polynomial.Generated as Generated

-- A function on a sum is the case analysis of its two restrictions.
both-η :
  {α β ν : Level} {A : Set α} {B : Set β} (C : A ⊎ B → Set ν)
  (k : (z : A ⊎ B) → C z) (z : A ⊎ B)
  → both C (λ a → k (inl a)) (λ b → k (inr b)) z ＝ k z
both-η C k (inl a) = refl
both-η C k (inr b) = refl

module _
  {ℓ κ : Level} {s : Scheme ℓ κ} (M : Algebra s)
  (let Z = Algebra.family M) (let G = Generated.generated M)
  where

  ----------------------------------------------------------------------
  -- Layers of the composite codes

  -- A layer of a sum is a layer of its first part with a layer of the
  -- continuation at that part's information, and a layer of a product is
  -- a layer at each point. On the sum the positions are a coproduct, so
  -- one direction uses extensionality; on the product both are by η.

  arrange :
    ((A : Set ℓ) (B : A → Set ℓ) → FunExt A B)
    → {X : Set (ℓ ⊔ κ)} {Y : X → Set (ℓ ⊔ κ)}
      (p : Poly ℓ κ (Scheme.Data s) X)
      (q : (x : X) → Poly ℓ κ (Scheme.Data s) (Y x))
    → Σ (Generated.Layer M p)
        (λ l → Generated.Layer M (q (info p Z (pr₁ l))))
      ≅ Generated.Layer M (sigma p q)
  arrange low p q = record
    { forward = λ w →
        (pr₁ (pr₁ w) , pr₁ (pr₂ w)) ,
        both
          (λ z →
            Generated.Der M
              (input (sigma p q) Z (pr₁ (pr₁ w) , pr₁ (pr₂ w)) z))
          (pr₂ (pr₁ w)) (pr₂ (pr₂ w))
    ; backward = λ l →
        (pr₁ (pr₁ l) , (λ z → pr₂ l (inl z))) ,
        (pr₂ (pr₁ l) , (λ z → pr₂ l (inr z)))
    ; backward-forward = λ w → refl
    ; forward-backward = λ l →
        ap (λ k → pr₁ l , k)
          ( low
              ( Position p Z (pr₁ (pr₁ l))
              ⊎ Position (q (info p Z (pr₁ (pr₁ l)))) Z (pr₂ (pr₁ l)))
              (λ z → Generated.Der M (input (sigma p q) Z (pr₁ l) z))
              (both
                (λ z → Generated.Der M (input (sigma p q) Z (pr₁ l) z))
                (λ z → pr₂ l (inl z)) (λ z → pr₂ l (inr z)))
              (pr₂ l)
              (both-η
                (λ z → Generated.Der M (input (sigma p q) Z (pr₁ l) z))
                (pr₂ l)))
    }

  choice :
    (A : Set ℓ) {Y : A → Set (ℓ ⊔ κ)}
    (p : (a : A) → Poly ℓ κ (Scheme.Data s) (Y a))
    → ((a : A) → Generated.Layer M (p a)) ≅ Generated.Layer M (pi A p)
  choice A p = record
    { forward = λ f → (λ a → pr₁ (f a)) , (λ w → pr₂ (f (pr₁ w)) (pr₂ w))
    ; backward = λ l a → pr₁ l a , (λ z → pr₂ l (a , z))
    ; backward-forward = λ f → refl
    ; forward-backward = λ l → refl
    }

  ----------------------------------------------------------------------
  -- Arguments over the generated family and layers

  -- By recursion on the code, as IR.Indexed.Comparison. At a sum the
  -- continuation is read at the generated information on one side and at
  -- the layer's on the other, so the second parts meet along `kept` at
  -- the first part.

  mutual
    arguments :
      (e : Extensionality ℓ κ) {X : Set (ℓ ⊔ κ)}
      (p : Poly ℓ κ (Scheme.Data s) X)
      → Args p G ≅ Generated.Layer M p
    arguments e (var i) = record
      { forward = λ a → pr₁ a , (λ _ → pr₂ a)
      ; backward = λ l → pr₁ l , pr₂ l (lift ⋆)
      ; backward-forward = λ a → refl
      ; forward-backward = λ l → refl
      }
    arguments e (con A) = record
      { forward = λ a →
          a , nowhere (λ z → Generated.Der M (input (con A) Z a z))
      ; backward = pr₁
      ; backward-forward = λ a → refl
      ; forward-backward = λ l →
          ap (λ c → pr₁ l , c)
            ( lowered κ e (Lift ℓ 𝟘)
                (λ z → Generated.Der M (input (con A) Z (pr₁ l) z))
                (nowhere (λ z → Generated.Der M (input (con A) Z (pr₁ l) z)))
                (pr₂ l)
                (λ z → 𝟘-elim (lower z)))
      }
    arguments e (sigma p q) =
      ≅-trans
        ( Σ-bicong
            (λ a → Args (q (info p G a)) G)
            (λ l → Generated.Layer M (q (info p Z (pr₁ l))))
            (arguments e p)
            (λ a →
              ≅-trans (arguments e (q (info p G a)))
                ( transport-is-isomorphism
                    (λ x → Generated.Layer M (q x)) (kept e p a ⁻¹))))
        (arrange (lowered κ e) p q)
    arguments e (pi A p) =
      ≅-trans
        ( Π-cong
            (lowered κ e A (λ a → Args (p a) G))
            (lowered κ e A (λ a → Generated.Layer M (p a)))
            (λ a → arguments e (p a)))
        (choice A p)

    kept :
      (e : Extensionality ℓ κ) {X : Set (ℓ ⊔ κ)}
      (p : Poly ℓ κ (Scheme.Data s) X) (a : Args p G)
      → info p Z (pr₁ (forward (arguments e p) a)) ＝ info p G a
    kept e (var i) a = refl
    kept e (con A) a = refl
    kept e (sigma {X} {Y} p q) (a , b) =
      pair-info (λ x → Generated.Layer M (q x)) Y
        (λ x l → info (q x) Z (pr₁ l)) (kept e p a ⁻¹)
        (forward (arguments e (q (info p G a))) b)
      ∙ ap (λ y → (info p G a , y)) (kept e (q (info p G a)) b)
    kept e (pi A {Y} p) f =
      e A Y
        (λ x → info (p x) Z (pr₁ (forward (arguments e (p x)) (f x))))
        (λ x → info (p x) G (f x))
        (λ x → kept e (p x) (f x))

  ----------------------------------------------------------------------
  -- The forward map is split

  -- The clauses of split at a sum and a product, as functions of the
  -- results at the parts.

  paired :
    {X : Set (ℓ ⊔ κ)} {Y : X → Set (ℓ ⊔ κ)}
    (p : Poly ℓ κ (Scheme.Data s) X)
    (q : (x : X) → Poly ℓ κ (Scheme.Data s) (Y x))
    (a : Args p G) (b : Args (q (info p G a)) G)
    → Σ (Generated.Layer M p) (λ l → info p Z (pr₁ l) ＝ info p G a)
    → Σ (Generated.Layer M (q (info p G a)))
        (λ l → info (q (info p G a)) Z (pr₁ l) ＝ info (q (info p G a)) G b)
    → Σ (Generated.Layer M (sigma p q))
        (λ l → info (sigma p q) Z (pr₁ l) ＝ info (sigma p q) G (a , b))
  paired {X} {Y} p q a b left right =
    let moved =
          transport (λ x → Generated.Layer M (q x)) (pr₂ left ⁻¹) (pr₁ right)
    in
    ( ( pr₁ (pr₁ left) , pr₁ moved)
    , both
        (λ z →
          Generated.Der M
            (input (sigma p q) Z (pr₁ (pr₁ left) , pr₁ moved) z))
        (pr₂ (pr₁ left))
        (pr₂ moved)) ,
    ( pair-info (λ x → Generated.Layer M (q x)) Y
        (λ x l → info (q x) Z (pr₁ l)) (pr₂ left ⁻¹) (pr₁ right)
    ∙ ap (λ y → (info p G a , y)) (pr₂ right))

  pieced :
    (e : Extensionality ℓ κ) (A : Set ℓ) {Y : A → Set (ℓ ⊔ κ)}
    (p : (a : A) → Poly ℓ κ (Scheme.Data s) (Y a))
    (f : (a : A) → Args (p a) G)
    → ((x : A)
      → Σ (Generated.Layer M (p x))
          (λ l → info (p x) Z (pr₁ l) ＝ info (p x) G (f x)))
    → Σ (Generated.Layer M (pi A p))
        (λ l → info (pi A p) Z (pr₁ l) ＝ info (pi A p) G f)
  pieced e A {Y} p f branch =
    ( (λ x → pr₁ (pr₁ (branch x)))
    , (λ w → pr₂ (pr₁ (branch (pr₁ w))) (pr₂ w))) ,
    e A Y
      (λ x → info (p x) Z (pr₁ (pr₁ (branch x))))
      (λ x → info (p x) G (f x))
      (λ x → pr₂ (branch x))

  presents :
    (e : Extensionality ℓ κ) {X : Set (ℓ ⊔ κ)}
    (p : Poly ℓ κ (Scheme.Data s) X) (a : Args p G)
    → _＝_
        {A = Σ (Generated.Layer M p) (λ l → info p Z (pr₁ l) ＝ info p G a)}
        (forward (arguments e p) a , kept e p a)
        (Generated.split M e p a)
  presents e (var i) a = refl
  presents e (con A) a = refl
  presents e (sigma p q) (a , b) =
    ap₂ (paired p q a b) (presents e p a)
      (presents e (q (info p G a)) b)
  presents e (pi A {Y} p) f =
    ap (pieced e A p f)
      ( e A
          (λ x →
            Σ (Generated.Layer M (p x))
              (λ l → info (p x) Z (pr₁ l) ＝ info (p x) G (f x)))
          (λ x → forward (arguments e (p x)) (f x) , kept e (p x) (f x))
          (λ x → Generated.split M e (p x) (f x))
          (λ x → presents e (p x) (f x)))

  -- The isomorphism whose forward map is split itself.
  presented :
    (e : Extensionality ℓ κ) {X : Set (ℓ ⊔ κ)}
    (p : Poly ℓ κ (Scheme.Data s) X)
    → Args p G ≅ Generated.Layer M p
  presented e p = record
    { forward = λ a → pr₁ (Generated.split M e p a)
    ; backward = backward (arguments e p)
    ; backward-forward = λ a →
        ap (backward (arguments e p)) (ap pr₁ (presents e p a) ⁻¹)
        ∙ backward-forward (arguments e p) a
    ; forward-backward = λ l →
        ap pr₁ (presents e p (backward (arguments e p) l)) ⁻¹
        ∙ forward-backward (arguments e p) l
    }

  ----------------------------------------------------------------------
  -- Every element is an introduction

  unroll :
    (e : Extensionality ℓ κ) (i : Scheme.Index s) → Generated.Carrier M i
    → Args (shape (Scheme.rule s i)) G
  unroll e i t =
    backward (presented e (shape (Scheme.rule s i)))
      (Generated.expose M i t)

  unroll-make :
    (e : Extensionality ℓ κ) (i : Scheme.Index s)
    (a : Args (shape (Scheme.rule s i)) G)
    → unroll e i (Generated.make M e i a) ＝ a
  unroll-make e i a =
    backward-forward (presented e (shape (Scheme.rule s i))) a

  make-unroll :
    (e : Extensionality ℓ κ) (i : Scheme.Index s)
    (t : Generated.Carrier M i)
    → Generated.make M e i (unroll e i t) ＝ t
  make-unroll e i t =
    ap (Generated.introduce M i)
      ( forward-backward (presented e (shape (Scheme.rule s i)))
          (Generated.expose M i t))
    ∙ Generated.introduce-expose M i t

  ----------------------------------------------------------------------
  -- Induction pulled back along split

  -- A hypothesis at each position of a layer, and a method at an argument
  -- whose hypotheses are those at the layer it splits into.

  Hypotheses :
    {ν : Level} (P : (i : Scheme.Index s) → Generated.Carrier M i → Set ν)
    {X : Set (ℓ ⊔ κ)} (p : Poly ℓ κ (Scheme.Data s) X)
    → Generated.Layer M p → Set (ℓ ⊔ ν)
  Hypotheses P p l =
    (z : Position p Z (pr₁ l))
    → P (pr₁ (input p Z (pr₁ l) z)) (pr₂ (input p Z (pr₁ l) z) , pr₂ l z)

  Method :
    {ν : Level} → Extensionality ℓ κ
    → ((i : Scheme.Index s) → Generated.Carrier M i → Set ν) → Set (ℓ ⊔ ν)
  Method e P =
    (i : Scheme.Index s) (a : Args (shape (Scheme.rule s i)) G)
    → Hypotheses P (shape (Scheme.rule s i))
        (pr₁ (Generated.split M e (shape (Scheme.rule s i)) a))
    → P i (Generated.make M e i a)

  -- At any layer, the method at its backward image, carried along the
  -- coherent law (Foundation.HalfAdjoint.Extension).
  method :
    {ν : Level} (e : Extensionality ℓ κ)
    (P : (i : Scheme.Index s) → Generated.Carrier M i → Set ν)
    → Method e P → Generated.Method M P
  method e P m i l =
    extension (presented e (shape (Scheme.rule s i)))
      (λ k →
        Hypotheses P (shape (Scheme.rule s i)) k
        → P i (Generated.introduce M i k))
      (m i) l

  -- Sealed: at a closed code its unfolding is a transport along the whole
  -- coherent law, and every use goes through `ind-β`.
  opaque
    ind :
      {ν : Level} (e : Extensionality ℓ κ)
      (P : (i : Scheme.Index s) → Generated.Carrier M i → Set ν)
      → Method e P → (i : Scheme.Index s) (t : Generated.Carrier M i) → P i t
    ind e P m = Generated.ind M P (method e P m)

  -- The hypotheses induction supplies at a layer.
  supplied :
    {ν : Level}
    (P : (i : Scheme.Index s) → Generated.Carrier M i → Set ν)
    (S : (i : Scheme.Index s) (t : Generated.Carrier M i) → P i t)
    {X : Set (ℓ ⊔ κ)} (p : Poly ℓ κ (Scheme.Data s) X)
    (l : Generated.Layer M p) → Hypotheses P p l
  supplied P S p l z =
    S (pr₁ (input p Z (pr₁ l) z)) (pr₂ (input p Z (pr₁ l) z) , pr₂ l z)

  opaque
    unfolding ind

    ind-β :
      {ν : Level} (e : Extensionality ℓ κ)
      (P : (i : Scheme.Index s) → Generated.Carrier M i → Set ν)
      (m : Method e P) (i : Scheme.Index s)
      (a : Args (shape (Scheme.rule s i)) G)
      → ind e P m i (Generated.make M e i a)
        ＝ m i a
            (supplied P (ind e P m) (shape (Scheme.rule s i))
              (pr₁ (Generated.split M e (shape (Scheme.rule s i)) a)))
    ind-β e P m i a =
      ap
        (λ φ →
          φ
            (supplied P (ind e P m) (shape (Scheme.rule s i))
              (pr₁ (Generated.split M e (shape (Scheme.rule s i)) a))))
        ( extension-β (presented e (shape (Scheme.rule s i)))
            (λ k →
              Hypotheses P (shape (Scheme.rule s i)) k
              → P i (Generated.introduce M i k))
            (m i) a)

  ----------------------------------------------------------------------
  -- Hypotheses at the argument's own positions

  -- The positions of an argument over the generated family are those of
  -- the layer it splits into. At a sum the continuation's layer was moved
  -- along the identity of informations, and `carry` undoes that.

  Literal :
    {ν : Level} (P : (i : Scheme.Index s) → Generated.Carrier M i → Set ν)
    {X : Set (ℓ ⊔ κ)} (p : Poly ℓ κ (Scheme.Data s) X)
    → Args p G → Set (ℓ ⊔ ν)
  Literal P p a =
    (z : Position p G a) → P (pr₁ (input p G a z)) (pr₂ (input p G a z))

  carry :
    {ν : Level} (P : (i : Scheme.Index s) → Generated.Carrier M i → Set ν)
    {X : Set (ℓ ⊔ κ)} {Y : X → Set (ℓ ⊔ κ)}
    (q : (x : X) → Poly ℓ κ (Scheme.Data s) (Y x)) {x y : X} (c : x ＝ y)
    (l : Generated.Layer M (q x))
    → Hypotheses P (q y) (transport (λ w → Generated.Layer M (q w)) c l)
    → Hypotheses P (q x) l
  carry P q refl l h = h

  carry-supplied :
    {ν : Level} (P : (i : Scheme.Index s) → Generated.Carrier M i → Set ν)
    (S : (i : Scheme.Index s) (t : Generated.Carrier M i) → P i t)
    {X : Set (ℓ ⊔ κ)} {Y : X → Set (ℓ ⊔ κ)}
    (q : (x : X) → Poly ℓ κ (Scheme.Data s) (Y x)) {x y : X} (c : x ＝ y)
    (l : Generated.Layer M (q x))
    → carry P q c l
        (supplied P S (q y)
          (transport (λ w → Generated.Layer M (q w)) c l))
      ＝ supplied P S (q x) l
  carry-supplied P S q refl l = refl

  transfer :
    {ν : Level} (e : Extensionality ℓ κ)
    (P : (i : Scheme.Index s) → Generated.Carrier M i → Set ν)
    {X : Set (ℓ ⊔ κ)} (p : Poly ℓ κ (Scheme.Data s) X) (a : Args p G)
    → Hypotheses P p (pr₁ (Generated.split M e p a)) → Literal P p a
  transfer e P (var i) a h z = h z
  transfer e P (con A) a h (lift ())
  transfer e P (sigma p q) (a , b) h (inl z) =
    transfer e P p a (λ y → h (inl y)) z
  transfer e P (sigma p q) (a , b) h (inr z) =
    transfer e P (q (info p G a)) b
      ( carry P q (pr₂ (Generated.split M e p a) ⁻¹)
          (pr₁ (Generated.split M e (q (info p G a)) b))
          (λ y → h (inr y)))
      z
  transfer e P (pi A p) f h (x , z) =
    transfer e P (p x) (f x) (λ y → h (x , y)) z

  transfer-β :
    {ν : Level} (e : Extensionality ℓ κ)
    (P : (i : Scheme.Index s) → Generated.Carrier M i → Set ν)
    (S : (i : Scheme.Index s) (t : Generated.Carrier M i) → P i t)
    {X : Set (ℓ ⊔ κ)} (p : Poly ℓ κ (Scheme.Data s) X) (a : Args p G)
    (z : Position p G a)
    → transfer e P p a
        (supplied P S p (pr₁ (Generated.split M e p a))) z
      ＝ S (pr₁ (input p G a z)) (pr₂ (input p G a z))
  transfer-β e P S (var i) a z = refl
  transfer-β e P S (con A) a (lift ())
  transfer-β e P S (sigma p q) (a , b) (inl z) = transfer-β e P S p a z
  transfer-β e P S (sigma p q) (a , b) (inr z) =
    ap
      (λ h → transfer e P (q (info p G a)) b h z)
      ( carry-supplied P S q (pr₂ (Generated.split M e p a) ⁻¹)
          (pr₁ (Generated.split M e (q (info p G a)) b)))
    ∙ transfer-β e P S (q (info p G a)) b z
  transfer-β e P S (pi A p) f (x , z) = transfer-β e P S (p x) (f x) z

  ----------------------------------------------------------------------
  -- The elimination rule on literal arguments

  Step :
    {ν : Level} → Extensionality ℓ κ
    → ((i : Scheme.Index s) → Generated.Carrier M i → Set ν) → Set (ℓ ⊔ ν)
  Step e P =
    (i : Scheme.Index s) (a : Args (shape (Scheme.rule s i)) G)
    → Literal P (shape (Scheme.rule s i)) a
    → P i (Generated.make M e i a)

  source :
    {ν : Level} (e : Extensionality ℓ κ)
    (P : (i : Scheme.Index s) → Generated.Carrier M i → Set ν)
    → Step e P → (i : Scheme.Index s) (t : Generated.Carrier M i) → P i t
  source e P m =
    ind e P (λ i a h → m i a (transfer e P (shape (Scheme.rule s i)) a h))

  -- Its computation identity also uses extensionality for functions from
  -- the positions into the motive.
  source-β :
    {ν : Level} (e : Extensionality ℓ κ)
    (P : (i : Scheme.Index s) → Generated.Carrier M i → Set ν)
    → ((A : Set ℓ) (B : A → Set ν) → FunExt A B)
    → (m : Step e P) (i : Scheme.Index s)
      (a : Args (shape (Scheme.rule s i)) G)
    → source e P m i (Generated.make M e i a)
      ＝ m i a
          (λ z →
            source e P m
              (pr₁ (input (shape (Scheme.rule s i)) G a z))
              (pr₂ (input (shape (Scheme.rule s i)) G a z)))
  source-β e P motive m i a =
    ind-β e P
      (λ j b h → m j b (transfer e P (shape (Scheme.rule s j)) b h)) i a
    ∙ ap (m i a)
        ( motive (Position (shape (Scheme.rule s i)) G a)
            (λ z →
              P (pr₁ (input (shape (Scheme.rule s i)) G a z))
                (pr₂ (input (shape (Scheme.rule s i)) G a z)))
            (transfer e P (shape (Scheme.rule s i)) a
              (supplied P (source e P m) (shape (Scheme.rule s i))
                (pr₁ (Generated.split M e (shape (Scheme.rule s i)) a))))
            (λ z →
              source e P m
                (pr₁ (input (shape (Scheme.rule s i)) G a z))
                (pr₂ (input (shape (Scheme.rule s i)) G a z)))
            (transfer-β e P (source e P m) (shape (Scheme.rule s i)) a))
