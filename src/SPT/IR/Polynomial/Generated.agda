{-# OPTIONS --safe --without-K #-}

module SPT.IR.Polynomial.Generated where

-- The generated part of an algebra M of a scheme. The recursive inputs of
-- an argument are its positions (`Position`, `input`). Derivations are the
-- closed trees of the signature whose operations at (i , c) are the
-- arguments that M sends to c at i, with one child at each input
-- (`Operation`, `signature`, `Der`); their total at each index, read out
-- through M, is the generated family (`Carrier`, `generated`). A layer is
-- an argument over M with a derivation at each position (`Layer`): it
-- introduces (`introduce`), every derivation exposes one (`expose`), and
-- induction over derivations computes by refl (`Method`, `ind`, `ind-β`).
-- Under extensionality an argument over the generated family splits into a
-- layer with the same information (`split`), so the generated family is
-- closed under its own rules with their output law (`make`, `make-β`), and
-- it folds into every algebra, keeping the readouts (`Witness`, `assemble`,
-- `folding`, `fold`, `fold-value`).

open import SPT.Base
open import SPT.Foundation.Signature using (Signature)
open import SPT.Foundation.Tree using (hole; node; History)
import SPT.Foundation.Tree.Fold as Fold

open import SPT.IR.Polynomial using
  (Poly; var; con; sigma; pi; Family; carrier; readout; Args; info;
   shape; output; Scheme; Extensionality)
open import SPT.IR.Polynomial.Action using (pair-info)
open import SPT.IR.Polynomial.Algebra using (Algebra)

------------------------------------------------------------------------
-- Recursive inputs of an argument

module _ {ι ℓ κ : Level} {I : Set ι} {D : I → Set (ℓ ⊔ κ)} where

  Position :
    {X : Set (ℓ ⊔ κ)} (p : Poly ℓ κ D X) (Z : Family ℓ κ D) → Args p Z
    → Set ℓ
  Position (var i) Z a = Lift ℓ 𝟙
  Position (con A) Z a = Lift ℓ 𝟘
  Position (sigma p q) Z (a , b) =
    Position p Z a ⊎ Position (q (info p Z a)) Z b
  Position (pi A p) Z f = Σ A (λ x → Position (p x) Z (f x))

  input :
    {X : Set (ℓ ⊔ κ)} (p : Poly ℓ κ D X) (Z : Family ℓ κ D) (a : Args p Z)
    → Position p Z a → Σ I (carrier Z)
  input (var i) Z a _ = i , a
  input (con A) Z a (lift ())
  input (sigma p q) Z (a , b) (inl z) = input p Z a z
  input (sigma p q) Z (a , b) (inr z) = input (q (info p Z a)) Z b z
  input (pi A p) Z f (x , z) = input (p x) Z (f x) z

-- Dependent case analysis on a sum and on the empty positions.

both :
  {α β ν : Level} {A : Set α} {B : Set β} (C : A ⊎ B → Set ν)
  → ((a : A) → C (inl a)) → ((b : B) → C (inr b)) → (z : A ⊎ B) → C z
both C f g (inl a) = f a
both C f g (inr b) = g b

nowhere : {ℓ ν : Level} (C : Lift ℓ 𝟘 → Set ν) (z : Lift ℓ 𝟘) → C z
nowhere C (lift ())

------------------------------------------------------------------------
-- Derivations over an algebra

-- An operation at (i , c) is an argument that M sends to c at i, so it
-- fixes its result literally and stores no identity.

module _ {ℓ κ : Level} {s : Scheme ℓ κ} (M : Algebra s) where

  open Algebra M using (family; operation; law)
  open Scheme s using (Index; Data; rule)

  data Operation : Σ Index (carrier family) → Set ℓ where
    apply :
      (i : Index) (u : Args (shape (rule i)) family)
      → Operation (i , operation i u)

  positions : {j : Σ Index (carrier family)} → Operation j → Set ℓ
  positions (apply i u) = Position (shape (rule i)) family u

  child :
    {j : Σ Index (carrier family)} (o : Operation j) → positions o
    → Σ Index (carrier family)
  child (apply i u) z = input (shape (rule i)) family u z

  signature : Signature ℓ ℓ ℓ
  signature = record
    { Judgment = Σ Index (carrier family)
    ; Op = Operation
    ; Pos = positions
    ; boundary = child
    }

  Der : Σ Index (carrier family) → Set ℓ
  Der = History signature

  Carrier : Index → Set ℓ
  Carrier i = Σ (carrier family i) (λ c → Der (i , c))

  generated : Family ℓ κ Data
  generated = record
    { carrier = Carrier
    ; readout = λ i x → readout family i (pr₁ x)
    }

------------------------------------------------------------------------
-- Layers, introduction and exposure

  Layer : {X : Set (ℓ ⊔ κ)} → Poly ℓ κ Data X → Set ℓ
  Layer p =
    Σ (Args p family)
      (λ u → (z : Position p family u) → Der (input p family u z))

  introduce : (i : Index) → Layer (shape (rule i)) → Carrier i
  introduce i l = operation i (pr₁ l) , node (apply i (pr₁ l)) (pr₂ l)

  expose : (i : Index) → Carrier i → Layer (shape (rule i))
  expose i (_ , hole ())
  expose i (_ , node (apply .i u) c) = u , c

  expose-introduce :
    (i : Index) (l : Layer (shape (rule i))) → expose i (introduce i l) ＝ l
  expose-introduce i l = refl

  introduce-expose :
    (i : Index) (t : Carrier i) → introduce i (expose i t) ＝ t
  introduce-expose i (_ , hole ())
  introduce-expose i (_ , node (apply .i u) c) = refl

------------------------------------------------------------------------
-- Induction over derivations

  -- A method treats every layer given a hypothesis at each of its
  -- positions. Induction is Fold.induction on the derivation.

  Method : {ν : Level} → ((i : Index) → Carrier i → Set ν) → Set (ℓ ⊔ ν)
  Method P =
    (i : Index) (l : Layer (shape (rule i)))
    → ((z : Position (shape (rule i)) family (pr₁ l))
      → P (pr₁ (input (shape (rule i)) family (pr₁ l) z))
          (pr₂ (input (shape (rule i)) family (pr₁ l) z) , pr₂ l z))
    → P i (introduce i l)

  no-hole :
    {ν : Level} (P : (i : Index) → Carrier i → Set ν)
    {j : Σ Index (carrier family)} (x : 𝟘) → P (pr₁ j) (pr₂ j , hole x)
  no-hole P ()

  step :
    {ν : Level} (P : (i : Index) → Carrier i → Set ν) → Method P
    → {j : Σ Index (carrier family)} (o : Operation j)
    (xs : (z : positions o) → Der (child o z))
    → ((z : positions o) → P (pr₁ (child o z)) (pr₂ (child o z) , xs z))
    → P (pr₁ j) (pr₂ j , node o xs)
  step P method (apply i u) xs hypotheses = method i (u , xs) hypotheses

  ind :
    {ν : Level} (P : (i : Index) → Carrier i → Set ν) → Method P
    → (i : Index) (t : Carrier i) → P i t
  ind P method i t =
    Fold.induction
      (λ (j : Σ Index (carrier family)) (d : Der j) → P (pr₁ j) (pr₂ j , d))
      (no-hole P)
      (step P method)
      (pr₂ t)

  ind-β :
    {ν : Level} (P : (i : Index) → Carrier i → Set ν) (method : Method P)
    (i : Index) (l : Layer (shape (rule i)))
    → ind P method i (introduce i l)
      ＝ method i l
          (λ z →
            ind P method (pr₁ (input (shape (rule i)) family (pr₁ l) z))
              (pr₂ (input (shape (rule i)) family (pr₁ l) z) , pr₂ l z))
  ind-β P method i l = refl

------------------------------------------------------------------------
-- Arguments over the generated family

  -- An argument over the generated family splits into a layer: its heads
  -- over M and the derivations at their positions, with the same
  -- information. At a sum the heads' information is identified with the
  -- argument's before the continuation is read; at a product
  -- extensionality identifies the information functions.

  split :
    Extensionality ℓ κ → {X : Set (ℓ ⊔ κ)} (p : Poly ℓ κ Data X)
    (a : Args p generated)
    → Σ (Layer p) (λ l → info p family (pr₁ l) ＝ info p generated a)
  split extensionality (var i) a = (pr₁ a , (λ _ → pr₂ a)) , refl
  split extensionality (con A) a =
    (a , nowhere (λ z → Der (input (con A) family a z))) , refl
  split extensionality (sigma {X} {Y} p q) (a , b) =
    let left = split extensionality p a
        right = split extensionality (q (info p generated a)) b
        moved = transport (λ x → Layer (q x)) (pr₂ left ⁻¹) (pr₁ right)
    in
    ( ( pr₁ (pr₁ left) , pr₁ moved)
    , both
        (λ z →
          Der (input (sigma p q) family (pr₁ (pr₁ left) , pr₁ moved) z))
        (pr₂ (pr₁ left))
        (pr₂ moved)) ,
    ( pair-info (λ x → Layer (q x)) Y (λ x l → info (q x) family (pr₁ l))
        (pr₂ left ⁻¹) (pr₁ right)
    ∙ ap (λ y → (info p generated a , y)) (pr₂ right))
  split extensionality (pi A {Y} p) f =
    let branch = λ x → split extensionality (p x) (f x)
    in
    ( (λ x → pr₁ (pr₁ (branch x)))
    , (λ w → pr₂ (pr₁ (branch (pr₁ w))) (pr₂ w))) ,
    extensionality A Y
      (λ x → info (p x) family (pr₁ (pr₁ (branch x))))
      (λ x → info (p x) generated (f x))
      (λ x → pr₂ (branch x))

  -- Introduction on arguments over the generated family itself.
  make :
    Extensionality ℓ κ → (i : Index) → Args (shape (rule i)) generated
    → Carrier i
  make extensionality i a =
    introduce i (pr₁ (split extensionality (shape (rule i)) a))

  make-β :
    (extensionality : Extensionality ℓ κ) (i : Index)
    (a : Args (shape (rule i)) generated)
    → readout generated i (make extensionality i a)
      ＝ output (rule i) (info (shape (rule i)) generated a)
  make-β extensionality i a =
    law i (pr₁ (pr₁ (split extensionality (shape (rule i)) a)))
    ∙ ap (output (rule i)) (pr₂ (split extensionality (shape (rule i)) a))

------------------------------------------------------------------------
-- Folding into any algebra

  -- An element of N reading out as a given element of M.
  Witness : (N : Algebra s) (i : Index) → carrier family i → Set (ℓ ⊔ κ)
  Witness N i c =
    Σ (carrier (Algebra.family N) i)
      (λ y → readout (Algebra.family N) i y ＝ readout family i c)

  -- An argument over M with a witness in N at each position assembles to
  -- an argument over N with the same information.
  assemble :
    Extensionality ℓ κ → (N : Algebra s) {X : Set (ℓ ⊔ κ)}
    (p : Poly ℓ κ Data X) (u : Args p family)
    → ((z : Position p family u)
      → Witness N (pr₁ (input p family u z)) (pr₂ (input p family u z)))
    → Σ (Args p (Algebra.family N))
        (λ b → info p (Algebra.family N) b ＝ info p family u)
  assemble extensionality N (var i) u w = w (lift ⋆)
  assemble extensionality N (con A) u w = u , refl
  assemble extensionality N (sigma {X} {Y} p q) (u , v) w =
    let left = assemble extensionality N p u (λ z → w (inl z))
        right =
          assemble extensionality N (q (info p family u)) v
            (λ z → w (inr z))
    in
    ( pr₁ left
    , transport (λ x → Args (q x) (Algebra.family N)) (pr₂ left ⁻¹)
        (pr₁ right)) ,
    ( pair-info (λ x → Args (q x) (Algebra.family N)) Y
        (λ x → info (q x) (Algebra.family N)) (pr₂ left ⁻¹) (pr₁ right)
    ∙ ap (λ y → (info p family u , y)) (pr₂ right))
  assemble extensionality N (pi A {Y} p) f w =
    let branch =
          λ x → assemble extensionality N (p x) (f x) (λ z → w (x , z))
    in
    (λ x → pr₁ (branch x)) ,
    extensionality A Y
      (λ x → info (p x) (Algebra.family N) (pr₁ (branch x)))
      (λ x → info (p x) family (f x))
      (λ x → pr₂ (branch x))

  -- The fold sends each layer to N's operation at the assembled argument,
  -- with its readout identity at every node.
  folding :
    Extensionality ℓ κ → (N : Algebra s) (i : Index) (t : Carrier i)
    → Witness N i (pr₁ t)
  folding extensionality N =
    ind (λ i t → Witness N i (pr₁ t))
      (λ i l hypotheses →
        let assembled =
              assemble extensionality N (shape (rule i)) (pr₁ l) hypotheses
        in
        Algebra.operation N i (pr₁ assembled) ,
        ( Algebra.law N i (pr₁ assembled)
        ∙ (ap (output (rule i)) (pr₂ assembled) ∙ law i (pr₁ l) ⁻¹)))

  fold :
    Extensionality ℓ κ → (N : Algebra s) (i : Index) → Carrier i
    → carrier (Algebra.family N) i
  fold extensionality N i t = pr₁ (folding extensionality N i t)

  fold-value :
    (extensionality : Extensionality ℓ κ) (N : Algebra s) (i : Index)
    (t : Carrier i)
    → readout (Algebra.family N) i (fold extensionality N i t)
      ＝ readout generated i t
  fold-value extensionality N i t = pr₂ (folding extensionality N i t)
