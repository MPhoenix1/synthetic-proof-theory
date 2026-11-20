{-# OPTIONS --safe --without-K #-}

module SPT.IR.Generated where

-- The generated part of an algebra M of a description γ, at any carrier
-- level. Derivations are the closed trees of the signature whose
-- operations at a code c are the shapes over the carrier that M sends to
-- c, with one child at each input (`Operation`, `signature`, `Der`). Their
-- total G, decoded by t, is the IR type of γ when M is small. It is the
-- restriction of (K , value) to the derivations, so an argument over
-- (G , t) splits into Restriction's heads and children there: `make`
-- introduces, `make-β` decodes, and `ind` eliminates into every level,
-- computing by refl (`ind-β`, `ind-make`). For the identity algebra it is
-- the raised fixed point of γ (Comparison).

open import SPT.Base
open import SPT.Foundation.Signature using (Signature)
open import SPT.Foundation.Tree using (hole; node; History)
import SPT.Foundation.Tree.Fold as Fold

open import SPT.IR.Algebra using (Algebra; Law)
open import SPT.IR.Description using
  (Desc; indexed; Shape; Mark)
open import SPT.IR.Restriction using
  (Position; input; heads; children; heads-β)

------------------------------------------------------------------------
-- Derivations over an algebra

-- An operation at c is a shape that M sends to c, so the operation fixes
-- its result literally and stores no identity.

module _
  {s κ j : Level} {E : Set j} {γ : Desc {s = s} E} (M : Algebra κ γ)
  where

  open Algebra M using (K; value; operation)

  data Operation : K → Set (s ⊔ κ) where
    apply : (a : Shape γ (indexed K value)) → Operation (operation a)

  positions : {c : K} → Operation c → Set s
  positions (apply a) = Position γ (indexed K value) a

  child : {c : K} (o : Operation c) → positions o → K
  child (apply a) p = input γ (indexed K value) a p

  signature : Signature κ (s ⊔ κ) s
  signature = record
    { Judgment = K
    ; Op = Operation
    ; Pos = positions
    ; boundary = child
    }

  Der : K → Set (s ⊔ κ)
  Der = History signature

  G : Set (s ⊔ κ)
  G = Σ K Der

  t : G → E
  t g = value (pr₁ g)

------------------------------------------------------------------------
-- Introduction and decoding

  -- An argument over the generated part has heads over the carrier and a
  -- derivation at each of their inputs; the decodings agree, since t is
  -- value on heads.

  make : Shape γ (indexed G t) → G
  make z =
    operation (heads value Der γ z) ,
    node (apply (heads value Der γ z)) (children value Der γ z)

  make-β :
    Law M → (z : Shape γ (indexed G t))
    → t (make z) ＝ Mark γ (indexed G t) z
  make-β law z = law (heads value Der γ z) ∙ heads-β value Der γ z

------------------------------------------------------------------------
-- Dependent elimination

  -- A method treats every operation given its children and a hypothesis
  -- at each of them. Induction is Fold.induction on the derivation.

  Method : {ν : Level} → (G → Set ν) → Set (s ⊔ κ ⊔ ν)
  Method P =
    (a : Shape γ (indexed K value))
    (xs : (p : Position γ (indexed K value) a)
      → Der (input γ (indexed K value) a p))
    → ((p : Position γ (indexed K value) a)
      → P (input γ (indexed K value) a p , xs p))
    → P (operation a , node (apply a) xs)

  no-hole : {ν : Level} (P : G → Set ν) {c : K} (x : 𝟘) → P (c , hole x)
  no-hole P ()

  step :
    {ν : Level} (P : G → Set ν) → Method P → {c : K} (o : Operation c)
    (xs : (p : positions o) → Der (child o p))
    → ((p : positions o) → P (child o p , xs p)) → P (c , node o xs)
  step P method (apply a) xs hypotheses = method a xs hypotheses

  ind : {ν : Level} (P : G → Set ν) → Method P → (g : G) → P g
  ind P method g =
    Fold.induction
      (λ (c : K) (d : Der c) → P (c , d))
      (no-hole P)
      (step P method)
      (pr₂ g)

  ind-β :
    {ν : Level} (P : G → Set ν) (method : Method P)
    (a : Shape γ (indexed K value))
    (xs : (p : Position γ (indexed K value) a)
      → Der (input γ (indexed K value) a p))
    → ind P method (operation a , node (apply a) xs)
      ＝ method a xs
          (λ p → ind P method (input γ (indexed K value) a p , xs p))
  ind-β P method a xs = refl

  ind-make :
    {ν : Level} (P : G → Set ν) (method : Method P)
    (z : Shape γ (indexed G t))
    → ind P method (make z)
      ＝ method (heads value Der γ z) (children value Der γ z)
          (λ p →
            ind P method
              ( input γ (indexed K value) (heads value Der γ z) p
              , children value Der γ z p))
  ind-make P method z = refl
