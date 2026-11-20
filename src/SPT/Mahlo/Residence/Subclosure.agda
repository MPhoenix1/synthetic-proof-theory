{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Residence.Subclosure where

-- The least subclosure of a closure. A closure L of a Tarski family on a
-- small carrier A makes A a small family in its own right, with L's codes
-- as its formers (child-formers) and L's inner family as its operator. A
-- closure K of that family, read through L, is a closure of the original
-- one: each of K's names is followed by L's name of its code (`onward`),
-- the interpretation is the composite (`through`), and it is least whenever
-- K is (`through-least`). Generated membership over A is such a closure and
-- is least, with no induction–recursion: the least subclosure of L
-- (subclosure, subclosure-least). So one small closure for an operator
-- gives a small least closure for it (subclosure-small), and Mahlo gives
-- one for every operator (mahlo-small). In a least closure every code is
-- reached by exactly one witness (reach, reach-unique), so a least closure
-- is isomorphic to its least subclosure (reached), by extensionality at the
-- branches.

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Isomorphisms using (_≅_)
open import SPT.Mahlo.Decoding using (child-formers)
open import SPT.Mahlo.Specification using
  (Family; Operator; Formers; Name; Decode; map; Closure; Reflection; Mahlo)
open import SPT.Mahlo.Residence.Absorption using
  (Methods; Induction; Small-Least)
open import SPT.Mahlo.Residence.Membership using
  ( along; Form; emptyᶠ; unitᶠ; twoᶠ; naturalᶠ; productᶠ; sumᶠ; treeᶠ
  ; identityᶠ; resultᶠ; branchᶠ; generated; least
  )
import SPT.Mahlo.Residence.Membership as Membership

------------------------------------------------------------------------
-- Closures through a closure

-- A closure K of L's own family, read through L: K's codes name L's
-- codes, which name the parent's codes. Each naming identification is K's,
-- carried by L's interpretation, followed by L's, and the methods and laws
-- of K serve unchanged.

module _
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ}
  {Q : Formers C D} {Ψ : Operator D} {A : Set ℓ}
  where

  -- A name in K of a code that L names by c is a name of c.
  onward :
    (L : Closure Q Ψ A)
    {X : Set ℓ}
    (K : Closure (child-formers L) (Closure.inner L) X)
    {c : C}
    (n : Name (Closure.interpret L) c)
    → Name (Closure.interpret K) (pr₁ n)
    → Name (λ x → Closure.interpret L (Closure.interpret K x)) c
  onward L K n m =
    pr₁ m , (ap (Closure.interpret L) (pr₂ m) ∙ pr₂ n)

  -- Mathematical shape:
  --
  --   interpret (through L K) x = interpret L (interpret K x),
  --   inner (through L K)       = inner K.
  through :
    (L : Closure Q Ψ A)
    {X : Set ℓ}
    → Closure (child-formers L) (Closure.inner L) X
    → Closure Q Ψ X
  through L K =
    let I = Closure.interpret L
        J = Closure.interpret K
    in record
      { interpret = λ x → I (J x)
      ; empty = onward L K (Closure.empty L) (Closure.empty K)
      ; unit = onward L K (Closure.unit L) (Closure.unit K)
      ; two = onward L K (Closure.two L) (Closure.two K)
      ; natural = onward L K (Closure.natural L) (Closure.natural K)
      ; product = λ F →
          onward L K
            ( Closure.product L (map (Decode D I) J F))
            ( Closure.product K F)
      ; sum = λ F →
          onward L K
            ( Closure.sum L (map (Decode D I) J F))
            ( Closure.sum K F)
      ; tree = λ F →
          onward L K
            ( Closure.tree L (map (Decode D I) J F))
            ( Closure.tree K F)
      ; identity = λ a x y →
          onward L K (Closure.identity L (J a) x y)
            ( Closure.identity K a x y)
      ; inner = Closure.inner K
      ; inner-β = λ F →
          ap (map D I) (Closure.inner-β K F)
          ∙ Closure.inner-β L (map (Decode D I) J F)
      }

  inward :
      (L : Closure Q Ψ A)
      {X : Set ℓ}
      (K : Closure (child-formers L) (Closure.inner L) X)
      {ν : Level}
      (P : X → Set ν)
    → Methods (through L K) P
    → Methods K P
  inward L K P m = record
    { on-empty = Methods.on-empty m
    ; on-unit = Methods.on-unit m
    ; on-two = Methods.on-two m
    ; on-natural = Methods.on-natural m
    ; on-product = Methods.on-product m
    ; on-sum = Methods.on-sum m
    ; on-tree = Methods.on-tree m
    ; on-identity = Methods.on-identity m
    ; on-result = Methods.on-result m
    ; on-branch = Methods.on-branch m
    }

  through-least :
      (L : Closure Q Ψ A)
      {X : Set ℓ}
      (K : Closure (child-formers L) (Closure.inner L) X)
      (ν : Level)
    → Induction K ν
    → Induction (through L K) ν
  through-least L K ν ind = record
    { induction = λ P m → Induction.induction ind P (inward L K P m)
    ; induction-empty = λ P m →
        Induction.induction-empty ind P (inward L K P m)
    ; induction-unit = λ P m →
        Induction.induction-unit ind P (inward L K P m)
    ; induction-two = λ P m →
        Induction.induction-two ind P (inward L K P m)
    ; induction-natural = λ P m →
        Induction.induction-natural ind P (inward L K P m)
    ; induction-product = λ P m φ →
        Induction.induction-product ind P (inward L K P m) φ
    ; induction-sum = λ P m φ →
        Induction.induction-sum ind P (inward L K P m) φ
    ; induction-tree = λ P m φ →
        Induction.induction-tree ind P (inward L K P m) φ
    ; induction-identity = λ P m a x y →
        Induction.induction-identity ind P (inward L K P m) a x y
    ; induction-result = λ P m φ →
        Induction.induction-result ind P (inward L K P m) φ
    ; induction-branch = λ P m φ y →
        Induction.induction-branch ind P (inward L K P m) φ y
    }

------------------------------------------------------------------------
-- The least subclosure

-- Mathematical shape: Σ(a : A). Form(L's formers, L's inner family)(a),
-- the codes of L reached from its formers and its inner family.

  subclosure :
      (L : Closure Q Ψ A)
    → Closure Q Ψ (Σ A (Form (child-formers L) (Closure.inner L)))
  subclosure L = through L (generated (child-formers L) (Closure.inner L))

  subclosure-least :
      (L : Closure Q Ψ A)
      (ν : Level)
    → Induction (subclosure L) ν
  subclosure-least L ν =
    through-least L (generated (child-formers L) (Closure.inner L)) ν
      ( least (child-formers L) (Closure.inner L) ν)

  subclosure-small :
      (L : Closure Q Ψ A)
      (ν : Level)
    → Small-Least Q Ψ ν
  subclosure-small L ν = record
    { carrier = Σ A (Form (child-formers L) (Closure.inner L))
    ; closure = subclosure L
    ; induction = subclosure-least L ν
    }

------------------------------------------------------------------------
-- A least closure is its least subclosure

-- In a least closure, induction reaches every code with a witness
-- (reach), and that witness is the only one (reach-unique): a witness
-- is formed from witnesses of the parts, and reaching a formed code
-- returns the witnesses reached at its parts.

  -- The family of reached codes over a family of codes.
  reached-family :
      (L : Closure Q Ψ A)
      (φ : Family (Decode D (Closure.interpret L)))
    → Form (child-formers L) (Closure.inner L) (pr₁ φ)
    → ((x : Decode D (Closure.interpret L) (pr₁ φ))
      → Form (child-formers L) (Closure.inner L) (pr₂ φ x))
    → Family
        (λ (a : Σ A (Form (child-formers L) (Closure.inner L)))
          → Decode D (Closure.interpret L) (pr₁ a))
  reached-family L φ head branches =
    (pr₁ φ , head) , (λ x → pr₂ φ x , branches x)

  reach-methods :
      (L : Closure Q Ψ A)
    → Methods L (Form (child-formers L) (Closure.inner L))
  reach-methods L = record
    { on-empty = emptyᶠ
    ; on-unit = unitᶠ
    ; on-two = twoᶠ
    ; on-natural = naturalᶠ
    ; on-product = λ φ head branches →
        productᶠ (reached-family L φ head branches)
    ; on-sum = λ φ head branches →
        sumᶠ (reached-family L φ head branches)
    ; on-tree = λ φ head branches →
        treeᶠ (reached-family L φ head branches)
    ; on-identity = λ a x y head → identityᶠ (a , head) x y
    ; on-result = λ φ head branches →
        resultᶠ (reached-family L φ head branches)
    ; on-branch = λ φ y head branches →
        branchᶠ (reached-family L φ head branches) y
    }

  reach :
      (L : Closure Q Ψ A)
    → Induction L ℓ
    → (a : A)
    → Form (child-formers L) (Closure.inner L) a
  reach L ind =
    Induction.induction ind (Form (child-formers L) (Closure.inner L))
      ( reach-methods L)

  -- Reaching the parts of a family gives the witnesses given for them.
  rejoin :
      (L : Closure Q Ψ A)
      (ind : Induction L ℓ)
      (extensionality : (X : Set ℓ) (B : X → Set ℓ) → FunExt X B)
      (φ : Family (Decode D (Closure.interpret L)))
      {ν : Level} {B : Set ν}
      (k : Form (child-formers L) (Closure.inner L) (pr₁ φ)
        → ((x : Decode D (Closure.interpret L) (pr₁ φ))
          → Form (child-formers L) (Closure.inner L) (pr₂ φ x))
        → B)
      {head : Form (child-formers L) (Closure.inner L) (pr₁ φ)}
      {branches :
        (x : Decode D (Closure.interpret L) (pr₁ φ))
        → Form (child-formers L) (Closure.inner L) (pr₂ φ x)}
    → reach L ind (pr₁ φ) ＝ head
    → ((x : Decode D (Closure.interpret L) (pr₁ φ))
      → reach L ind (pr₂ φ x) ＝ branches x)
    → k (reach L ind (pr₁ φ))
        (λ x → reach L ind (pr₂ φ x))
      ＝ k head branches
  rejoin L ind extensionality φ k {branches = branches} e es =
    ap₂ k e
      ( extensionality (Decode D (Closure.interpret L) (pr₁ φ))
          ( λ x → Form (child-formers L) (Closure.inner L) (pr₂ φ x))
          ( λ x → reach L ind (pr₂ φ x)) branches es)

  unique-methods :
      (L : Closure Q Ψ A)
      (ind : Induction L ℓ)
      (extensionality : (X : Set ℓ) (B : X → Set ℓ) → FunExt X B)
    → Methods (generated (child-formers L) (Closure.inner L))
        (λ w → reach L ind (pr₁ w) ＝ pr₂ w)
  unique-methods L ind extensionality = record
    { on-empty =
        Induction.induction-empty ind
          ( Form (child-formers L) (Closure.inner L)) (reach-methods L)
    ; on-unit =
        Induction.induction-unit ind
          ( Form (child-formers L) (Closure.inner L)) (reach-methods L)
    ; on-two =
        Induction.induction-two ind
          ( Form (child-formers L) (Closure.inner L)) (reach-methods L)
    ; on-natural =
        Induction.induction-natural ind
          ( Form (child-formers L) (Closure.inner L)) (reach-methods L)
    ; on-product = λ φ head branches →
        Induction.induction-product ind
          ( Form (child-formers L) (Closure.inner L)) (reach-methods L)
          ( along (Decode D (Closure.interpret L)) pr₁ φ)
        ∙ rejoin L ind extensionality
            ( along (Decode D (Closure.interpret L)) pr₁ φ)
            ( λ h b →
                productᶠ
                  ( reached-family L
                      ( along (Decode D (Closure.interpret L)) pr₁ φ) h b))
            head branches
    ; on-sum = λ φ head branches →
        Induction.induction-sum ind
          ( Form (child-formers L) (Closure.inner L)) (reach-methods L)
          ( along (Decode D (Closure.interpret L)) pr₁ φ)
        ∙ rejoin L ind extensionality
            ( along (Decode D (Closure.interpret L)) pr₁ φ)
            ( λ h b →
                sumᶠ
                  ( reached-family L
                      ( along (Decode D (Closure.interpret L)) pr₁ φ) h b))
            head branches
    ; on-tree = λ φ head branches →
        Induction.induction-tree ind
          ( Form (child-formers L) (Closure.inner L)) (reach-methods L)
          ( along (Decode D (Closure.interpret L)) pr₁ φ)
        ∙ rejoin L ind extensionality
            ( along (Decode D (Closure.interpret L)) pr₁ φ)
            ( λ h b →
                treeᶠ
                  ( reached-family L
                      ( along (Decode D (Closure.interpret L)) pr₁ φ) h b))
            head branches
    ; on-identity = λ a x y head →
        Induction.induction-identity ind
          ( Form (child-formers L) (Closure.inner L)) (reach-methods L)
          ( pr₁ a) x y
        ∙ ap (λ h → identityᶠ (pr₁ a , h) x y) head
    ; on-result = λ φ head branches →
        Induction.induction-result ind
          ( Form (child-formers L) (Closure.inner L)) (reach-methods L)
          ( along (Decode D (Closure.interpret L)) pr₁ φ)
        ∙ rejoin L ind extensionality
            ( along (Decode D (Closure.interpret L)) pr₁ φ)
            ( λ h b →
                resultᶠ
                  ( reached-family L
                      ( along (Decode D (Closure.interpret L)) pr₁ φ) h b))
            head branches
    ; on-branch = λ φ y head branches →
        Induction.induction-branch ind
          ( Form (child-formers L) (Closure.inner L)) (reach-methods L)
          ( along (Decode D (Closure.interpret L)) pr₁ φ) y
        ∙ rejoin L ind extensionality
            ( along (Decode D (Closure.interpret L)) pr₁ φ)
            ( λ h b →
                branchᶠ
                  ( reached-family L
                      ( along (Decode D (Closure.interpret L)) pr₁ φ) h b)
                  y)
            head branches
    }

  reach-unique :
      (L : Closure Q Ψ A)
      (ind : Induction L ℓ)
      (extensionality : (X : Set ℓ) (B : X → Set ℓ) → FunExt X B)
      {a : A}
      (r : Form (child-formers L) (Closure.inner L) a)
    → reach L ind a ＝ r
  reach-unique L ind extensionality r =
    Membership.induction (child-formers L) (Closure.inner L)
      ( λ w → reach L ind (pr₁ w) ＝ pr₂ w)
      ( unique-methods L ind extensionality)
      r

  reached :
      (L : Closure Q Ψ A)
    → Induction L ℓ
    → ((X : Set ℓ) (B : X → Set ℓ) → FunExt X B)
    → A ≅ Σ A (Form (child-formers L) (Closure.inner L))
  reached L ind extensionality = record
    { forward = λ a → a , reach L ind a
    ; backward = pr₁
    ; backward-forward = λ a → refl
    ; forward-backward = λ w →
        ap (λ r → pr₁ w , r)
          ( reach-unique L ind extensionality (pr₂ w))
    }

------------------------------------------------------------------------
-- Mahlo gives small least closures

module _
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ}
  {Q : Formers C D}
  where

  mahlo-small :
      Mahlo Q
    → (Ψ : Operator D)
      (ν : Level)
    → Small-Least Q Ψ ν
  mahlo-small mahlo Ψ ν =
    subclosure-small (Reflection.closure (Mahlo.reflect mahlo Ψ)) ν
