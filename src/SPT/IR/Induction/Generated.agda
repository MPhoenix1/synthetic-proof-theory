{-# OPTIONS --safe --without-K #-}

module SPT.IR.Induction.Generated where

-- The generated part of an algebra satisfies induction on source
-- arguments, Dybjer and Setzer's elimination rule: the specification of
-- Base.Induction at Generated's introduction, whose arguments are the
-- source arguments with their inputs. Source arguments and layers
-- are isomorphic, through split and join with their two laws
-- (`arguments`, Restriction's split and join at the derivations). The
-- positions of a source argument are those of its heads, so hypotheses at
-- a layer's positions are hypotheses at the argument's (`Hypotheses`,
-- Restriction's `transfer`). A step at source arguments gives
-- a method at layers by transport along the coherent law
-- split (join l) ＝ l (`step`, `method`, Foundation.HalfAdjoint.Extension),
-- and induction over derivations with it is induction on source arguments
-- (`source`). Its computation identity (`source-β`): at split z the method
-- is the step there (`extension-β`), and the transferred hypotheses of the
-- induction are its hypotheses at the inputs of z (Restriction's
-- `transfer-β`). The
-- isomorphism uses extensionality for families over positions
-- (split-join); the computation identity also uses it for functions from
-- positions into the motive.

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.HalfAdjoint.Extension using
  (extension; extension-β)
open import SPT.Foundation.Isomorphisms using (_≅_)

open import SPT.IR.Algebra using (Algebra)
import SPT.IR.Arguments as Arguments
open import SPT.IR.Description using (Desc; indexed; Shape)
import SPT.IR.Generated as Generated
open import SPT.IR.Polynomial using (Extensionality)
open import SPT.IR.Restriction using
  ( Position; input; heads; children; transfer; transfer-β; Layer; split
  ; join; join-split; split-join )

module _
  {s κ j : Level} {E : Set j} {γ : Desc {s = s} E} (M : Algebra κ γ)
  where

  open Algebra M using (K; value; operation)

  ----------------------------------------------------------------------
  -- Source arguments and layers

  arguments :
    Extensionality s κ
    → Shape γ (indexed (Generated.G M) (Generated.t M))
      ≅ Layer value (Generated.Der M) γ
  arguments extensionality = record
    { forward = split value (Generated.Der M) γ
    ; backward = join value (Generated.Der M) γ
    ; backward-forward = join-split value (Generated.Der M) γ
    ; forward-backward = split-join value (Generated.Der M) extensionality γ
    }

  ----------------------------------------------------------------------
  -- Hypotheses at a layer and at a source argument

  Hypotheses :
    {ν : Level} (P : Generated.G M → Set ν) → Layer value (Generated.Der M) γ
    → Set (s ⊔ ν)
  Hypotheses P l =
    (p : Position γ (indexed K value) (pr₁ l))
    → P (input γ (indexed K value) (pr₁ l) p , pr₂ l p)

  ----------------------------------------------------------------------
  -- Induction on source arguments

  -- A step at source arguments, read at the layer a source argument
  -- splits into.
  step :
    {ν : Level} (P : Generated.G M → Set ν)
    → Argument-Step (input γ (indexed (Generated.G M) (Generated.t M)))
        (Generated.make M) P
    → (z : Shape γ (indexed (Generated.G M) (Generated.t M)))
    → Hypotheses P (split value (Generated.Der M) γ z)
    → P (Arguments.layer M (split value (Generated.Der M) γ z))
  step P m z h = m z (transfer value (Generated.Der M) P γ z h)

  -- At any layer, the step at its join, carried along the coherent law
  -- (Foundation.HalfAdjoint.Extension).
  method :
    {ν : Level} (P : Generated.G M → Set ν) → Extensionality s κ
    → Argument-Step (input γ (indexed (Generated.G M) (Generated.t M)))
        (Generated.make M) P
    → (l : Layer value (Generated.Der M) γ) → Hypotheses P l
    → P (Arguments.layer M l)
  method P extensionality m l =
    extension (arguments extensionality)
      (λ k → Hypotheses P k → P (Arguments.layer M k)) (step P m) l

  source :
    Extensionality s κ → (ν : Level)
    → Argument-Induction (input γ (indexed (Generated.G M) (Generated.t M)))
        (Generated.make M) ν
  source extensionality ν P m =
    Generated.ind M P
      (λ a xs hypotheses → method P extensionality m (a , xs) hypotheses)

  source-β :
    (extensionality : Extensionality s κ) (ν : Level)
    → ((A : Set s) (B : A → Set ν) → FunExt A B)
    → Argument-Computation (input γ (indexed (Generated.G M) (Generated.t M)))
        (Generated.make M) (source extensionality ν)
  source-β extensionality ν motive P m z =
    ap
      (λ φ →
        φ (λ q →
          source extensionality ν P m
            ( input γ (indexed K value)
                (heads value (Generated.Der M) γ z) q
            , children value (Generated.Der M) γ z q)))
      ( extension-β (arguments extensionality)
          (λ k → Hypotheses P k → P (Arguments.layer M k)) (step P m) z)
    ∙ ap (m z)
        (motive (Position γ (indexed (Generated.G M) (Generated.t M)) z)
          (λ p → P (input γ (indexed (Generated.G M) (Generated.t M)) z p))
          (transfer value (Generated.Der M) P γ z
            (λ q →
              source extensionality ν P m
                ( input γ (indexed K value)
                    (heads value (Generated.Der M) γ z) q
                , children value (Generated.Der M) γ z q)))
          (λ p →
            source extensionality ν P m
              (input γ (indexed (Generated.G M) (Generated.t M)) z p))
          (transfer-β value (Generated.Der M) P (source extensionality ν P m)
            γ z))
