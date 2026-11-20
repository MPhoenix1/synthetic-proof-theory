{-# OPTIONS --safe --without-K --two-level #-}

module SPT.TwoLevel.Mahlo.StepAlgebra where

-- A labelled algebra of the Mahlo step gives the strict Mahlo rule.
-- Labelled specifies carriers with readouts, operations for the formers,
-- operator results and branches, and their strict laws in context.
-- Classification names those carriers, with to after from strictly the
-- identity. The theorem inner-law joins the result and branch laws;
-- strict-mahlo constructs Strict-Mahlo from both records. For the ambient
-- family the classification is the identity (ambient, ambient-mahlo).

open import Agda.Primitive using (SSet)
open import SPT.Base
open import SPT.Mahlo.Specification using
  (Family; Operator; Formers; Decode; map)
import SPT.Mahlo.Ambient as Ambient
open import SPT.TwoLevel.Coherence using
  (_≐_; same; apˢ; transportˢ; _∙ˢ_)
open import SPT.TwoLevel.Mahlo using (Strict-Mahlo)

------------------------------------------------------------------------
-- Labelled algebras and classifications

-- The label laws are specified summand by summand in context.
record Labelled {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ}
  (Q : Formers C D) : SSet (κ ⊔ lsuc ℓ) where
  field
    Carrier : Operator D → Set ℓ
    readout : (Ψ : Operator D) → Carrier Ψ → C

    empty unit two natural : (Ψ : Operator D) → Carrier Ψ
    product sum tree result : (Ψ : Operator D) →
      Family (Decode D (readout Ψ)) → Carrier Ψ
    identity : (Ψ : Operator D) (a : Carrier Ψ) →
      Decode D (readout Ψ) a → Decode D (readout Ψ) a → Carrier Ψ
    branch : (Ψ : Operator D) (F : Family (Decode D (readout Ψ))) →
      D (pr₁ (Ψ (map D (readout Ψ) F))) → Carrier Ψ

    empty-β : (λ (Ψ : Operator D) → readout Ψ (empty Ψ)) ≐
      (λ Ψ → Formers.empty Q)
    unit-β : (λ (Ψ : Operator D) → readout Ψ (unit Ψ)) ≐
      (λ Ψ → Formers.unit Q)
    two-β : (λ (Ψ : Operator D) → readout Ψ (two Ψ)) ≐
      (λ Ψ → Formers.two Q)
    natural-β : (λ (Ψ : Operator D) → readout Ψ (natural Ψ)) ≐
      (λ Ψ → Formers.natural Q)
    product-β :
      (λ (Ψ : Operator D) (F : Family (Decode D (readout Ψ))) →
        readout Ψ (product Ψ F)) ≐
      (λ Ψ F → Formers.product Q (map D (readout Ψ) F))
    sum-β :
      (λ (Ψ : Operator D) (F : Family (Decode D (readout Ψ))) →
        readout Ψ (sum Ψ F)) ≐
      (λ Ψ F → Formers.sum Q (map D (readout Ψ) F))
    tree-β :
      (λ (Ψ : Operator D) (F : Family (Decode D (readout Ψ))) →
        readout Ψ (tree Ψ F)) ≐
      (λ Ψ F → Formers.tree Q (map D (readout Ψ) F))
    result-β :
      (λ (Ψ : Operator D) (F : Family (Decode D (readout Ψ))) →
        readout Ψ (result Ψ F)) ≐
      (λ Ψ F → pr₁ (Ψ (map D (readout Ψ) F)))
    identity-β :
      (λ (Ψ : Operator D) (a : Carrier Ψ)
         (x y : Decode D (readout Ψ) a) →
        readout Ψ (identity Ψ a x y)) ≐
      (λ Ψ a x y → Formers.identity Q (readout Ψ a) x y)
    branch-β :
      (λ (Ψ : Operator D) (F : Family (Decode D (readout Ψ)))
         (y : D (pr₁ (Ψ (map D (readout Ψ) F)))) →
        readout Ψ (branch Ψ F y)) ≐
      (λ Ψ F y → pr₂ (Ψ (map D (readout Ψ) F)) y)

-- Only the strict section law to-from is required of the classification.
record Classification {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ}
  {Q : Formers C D} (M : Labelled Q) : SSet (κ ⊔ ℓ) where
  field
    code : Operator D → C
    to : (Ψ : Operator D) → D (code Ψ) → Labelled.Carrier M Ψ
    from : (Ψ : Operator D) → Labelled.Carrier M Ψ → D (code Ψ)
    to-from :
      (λ (Ψ : Operator D) (y : Labelled.Carrier M Ψ) → to Ψ (from Ψ y)) ≐
      (λ Ψ y → y)

------------------------------------------------------------------------
-- The algebra on the parent's decodings

module _
  {κ ℓ : Level} {C : Set κ} {D : C → Set ℓ} {Q : Formers C D}
  (M : Labelled Q) (K : Classification M)
  where

  open Classification K using (code; to; from; to-from)

  interpret : (Ψ : Operator D) → D (code Ψ) → C
  interpret Ψ x = Labelled.readout M Ψ (to Ψ x)

  lifted :
    (Ψ : Operator D) → Family (Decode D (interpret Ψ))
    → Family (Decode D (Labelled.readout M Ψ))
  lifted Ψ F = to Ψ (pr₁ F) , (λ x → to Ψ (pr₂ F x))

  at-lifted :
    ((Ψ : Operator D) → Family (Decode D (Labelled.readout M Ψ)) → C)
    → (Ψ : Operator D) → Family (Decode D (interpret Ψ)) → C
  at-lifted h Ψ F = h Ψ (lifted Ψ F)

  nullary-operation-reads :
    (o : (Ψ : Operator D) → Labelled.Carrier M Ψ)
    → (λ (Ψ : Operator D) → interpret Ψ (from Ψ (o Ψ))) ≐
      (λ Ψ → Labelled.readout M Ψ (o Ψ))
  nullary-operation-reads o =
    apˢ
      ( λ (g : (Ψ : Operator D) →
                 Labelled.Carrier M Ψ → Labelled.Carrier M Ψ)
          (Ψ : Operator D) → Labelled.readout M Ψ (g Ψ (o Ψ)))
      to-from

  family-operation-reads :
    (o : (Ψ : Operator D) →
      Family (Decode D (interpret Ψ)) → Labelled.Carrier M Ψ)
    → (λ (Ψ : Operator D) (F : Family (Decode D (interpret Ψ))) →
        interpret Ψ (from Ψ (o Ψ F))) ≐
      (λ Ψ F → Labelled.readout M Ψ (o Ψ F))
  family-operation-reads o =
    apˢ
      ( λ (g : (Ψ : Operator D) →
                 Labelled.Carrier M Ψ → Labelled.Carrier M Ψ)
          (Ψ : Operator D) (F : Family (Decode D (interpret Ψ))) →
          Labelled.readout M Ψ (g Ψ (o Ψ F)))
      to-from

  result-read : (Ψ : Operator D) → Family (Decode D (interpret Ψ)) → C
  result-read Ψ F =
    interpret Ψ (from Ψ (Labelled.result M Ψ (lifted Ψ F)))

  result-law :
    result-read ≐ (λ Ψ F → pr₁ (Ψ (map D (interpret Ψ) F)))
  result-law =
    family-operation-reads (λ Ψ F → Labelled.result M Ψ (lifted Ψ F))
    ∙ˢ apˢ at-lifted (Labelled.result-β M)

  branch-read :
    (Ψ : Operator D) (F : Family (Decode D (interpret Ψ)))
    → D (pr₁ (Ψ (map D (interpret Ψ) F))) → C
  branch-read Ψ F y =
    interpret Ψ (from Ψ (Labelled.branch M Ψ (lifted Ψ F) y))

  branch-law :
    branch-read ≐ (λ Ψ F y → pr₂ (Ψ (map D (interpret Ψ) F)) y)
  branch-law =
    apˢ
      ( λ (g : (Ψ : Operator D) →
                 Labelled.Carrier M Ψ → Labelled.Carrier M Ψ)
          (Ψ : Operator D) (F : Family (Decode D (interpret Ψ)))
          (y : D (pr₁ (Ψ (map D (interpret Ψ) F)))) →
          Labelled.readout M Ψ
            (g Ψ (Labelled.branch M Ψ (lifted Ψ F) y)))
      to-from
    ∙ˢ apˢ
      ( λ (h : (Ψ : Operator D)
               (F : Family (Decode D (Labelled.readout M Ψ))) →
             D (pr₁ (Ψ (map D (Labelled.readout M Ψ) F))) → C)
          (Ψ : Operator D) (F : Family (Decode D (interpret Ψ)))
          (y : D (pr₁ (Ψ (map D (interpret Ψ) F)))) →
          h Ψ (lifted Ψ F) y)
      (Labelled.branch-β M)

------------------------------------------------------------------------
-- The complete inner equation

  along :
    (r : (Ψ : Operator D) → Family (Decode D (interpret Ψ)) → C)
    → r ≐ (λ Ψ F → pr₁ (Ψ (map D (interpret Ψ) F)))
    → (Ψ : Operator D) (F : Family (Decode D (interpret Ψ)))
    → D (r Ψ F) → D (pr₁ (Ψ (map D (interpret Ψ) F)))
  along r e Ψ F =
    transportˢ D
      ( apˢ
          ( λ (h : (Ψ′ : Operator D) →
                 Family (Decode D (interpret Ψ′)) → C) → h Ψ F)
          e)

  inner-law :
    (r : (Ψ : Operator D) → Family (Decode D (interpret Ψ)) → C)
    (b : (Ψ : Operator D) (F : Family (Decode D (interpret Ψ)))
      → D (pr₁ (Ψ (map D (interpret Ψ) F))) → C)
    (e : r ≐ (λ Ψ F → pr₁ (Ψ (map D (interpret Ψ) F))))
    → b ≐ (λ Ψ F y → pr₂ (Ψ (map D (interpret Ψ) F)) y)
    → _≐_
        {A = (Ψ : Operator D) → Family (Decode D (interpret Ψ)) → Family D}
        (λ Ψ F → r Ψ F , (λ (x : D (r Ψ F)) → b Ψ F (along r e Ψ F x)))
        (λ Ψ F → Ψ (map D (interpret Ψ) F))
  inner-law r b same same = same

  inner :
    (Ψ : Operator D) → Family (Decode D (interpret Ψ))
    → Family (Decode D (interpret Ψ))
  inner Ψ F =
    from Ψ (Labelled.result M Ψ (lifted Ψ F)) ,
    (λ x →
      from Ψ
        (Labelled.branch M Ψ (lifted Ψ F)
          (along result-read result-law Ψ F x)))

------------------------------------------------------------------------
-- The strict Mahlo rule

  strict-mahlo : Strict-Mahlo Q
  strict-mahlo = record
    { carrier = code
    ; interpret = interpret
    ; empty = λ Ψ → from Ψ (Labelled.empty M Ψ)
    ; unit = λ Ψ → from Ψ (Labelled.unit M Ψ)
    ; two = λ Ψ → from Ψ (Labelled.two M Ψ)
    ; natural = λ Ψ → from Ψ (Labelled.natural M Ψ)
    ; product = λ Ψ F → from Ψ (Labelled.product M Ψ (lifted Ψ F))
    ; sum = λ Ψ F → from Ψ (Labelled.sum M Ψ (lifted Ψ F))
    ; tree = λ Ψ F → from Ψ (Labelled.tree M Ψ (lifted Ψ F))
    ; identity = λ Ψ a x y →
        from Ψ (Labelled.identity M Ψ (to Ψ a) x y)
    ; inner = inner
    ; empty-β =
        nullary-operation-reads (Labelled.empty M) ∙ˢ Labelled.empty-β M
    ; unit-β =
        nullary-operation-reads (Labelled.unit M) ∙ˢ Labelled.unit-β M
    ; two-β =
        nullary-operation-reads (Labelled.two M) ∙ˢ Labelled.two-β M
    ; natural-β =
        nullary-operation-reads (Labelled.natural M) ∙ˢ Labelled.natural-β M
    ; product-β =
        family-operation-reads (λ Ψ F → Labelled.product M Ψ (lifted Ψ F))
        ∙ˢ apˢ at-lifted (Labelled.product-β M)
    ; sum-β =
        family-operation-reads (λ Ψ F → Labelled.sum M Ψ (lifted Ψ F))
        ∙ˢ apˢ at-lifted (Labelled.sum-β M)
    ; tree-β =
        family-operation-reads (λ Ψ F → Labelled.tree M Ψ (lifted Ψ F))
        ∙ˢ apˢ at-lifted (Labelled.tree-β M)
    ; identity-β =
        apˢ
          ( λ (g : (Ψ : Operator D) →
                     Labelled.Carrier M Ψ → Labelled.Carrier M Ψ)
              (Ψ : Operator D) (a : D (code Ψ))
              (x y : Decode D (interpret Ψ) a) →
              Labelled.readout M Ψ
                (g Ψ (Labelled.identity M Ψ (to Ψ a) x y)))
          to-from
        ∙ˢ apˢ
          ( λ (h : (Ψ : Operator D) (a : Labelled.Carrier M Ψ)
                 (x y : Decode D (Labelled.readout M Ψ) a) → C)
              (Ψ : Operator D) (a : D (code Ψ))
              (x y : Decode D (interpret Ψ) a) →
              h Ψ (to Ψ a) x y)
          (Labelled.identity-β M)
    ; inner-β = inner-law result-read branch-read result-law branch-law
    }

------------------------------------------------------------------------
-- The ambient family

module _ {ℓ : Level} (M : Labelled (Ambient.formers ℓ)) where

  ambient : Classification M
  ambient = record
    { code = Labelled.Carrier M
    ; to = λ Ψ y → y
    ; from = λ Ψ y → y
    ; to-from = same
    }

  ambient-mahlo : Strict-Mahlo (Ambient.formers ℓ)
  ambient-mahlo = strict-mahlo M ambient
