{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.Universe where

-- A small Tarski universe generated from a displayed seed U and an operator Ψ
-- on small families. Codes and decoding are induction–recursive (`Code`,
-- `decode`). The universe contains U's base and fibers, all ordinary formers,
-- and Ψ's complete results and branches, with judgmental decoding equations.
-- Coded seed diagrams (`Seeds`) also name whole indexed boundary families of
-- Universe.Boundary and their exact fills (`boundary`, `filling`), which can
-- determine further formation at level ℓ. The codes form a closure of the
-- ambient formers and Ψ (`closure`), with the child's formers and laws
-- (`formers`, `laws`), hence a Mahlo reflection of the ambient family
-- (`reflection`), and they have dependent induction (`Methods`, `ind`).

open import SPT.Base
open import SPT.Foundation.Spaces.Maps using (Split-Map)
open import SPT.Foundation.Spaces using (DΣ; Base; Fiber; Total)
open import SPT.Mahlo.Universe.Boundary using
  (RetainedBoundary; RetainedFill; retained-seed; filler-indexed-fan)
import SPT.Mahlo.Ambient as Ambient
open import SPT.Foundation.Tree.W using (W)
open import SPT.Mahlo.Decoding using
  (DecodingLaws; MahloReflection; child-formers; child-decoding)
import SPT.Mahlo.Specification as Specification

------------------------------------------------------------------------
-- Seed diagrams

-- A coded index type, its seed family, and the dependent seed fillers.
-- Keeping this diagram together fixes the whole indexed formation.
record Seeds {ℓ : Level} (C : Set ℓ) (D : C → Set ℓ) : Set ℓ where
  constructor seeds
  field
    index : C
    seed : D index → C
    fiber : (i : D index) → D (seed i) → C

module _ {ℓ : Level} {C : Set ℓ} {D : C → Set ℓ} where

  -- The boundary family of a diagram, at each point of its index.
  Boundary : (S : Seeds C D) → D (Seeds.index S) → Set ℓ
  Boundary S =
    RetainedBoundary (D (Seeds.index S)) (λ i → D (Seeds.seed S i))
      ( λ {i} x → D (Seeds.fiber S i x))

  -- A motive at every code of a diagram.
  record All {ν : Level} (S : Seeds C D) (P : C → Set ν) :
    Set (ℓ ⊔ ν) where
    field
      on-index : P (Seeds.index S)
      on-seed : (i : D (Seeds.index S)) → P (Seeds.seed S i)
      on-fiber : (i : D (Seeds.index S)) (x : D (Seeds.seed S i)) →
        P (Seeds.fiber S i x)

------------------------------------------------------------------------
-- The codes and their decoding

-- U and Ψ are fixed before formation. Every dependent code family is
-- indexed by the literal decoding of its domain code. A branch retains
-- the selected point of Ψ's result, which determines its decoded type.
mutual
  data Code {ℓ : Level} (U : DΣ ℓ ℓ) (Ψ : Ambient.Operator ℓ) : Set ℓ

  decode : {ℓ : Level} {U : DΣ ℓ ℓ} {Ψ : Ambient.Operator ℓ} →
    Code U Ψ → Set ℓ

  data Code {ℓ} U Ψ where
    codes : Code U Ψ
    old : Base U → Code U Ψ
    empty unit two natural : Code U Ψ
    product sum tree result : (a : Code U Ψ) →
      (decode a → Code U Ψ) → Code U Ψ
    identity : (a : Code U Ψ) → decode a → decode a → Code U Ψ
    branch : (a : Code U Ψ) (b : decode a → Code U Ψ) →
      pr₁ (Ψ (decode a , (λ x → decode (b x)))) → Code U Ψ
    boundary : (S : Seeds (Code U Ψ) decode) →
      decode (Seeds.index S) → Code U Ψ
    filling : (S : Seeds (Code U Ψ) decode)
      (i : decode (Seeds.index S)) → decode (boundary S i) → Code U Ψ

  decode {U = U} codes = Base U
  decode {U = U} (old c) = Fiber U c
  decode {ℓ} empty = Lift ℓ 𝟘
  decode {ℓ} unit = Lift ℓ 𝟙
  decode {ℓ} two = Lift ℓ 𝟚
  decode {ℓ} natural = Lift ℓ ℕ
  decode (product a b) = (x : decode a) → decode (b x)
  decode (sum a b) = Σ (decode a) (λ x → decode (b x))
  decode (tree a b) = W (decode a) (λ x → decode (b x))
  decode (identity a x y) = x ＝ y
  decode {Ψ = Ψ} (result a b) =
    pr₁ (Ψ (decode a , (λ x → decode (b x))))
  decode {Ψ = Ψ} (branch a b y) =
    pr₂ (Ψ (decode a , (λ x → decode (b x)))) y
  decode (boundary (seeds a b c) i) =
    RetainedBoundary (decode a) (λ j → decode (b j))
      ( λ {j} x → decode (c j x)) i
  decode (filling S i r) = RetainedFill r

universe : {ℓ : Level} → DΣ ℓ ℓ → Ambient.Operator ℓ → DΣ ℓ ℓ
universe U Ψ = record { Base = Code U Ψ ; Fiber = decode }

------------------------------------------------------------------------
-- Decoding equations

codes-β : {ℓ : Level} (U : DΣ ℓ ℓ) (Ψ : Ambient.Operator ℓ) →
  decode (codes {U = U} {Ψ = Ψ}) ＝ Base U
codes-β U Ψ = refl

old-β : {ℓ : Level} (U : DΣ ℓ ℓ) (Ψ : Ambient.Operator ℓ)
  (c : Base U) → decode (old {U = U} {Ψ = Ψ} c) ＝ Fiber U c
old-β U Ψ c = refl

boundary-β : {ℓ : Level} {U : DΣ ℓ ℓ} {Ψ : Ambient.Operator ℓ}
  (S : Seeds (Code U Ψ) decode) (i : decode (Seeds.index S)) →
  decode (boundary S i) ＝ Boundary S i
boundary-β S i = refl

filling-β : {ℓ : Level} {U : DΣ ℓ ℓ} {Ψ : Ambient.Operator ℓ}
  (S : Seeds (Code U Ψ) decode) (i : decode (Seeds.index S))
  (r : decode (boundary S i)) →
  decode (filling S i r) ＝ RetainedFill r
filling-β S i r = refl

filling-seed-β : {ℓ : Level} {U : DΣ ℓ ℓ} {Ψ : Ambient.Operator ℓ}
  (S : Seeds (Code U Ψ) decode) (i : decode (Seeds.index S))
  (x : decode (Seeds.seed S i)) →
  decode (filling S i (retained-seed x)) ＝
    decode (Seeds.fiber S i x)
filling-seed-β S i x = refl

filling-fan-β : {ℓ : Level} {U : DΣ ℓ ℓ} {Ψ : Ambient.Operator ℓ}
  (S : Seeds (Code U Ψ) decode) (i : decode (Seeds.index S))
  (r : decode (boundary S i))
  (k : decode (filling S i r) → decode (boundary S i)) →
  decode (filling S i (filler-indexed-fan r k)) ＝
    ((x : decode (filling S i r)) → decode (filling S i (k x)))
filling-fan-β S i r k = refl

------------------------------------------------------------------------
-- The seed, complete families and the operator's action

inclusion : {ℓ : Level} (U : DΣ ℓ ℓ) (Ψ : Ambient.Operator ℓ) →
  Split-Map U (universe U Ψ)
inclusion U Ψ = record
  { on-base = old
  ; on-fiber = λ c x → x
  }

Family : {ℓ : Level} → DΣ ℓ ℓ → Ambient.Operator ℓ → Set ℓ
Family U Ψ = Specification.Family (decode {U = U} {Ψ = Ψ})

map : {ℓ : Level} {U : DΣ ℓ ℓ} {Ψ : Ambient.Operator ℓ} →
  Family U Ψ → Specification.Family (λ (A : Set ℓ) → A)
map (a , b) = decode a , (λ x → decode (b x))

formed : {ℓ : Level} {U : DΣ ℓ ℓ} {Ψ : Ambient.Operator ℓ}
  (S : Seeds (Code U Ψ) decode) (i : decode (Seeds.index S)) →
  Family U Ψ
formed S i = boundary S i , filling S i

formed-β : {ℓ : Level} {U : DΣ ℓ ℓ} {Ψ : Ambient.Operator ℓ}
  (S : Seeds (Code U Ψ) decode) (i : decode (Seeds.index S)) →
  map (formed S i) ＝ (Boundary S i , (λ r → RetainedFill r))
formed-β S i = refl

formed-total-β : {ℓ : Level} {U : DΣ ℓ ℓ} {Ψ : Ambient.Operator ℓ}
  (S : Seeds (Code U Ψ) decode) (i : decode (Seeds.index S)) →
  decode (sum (boundary S i) (filling S i)) ＝
    Σ (Boundary S i) (λ r → RetainedFill r)
formed-total-β S i = refl

ambient : {ℓ : Level} (U : DΣ ℓ ℓ) (Ψ : Ambient.Operator ℓ) →
  Family U Ψ
ambient U Ψ = codes , old

ambient-β : {ℓ : Level} (U : DΣ ℓ ℓ) (Ψ : Ambient.Operator ℓ) →
  map (ambient U Ψ) ＝ (Base U , Fiber U)
ambient-β U Ψ = refl

total-β : {ℓ : Level} (U : DΣ ℓ ℓ) (Ψ : Ambient.Operator ℓ) →
  decode (sum {U = U} {Ψ = Ψ} codes old) ＝ Total U
total-β U Ψ = refl

action : {ℓ : Level} {U : DΣ ℓ ℓ} {Ψ : Ambient.Operator ℓ} →
  Family U Ψ → Family U Ψ
action (a , b) = result a b , branch a b

action-β : {ℓ : Level} {U : DΣ ℓ ℓ} {Ψ : Ambient.Operator ℓ}
  (F : Family U Ψ) → map (action F) ＝ Ψ (map F)
action-β (a , b) = refl

------------------------------------------------------------------------
-- The closure, its formers and laws, and the reflection

closure : {ℓ : Level} (U : DΣ ℓ ℓ) (Ψ : Ambient.Operator ℓ) →
  Specification.Closure (Ambient.formers ℓ) Ψ (Code U Ψ)
closure U Ψ = record
  { interpret = decode
  ; empty = empty , refl
  ; unit = unit , refl
  ; two = two , refl
  ; natural = natural , refl
  ; product = λ F → product (pr₁ F) (pr₂ F) , refl
  ; sum = λ F → sum (pr₁ F) (pr₂ F) , refl
  ; tree = λ F → tree (pr₁ F) (pr₂ F) , refl
  ; identity = λ a x y → identity a x y , refl
  ; inner = action
  ; inner-β = action-β
  }

formers : {ℓ : Level} (U : DΣ ℓ ℓ) (Ψ : Ambient.Operator ℓ) →
  Specification.Formers (Code U Ψ) decode
formers U Ψ = child-formers (closure U Ψ)

laws : {ℓ : Level} (U : DΣ ℓ ℓ) (Ψ : Ambient.Operator ℓ) →
  DecodingLaws (formers U Ψ)
laws {ℓ} U Ψ = child-decoding (Ambient.laws ℓ) (closure U Ψ)

-- The generated carrier is a code of the ambient Set ℓ parent. Its
-- reflector returns this exact small universe, with U retained throughout.
-- Reflection for arbitrary operators inside Code U Ψ is not asserted.
reflection : {ℓ : Level} (U : DΣ ℓ ℓ) →
  MahloReflection (Ambient.formers ℓ)
reflection {ℓ} U = record
  { codeReflection = record
      { reflect = λ Ψ → record
          { carrier = Code U Ψ
          ; closure = closure U Ψ
          }
      }
  ; decoding = Ambient.laws ℓ
  }

------------------------------------------------------------------------
-- Dependent induction

-- Dependent induction retains each literal branch family and every
-- selected result point. No equality of decoded types identifies codes.
record Methods {ℓ ν : Level} (U : DΣ ℓ ℓ) (Ψ : Ambient.Operator ℓ)
  (P : Code U Ψ → Set ν) : Set (ℓ ⊔ ν) where
  field
    on-codes : P codes
    on-old : (c : Base U) → P (old c)
    on-empty : P empty
    on-unit : P unit
    on-two : P two
    on-natural : P natural
    on-product : (a : Code U Ψ) (b : decode a → Code U Ψ) →
      P a → ((x : decode a) → P (b x)) → P (product a b)
    on-sum : (a : Code U Ψ) (b : decode a → Code U Ψ) →
      P a → ((x : decode a) → P (b x)) → P (sum a b)
    on-tree : (a : Code U Ψ) (b : decode a → Code U Ψ) →
      P a → ((x : decode a) → P (b x)) → P (tree a b)
    on-identity : (a : Code U Ψ) (x y : decode a) →
      P a → P (identity a x y)
    on-result : (a : Code U Ψ) (b : decode a → Code U Ψ) →
      P a → ((x : decode a) → P (b x)) → P (result a b)
    on-branch : (a : Code U Ψ) (b : decode a → Code U Ψ)
      (y : pr₁ (Ψ (decode a , (λ x → decode (b x))))) →
      P a → ((x : decode a) → P (b x)) → P (branch a b y)
    on-boundary : (S : Seeds (Code U Ψ) decode)
      (i : decode (Seeds.index S)) → All S P → P (boundary S i)
    on-filling : (S : Seeds (Code U Ψ) decode)
      (i : decode (Seeds.index S)) (r : decode (boundary S i)) →
      All S P → P (filling S i r)

mutual
  ind : {ℓ ν : Level} {U : DΣ ℓ ℓ} {Ψ : Ambient.Operator ℓ}
    {P : Code U Ψ → Set ν} → Methods U Ψ P → (a : Code U Ψ) → P a
  ind m codes = Methods.on-codes m
  ind m (old c) = Methods.on-old m c
  ind m empty = Methods.on-empty m
  ind m unit = Methods.on-unit m
  ind m two = Methods.on-two m
  ind m natural = Methods.on-natural m
  ind m (product a b) =
    Methods.on-product m a b (ind m a) (λ x → ind m (b x))
  ind m (sum a b) = Methods.on-sum m a b (ind m a) (λ x → ind m (b x))
  ind m (tree a b) = Methods.on-tree m a b (ind m a) (λ x → ind m (b x))
  ind m (identity a x y) = Methods.on-identity m a x y (ind m a)
  ind m (result a b) =
    Methods.on-result m a b (ind m a) (λ x → ind m (b x))
  ind m (branch a b y) =
    Methods.on-branch m a b y (ind m a) (λ x → ind m (b x))
  ind m (boundary S i) = Methods.on-boundary m S i (ind-seeds m S)
  ind m (filling S i r) = Methods.on-filling m S i r (ind-seeds m S)

  ind-seeds : {ℓ ν : Level} {U : DΣ ℓ ℓ} {Ψ : Ambient.Operator ℓ}
    {P : Code U Ψ → Set ν} → Methods U Ψ P →
    (S : Seeds (Code U Ψ) decode) → All S P
  ind-seeds m (seeds a b c) = record
    { on-index = ind m a
    ; on-seed = λ i → ind m (b i)
    ; on-fiber = λ i x → ind m (c i x)
    }
