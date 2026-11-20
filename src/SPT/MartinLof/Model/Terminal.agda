{-# OPTIONS --safe --without-K #-}

module SPT.MartinLof.Model.Terminal where

-- The terminal model of the core theory (`terminal`): one context, one
-- substitution, one term, and every operation constant. Every law holds by
-- refl, since ⊤ has η.
--
-- It shows that the fields of Model are jointly satisfiable, for any
-- constants. It is no witness of consistency: in it, the empty type has a
-- closed term.

open import SPT.Base hiding (Lift; nothing)
open import SPT.MartinLof.Model using (Model)
open import SPT.MartinLof.Model.Empty using (Empty)
open import SPT.MartinLof.Model.Identity using (Identity)
open import SPT.MartinLof.Model.Lift using (Lift)
open import SPT.MartinLof.Model.Natural using (Natural)
open import SPT.MartinLof.Model.Subuniverse using
  (Operations; Subuniverse)
open import SPT.MartinLof.Model.Pi using (Pi)
open import SPT.MartinLof.Model.Russell using (Russell)
open import SPT.MartinLof.Model.Sigma using (Sigma)
open import SPT.MartinLof.Model.Sum using (Sum)
open import SPT.MartinLof.Model.Unit using (Unit)
open import SPT.MartinLof.Model.WellFounded using (WellFounded)

point : Russell lzero
point = record
  { Ob = 𝟙
  ; Hom = λ _ _ → 𝟙
  ; id = ⋆
  ; _∘_ = λ _ _ → ⋆
  ; id-left = λ _ → refl
  ; id-right = λ _ → refl
  ; associative = λ _ _ _ → refl
  ; ◇ = ⋆
  ; ε = λ _ → ⋆
  ; ε-unique = λ _ → refl
  ; Tm = λ _ → 𝟙
  ; _[_] = λ _ _ → ⋆
  ; [id] = λ _ → refl
  ; [∘] = λ _ _ _ → refl
  ; type-of = λ _ → ⋆
  ; type-of-[] = λ _ _ → refl
  ; universe = λ _ → ⋆
  ; universe-type = λ _ → refl
  ; _▸_ = λ _ _ → ⋆
  ; p = ⋆
  ; q = λ _ → ⋆
  ; q-type = λ _ _ _ → refl
  ; extend = λ _ _ _ _ → ⋆
  ; p-extend = λ _ _ _ _ → refl
  ; q-extend = λ _ _ _ _ _ _ → refl
  ; extend-unique = λ _ _ _ _ _ → refl
  ; _[_⨾_] = λ _ _ _ → ⋆
  ; [⨾] = λ _ _ _ _ _ → refl
  }

lifting : Lift point
lifting = record
  { lifted = λ _ _ _ → ⋆
  ; lift = λ _ _ _ _ → ⋆
  ; lower = λ _ _ _ _ → ⋆
  ; lifted-type = λ _ _ _ _ → refl
  ; lift-type = λ _ _ _ _ _ _ → refl
  ; lower-type = λ _ _ _ _ _ _ → refl
  ; lower-lift = λ _ _ _ _ _ _ → refl
  ; lift-lower = λ _ _ _ _ _ _ → refl
  ; lifted-[] = λ _ _ _ _ _ → refl
  ; lift-[] = λ _ _ _ _ _ _ _ → refl
  ; lower-[] = λ _ _ _ _ _ _ _ → refl
  }

products : Pi point
products = record
  { pi = λ _ _ _ _ → ⋆
  ; lambda = λ _ _ _ _ _ → ⋆
  ; application = λ _ _ _ _ _ _ → ⋆
  ; pi-type = λ _ _ _ _ _ _ → refl
  ; lambda-type = λ _ _ _ _ _ _ _ _ → refl
  ; application-type = λ _ _ _ _ _ _ _ _ _ _ → refl
  ; application-lambda = λ _ _ _ _ _ _ _ _ _ _ → refl
  ; lambda-application = λ _ _ _ _ _ _ _ _ → refl
  ; pi-[] = λ _ _ _ _ _ _ _ → refl
  ; lambda-[] = λ _ _ _ _ _ _ _ _ _ → refl
  ; application-[] = λ _ _ _ _ _ _ _ _ _ _ _ → refl
  }

pairs : Sigma point
pairs = record
  { sigma = λ _ _ _ _ → ⋆
  ; pair = λ _ _ _ _ _ _ → ⋆
  ; first = λ _ _ _ _ _ → ⋆
  ; second = λ _ _ _ _ _ → ⋆
  ; sigma-type = λ _ _ _ _ _ _ → refl
  ; pair-type = λ _ _ _ _ _ _ _ _ _ _ → refl
  ; first-type = λ _ _ _ _ _ _ _ _ → refl
  ; second-type = λ _ _ _ _ _ _ _ _ → refl
  ; first-pair = λ _ _ _ _ _ _ _ _ _ _ → refl
  ; second-pair = λ _ _ _ _ _ _ _ _ _ _ → refl
  ; pair-projections = λ _ _ _ _ _ _ _ _ → refl
  ; sigma-[] = λ _ _ _ _ _ _ _ → refl
  ; pair-[] = λ _ _ _ _ _ _ _ _ _ _ _ → refl
  ; first-[] = λ _ _ _ _ _ _ _ _ _ → refl
  ; second-[] = λ _ _ _ _ _ _ _ _ _ → refl
  }

paths : Identity point
paths = record
  { identity = λ _ _ _ _ → ⋆
  ; reflexivity = λ _ _ _ → ⋆
  ; path-induction = λ _ _ _ _ _ _ _ _ → ⋆
  ; identity-type = λ _ _ _ _ _ _ _ → refl
  ; reflexivity-type = λ _ _ _ _ _ → refl
  ; path-induction-type = λ _ _ _ _ _ _ _ _ _ _ _ _ _ _ → refl
  ; path-induction-reflexivity = λ _ _ _ _ _ _ _ _ _ _ → refl
  ; identity-[] = λ _ _ _ _ _ _ _ _ → refl
  ; reflexivity-[] = λ _ _ _ _ _ _ → refl
  ; path-induction-[] = λ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ → refl
  }

trees : WellFounded point products
trees = record
  { tree = λ _ _ _ _ → ⋆
  ; supremum = λ _ _ _ _ _ _ → ⋆
  ; tree-induction = λ _ _ _ _ _ _ _ → ⋆
  ; tree-type = λ _ _ _ _ _ _ → refl
  ; supremum-type = λ _ _ _ _ _ _ _ _ _ _ → refl
  ; tree-induction-type = λ _ _ _ _ _ _ _ _ _ _ _ → refl
  ; tree-induction-supremum =
      λ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ → refl
  ; tree-[] = λ _ _ _ _ _ _ _ → refl
  ; supremum-[] = λ _ _ _ _ _ _ _ _ _ _ _ → refl
  ; tree-induction-[] = λ _ _ _ _ _ _ _ _ _ _ _ _ _ → refl
  }

nothing : Empty point
nothing = record
  { empty = ⋆
  ; absurd = λ _ _ _ → ⋆
  ; empty-type = refl
  ; absurd-type = λ _ _ _ _ _ → refl
  ; absurd-[] = λ _ _ _ _ _ _ → refl
  }

one : Unit point
one = record
  { unit = ⋆
  ; star = ⋆
  ; unit-type = refl
  ; star-type = refl
  ; star-unique = λ _ _ → refl
  }

sums : Sum point
sums = record
  { sum = λ _ _ _ _ → ⋆
  ; left = λ _ _ _ _ _ → ⋆
  ; right = λ _ _ _ _ _ → ⋆
  ; case = λ _ _ _ _ _ _ _ _ _ → ⋆
  ; sum-type = λ _ _ _ _ _ _ → refl
  ; left-type = λ _ _ _ _ _ _ _ _ → refl
  ; right-type = λ _ _ _ _ _ _ _ _ → refl
  ; case-type = λ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ → refl
  ; case-left = λ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ → refl
  ; case-right = λ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ → refl
  ; sum-[] = λ _ _ _ _ _ _ _ → refl
  ; left-[] = λ _ _ _ _ _ _ _ _ _ → refl
  ; right-[] = λ _ _ _ _ _ _ _ _ _ → refl
  ; case-[] = λ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ → refl
  }

numbers : Natural point
numbers = record
  { natural = ⋆
  ; zero = ⋆
  ; successor = λ _ → ⋆
  ; natural-induction = λ _ _ _ _ _ → ⋆
  ; natural-type = refl
  ; zero-type = refl
  ; successor-type = λ _ _ → refl
  ; natural-induction-type = λ _ _ _ _ _ _ _ _ _ → refl
  ; natural-induction-zero = λ _ _ _ _ _ _ _ → refl
  ; natural-induction-successor = λ _ _ _ _ _ _ _ _ _ → refl
  ; successor-[] = λ _ _ _ → refl
  ; natural-induction-[] = λ _ _ _ _ _ _ _ _ _ _ _ → refl
  }

operations : Operations point
operations = record
  { subuniverse = λ _ _ _ _ _ → ⋆
  ; inclusion = λ _ _ _ _ _ _ → ⋆
  ; closure = λ _ _ _ _ _ _ _ _ → ⋆
  ; decoding = λ _ _ _ _ _ _ → ⋆
  ; induction = λ _ _ _ _ _ _ _ _ _ _ → ⋆
  }

subuniverses : Subuniverse point products operations
subuniverses = record
  { subuniverse-code = λ _ _ _ _ _ _ → refl
  ; inclusion-type = λ _ _ _ _ _ _ _ _ → refl
  ; closure-type = λ _ _ _ _ _ _ _ _ _ _ → refl
  ; decoding-code = λ _ _ _ _ _ _ _ _ → refl
  ; induction-type = λ _ _ _ _ _ _ _ _ _ _ _ _ _ → refl
  ; inclusion-decoding = λ _ _ _ _ _ _ _ _ → refl
  ; closure-decoding = λ _ _ _ _ _ _ _ _ _ _ → refl
  ; inclusion-computation = λ _ _ _ _ _ _ _ _ _ _ _ _ _ → refl
  ; closure-computation = λ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ → refl
  ; subuniverse-[] = λ _ _ _ _ _ _ _ → refl
  ; inclusion-[] = λ _ _ _ _ _ _ _ _ _ → refl
  ; closure-[] = λ _ _ _ _ _ _ _ _ _ _ _ → refl
  ; decoding-[] = λ _ _ _ _ _ _ _ _ _ → refl
  ; induction-[] = λ _ _ _ _ _ _ _ _ _ _ _ _ _ _ → refl
  }

terminal : (C : Set) → Model lzero C
terminal C = record
  { base = point
  ; lift-structure = lifting
  ; pi-structure = products
  ; sigma-structure = pairs
  ; identity-structure = paths
  ; tree-structure = trees
  ; empty-structure = nothing
  ; unit-structure = one
  ; sum-structure = sums
  ; natural-structure = numbers
  ; subuniverse-operations = operations
  ; subuniverse-structure = subuniverses
  ; constant = λ _ → ⋆
  }
