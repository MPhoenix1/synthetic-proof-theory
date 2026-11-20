{-# OPTIONS --safe --without-K #-}

module SPT.IR.Indexed.General.Reducibility.Kripke.Neutral.Discriminator where

-- Readback of Kubánek's Kripke predicate with neutral codes on one stage
-- with two edges (`stages`), over a syntax whose codes and elements are
-- numbers (`numbers`, `syntaxes`): the element 0 is canonical, 1 is the
-- variable, and every other number is neither. An element is neutral when
-- it is 1 and normal when it is 0 or 1 (`forms`). The base decoding holds
-- of the normal elements, and the plus decoding of what the decoding of
-- its recursive input holds of (`predicates`). Every code may be neutral;
-- a code reads back to a number: El0' to 0, a neutral code to 5, El+' to
-- one more than the sum of its parts (`readback′`). The extension of a
-- stage is the stage itself, with the variable 1 (`extension`).
--
-- - One code, reducible as El0' and as a neutral code, decodes
--   differently at the two: 0 is reducible at El0', not at the neutral
--   code (`canonical-reducible`, `canonical-not-neutral`).
-- - Reflection at El+' goes through the readback of its recursive input:
--   the variable is reducible at the plus code by the base decoding's
--   neutral case (`plus-reflected`).
-- - The plus code's family is reducible as El0' at a canonical element and
--   as a neutral code at the variable (`pick`, `plus`). The plus code reads
--   back to 6, not to 1: its family is read back at the variable,
--   reducible there by reflection (`plus-readback`; a false readback
--   fails).
-- - A valuation that is not `reify-code` by definition, the successor of
--   (nA + nB) + 0 at El+', has its equation there by `+-zero-right`, an
--   induction (`padded`, `padded-reifies`). Neutral/Initiality's uniqueness
--   makes it the readback, so the plus code reads back to 6 through it
--   (`padded-is-reify-code`, `padded-plus`; a false equation fails).

open import SPT.Base

open import SPT.Foundation.Kripke using
  (Stages; Stage; Arrow; identity; restrict; shift)
open import SPT.IR.Indexed.General.Reducibility using (Syntax)
open import SPT.IR.Indexed.General.Reducibility.Kripke using
  (Ma♯; U0♯; El♯; El0'♯; Fam♯; applied; U+♯; El+'♯; Predicates)
open import SPT.IR.Indexed.General.Reducibility.Kripke.Neutral using
  (Forms; Extension; Readback; Normal-Code; Map; Elp; El0'p; El+'p; nep;
   restricted; MapElim; reflect; family-readback; Reified; reify-code)
open import
  SPT.IR.Indexed.General.Reducibility.Kripke.Neutral.Initiality
  using (Reification; reify-code-unique)

stages : Stages lzero
stages = record { Stage = 𝟙 ; Edge = λ e c → 𝟚 }

numbers : Syntax lzero
numbers = record
  { Ma = ℕ
  ; El = λ m → ℕ
  ; U0 = 𝟙
  ; El0' = λ u → 0
  ; Fam = λ A → 𝟙
  ; _$$_ = λ B a → 0
  ; U+ = λ A B → 𝟙
  ; El+' = λ A B C → suc A
  }

syntaxes : Stage stages → Syntax lzero
syntaxes e = numbers

-- The canonical element and the variable.
normal : ℕ → Set
normal n = (n ＝ 0) ⊎ (n ＝ 1)

forms : Forms stages syntaxes
forms = record
  { Neutral-Code₀ = λ d m → 𝟙
  ; Neutral₀ = λ d A a → a ⋆ ₀ ＝ 1
  ; Normal-Code₀ = λ d m → ℕ
  ; Normal₀ = λ d A a → normal (a ⋆ ₀)
  ; Normal-Family₀ = λ d A B → ℕ
  }

predicates : Predicates stages syntaxes
predicates = record
  { U0p₀ = λ d u → 𝟙
  ; El0p₀ = λ d u up t → normal (t ⋆ ₀)
  ; U+p₀ = λ d A Ap B Bp C → 𝟙
  ; El+p₀ = λ d A Ap B Bp C Cp t → Ap d (identity stages) t
  }

readback′ : Readback stages syntaxes forms predicates
readback′ = record
  { base-reflect = λ d u up a n → inr (n d (identity stages))
  ; base-reify = λ d u up a ap → ap
  ; plus-reflect = λ d A Ap B Bp C Cp a P Q n →
      pr₁ (P d (identity stages) a) n
  ; plus-reify = λ d A Ap B Bp C Cp a P Q ap →
      pr₂ (P d (identity stages) a) ap
  ; neutral-normal = λ d A a n → inr (n d (identity stages))
  ; neutral-code-normal = λ d m mn → 5
  ; base-normal = λ d u up → 0
  ; plus-normal = λ d A Ap B Bp C nA nB Cp → suc (nA + nB)
  }

extension : Extension stages syntaxes forms
extension = record
  { extend = λ d A → d
  ; weaken = λ d A → identity stages
  ; fresh = λ d A e g → 1
  ; fresh-neutral = λ d A d′ φ → refl
  ; family-normal = λ d A B n → n
  }

------------------------------------------------------------------------
-- One code, two decodings

point : (d : Stage stages) → U0♯ stages syntaxes d
point d = λ e g → ⋆

base :
  Map stages syntaxes forms predicates ⋆ (El0'♯ stages syntaxes ⋆ (point ⋆))
base = El0'p stages syntaxes forms predicates ⋆ (point ⋆) (λ d φ → ⋆)

zero-element : El♯ stages syntaxes ⋆ (El0'♯ stages syntaxes ⋆ (point ⋆))
zero-element = λ e g → 0

canonical-reducible :
  Elp stages syntaxes forms predicates ⋆ (El0'♯ stages syntaxes ⋆ (point ⋆))
    base zero-element
canonical-reducible = λ d φ → inl refl

canonical-not-neutral :
  Elp stages syntaxes forms predicates ⋆ (El0'♯ stages syntaxes ⋆ (point ⋆))
    (nep stages syntaxes forms predicates ⋆
      (El0'♯ stages syntaxes ⋆ (point ⋆)) (λ d φ → ⋆))
    zero-element
  → 𝟘
canonical-not-neutral w with w ⋆ (identity stages)
... | ()

------------------------------------------------------------------------
-- The plus code

family : Fam♯ stages syntaxes ⋆ (El0'♯ stages syntaxes ⋆ (point ⋆))
family = λ e g → ⋆

operation :
  U+♯ stages syntaxes ⋆ (El0'♯ stages syntaxes ⋆ (point ⋆)) family
operation = λ e g → ⋆

-- The family's value is reducible as El0' at a canonical element and as a
-- neutral code at the variable.
pick :
  {X Y : Set} (d : Stage stages) → X ⊎ Y
  → Map stages syntaxes forms predicates d
      (El0'♯ stages syntaxes d (point d))
pick d (inl x) =
  El0'p stages syntaxes forms predicates d (point d) (λ d′ φ → ⋆)
pick d (inr y) =
  nep stages syntaxes forms predicates d (El0'♯ stages syntaxes d (point d))
    (λ d′ φ → ⋆)

plus :
  Map stages syntaxes forms predicates ⋆
    (El+'♯ stages syntaxes ⋆ (El0'♯ stages syntaxes ⋆ (point ⋆)) family
      operation)
plus =
  El+'p stages syntaxes forms predicates ⋆
    (El0'♯ stages syntaxes ⋆ (point ⋆))
    (restricted stages syntaxes forms predicates ⋆
      (El0'♯ stages syntaxes ⋆ (point ⋆)) base)
    family (λ d φ a ap → pick d (ap d (identity stages))) operation
    (λ d φ → ⋆)

-- The variable is reducible at the plus code through the base decoding's
-- neutral case.
plus-reflected :
  reflect stages syntaxes forms predicates readback′ extension ⋆
    (El+'♯ stages syntaxes ⋆ (El0'♯ stages syntaxes ⋆ (point ⋆)) family
      operation)
    plus (λ e g → 1) (λ d φ → refl) ⋆ (identity stages) ⋆
    (identity stages)
  ＝ inr refl
plus-reflected = refl

-- The plus code reads back through its family at the variable.
plus-readback :
  reify-code stages syntaxes forms predicates readback′ extension ⋆
    (El+'♯ stages syntaxes ⋆ (El0'♯ stages syntaxes ⋆ (point ⋆)) family
      operation)
    plus ⋆ (identity stages)
  ＝ 6
plus-readback = refl

------------------------------------------------------------------------
-- Uniqueness of the readback of codes

padded :
  (c : Stage stages) (m : Ma♯ stages syntaxes c)
  → Map stages syntaxes forms predicates c m
  → Normal-Code stages syntaxes forms c m
padded =
  MapElim stages syntaxes forms predicates
    (Reified stages syntaxes forms predicates readback′ extension)
    (λ c u up d φ → 0)
    (λ c A Ap k B Bp k′ C Cp d φ →
      suc
        ( ( k d φ d (identity stages)
          + family-readback stages syntaxes forms predicates readback′
              extension d (A ·⟨ stages ⟩ φ) (shift stages Ap φ)
              (B ·⟨ stages ⟩ φ) (shift stages Bp φ) (shift stages k′ φ))
        + zero))
    (λ c m mn d φ → 5)

padded-reifies :
  Reification stages syntaxes forms predicates readback′ extension padded
padded-reifies = record
  { reifies-El0'p = λ c u up d φ → refl
  ; reifies-El+'p = λ c A Ap B Bp C Cp d φ →
      ap suc
        ( +-zero-right
          ( padded d (A ·⟨ stages ⟩ φ) (Ap d φ) d (identity stages)
          + family-readback stages syntaxes forms predicates readback′
              extension d (A ·⟨ stages ⟩ φ) (shift stages Ap φ)
              (B ·⟨ stages ⟩ φ) (shift stages Bp φ)
              (shift stages
                (λ d₁ φ₁ a ap →
                  padded d₁
                    (applied stages syntaxes d₁ (A ·⟨ stages ⟩ φ₁)
                      (B ·⟨ stages ⟩ φ₁) a)
                    (Bp d₁ φ₁ a ap))
                φ)))
  ; reifies-nep = λ c m mn d φ → refl
  }

padded-is-reify-code :
  (c : Stage stages) (m : Ma♯ stages syntaxes c)
  (mp : Map stages syntaxes forms predicates c m)
  (d : Stage stages) (φ : Arrow stages d c)
  → padded c m mp d φ
    ＝ reify-code stages syntaxes forms predicates readback′ extension c m mp
        d φ
padded-is-reify-code =
  reify-code-unique stages syntaxes forms predicates readback′ extension
    padded padded-reifies

padded-plus :
  padded ⋆
    (El+'♯ stages syntaxes ⋆ (El0'♯ stages syntaxes ⋆ (point ⋆)) family
      operation)
    plus ⋆ (identity stages)
  ＝ 6
padded-plus =
  padded-is-reify-code ⋆
    (El+'♯ stages syntaxes ⋆ (El0'♯ stages syntaxes ⋆ (point ⋆)) family
      operation)
    plus ⋆ (identity stages)
  ∙ plus-readback
