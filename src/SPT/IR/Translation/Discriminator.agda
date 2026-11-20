{-# OPTIONS --safe --without-K #-}

module SPT.IR.Translation.Discriminator where

-- Translations of closed descriptions over numbers. They are not
-- cartesian: one erases a position and one uses a position twice (`erase`,
-- `erases`, `duplicate`, `duplicates`). They can be lax: the output law of
-- `absorb` is `n ＝ n + 0`, by induction. The target may vary along a map
-- (`shifted`, along the successor). The laws refute: no translation from a
-- code with no positions to one with a position, none onto a successor
-- output (`no-position`, `no-successor`). Sections along a translation are
-- not unique out of an algebra that is not generated (`different`).

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Induction.Initiality using (Section)

open import SPT.IR.Algebra using (Algebra; Law)
open import SPT.IR.Description using
  (Desc; ι; σ; δ; indexed; Shape; Mark)
open import SPT.IR.Restriction using (Position; input)
open import SPT.IR.Translation using (Translation; identity)
open import SPT.IR.Translation.Morphism using (Along)

------------------------------------------------------------------------
-- Erasing and duplicating positions

-- Two inputs with the first as output, and one input as output. The first
-- translation drops the second input of a pair; the second uses its one
-- input at both positions of a pair.

pair : Desc {s = lzero} ℕ
pair = δ 𝟚 (λ q → ι (q ₀))

single : Desc {s = lzero} ℕ
single = δ 𝟙 (λ q → ι (q ⋆))

erase-back :
  (c : Shape pair (indexed ℕ (λ e → e)))
  → Position single (indexed ℕ (λ e → e)) ((λ x → pr₁ c ₀) , lift ⋆)
  → Position pair (indexed ℕ (λ e → e)) c
erase-back c (inl x) = inl ₀
erase-back c (inr (lift ()))

erase-input :
  (c : Shape pair (indexed ℕ (λ e → e)))
  (q : Position single (indexed ℕ (λ e → e)) ((λ x → pr₁ c ₀) , lift ⋆))
  → input pair (indexed ℕ (λ e → e)) c (erase-back c q)
    ＝ input single (indexed ℕ (λ e → e)) ((λ x → pr₁ c ₀) , lift ⋆) q
erase-input c (inl x) = refl
erase-input c (inr (lift ()))

erase : Translation (λ e → e) pair single
erase = record
  { shape = λ c → (λ x → pr₁ c ₀) , lift ⋆
  ; back = erase-back
  ; inputs = erase-input
  ; output = λ c → refl
  }

-- The position 1 of a pair is read back by no position of the image.

first : 𝟚 ⊎ Lift lzero 𝟘 → 𝟚
first (inl b) = b
first (inr (lift ()))

erases :
  (c : Shape pair (indexed ℕ (λ e → e)))
  (q : Position single (indexed ℕ (λ e → e)) (Translation.shape erase c))
  → Translation.back erase c q ＝ inl ₁ → 𝟘
erases c (inl x) e = ₀-is-not-₁ (ap first e)
erases c (inr (lift ()))

duplicate-back :
  (c : Shape single (indexed ℕ (λ e → e)))
  → Position pair (indexed ℕ (λ e → e)) ((λ b → pr₁ c ⋆) , lift ⋆)
  → Position single (indexed ℕ (λ e → e)) c
duplicate-back c (inl b) = inl ⋆
duplicate-back c (inr (lift ()))

duplicate-input :
  (c : Shape single (indexed ℕ (λ e → e)))
  (q : Position pair (indexed ℕ (λ e → e)) ((λ b → pr₁ c ⋆) , lift ⋆))
  → input single (indexed ℕ (λ e → e)) c (duplicate-back c q)
    ＝ input pair (indexed ℕ (λ e → e)) ((λ b → pr₁ c ⋆) , lift ⋆) q
duplicate-input c (inl b) = refl
duplicate-input c (inr (lift ()))

duplicate : Translation (λ e → e) single pair
duplicate = record
  { shape = λ c → (λ b → pr₁ c ⋆) , lift ⋆
  ; back = duplicate-back
  ; inputs = duplicate-input
  ; output = λ c → refl
  }

duplicates :
  (c : Shape single (indexed ℕ (λ e → e)))
  → Translation.back duplicate c (inl ₀)
    ＝ Translation.back duplicate c (inl ₁)
duplicates c = refl

------------------------------------------------------------------------
-- A lax translation, and a target that moves

-- A pad n + 0 on the output is absorbed by the output law, which is an
-- identification proved by induction and not a computation: the control
-- with refl fails. Along the successor every input and the output move.

padded : Desc {s = lzero} ℕ
padded = δ 𝟙 (λ q → ι (q ⋆ + zero))

plus-zero : (n : ℕ) → n ＝ n + zero
plus-zero zero = refl
plus-zero (suc n) = ap suc (plus-zero n)

absorb-back :
  (c : Shape padded (indexed ℕ (λ e → e)))
  → Position single (indexed ℕ (λ e → e)) c
  → Position padded (indexed ℕ (λ e → e)) c
absorb-back c (inl x) = inl x
absorb-back c (inr (lift ()))

absorb-input :
  (c : Shape padded (indexed ℕ (λ e → e)))
  (q : Position single (indexed ℕ (λ e → e)) c)
  → input padded (indexed ℕ (λ e → e)) c (absorb-back c q)
    ＝ input single (indexed ℕ (λ e → e)) c q
absorb-input c (inl x) = refl
absorb-input c (inr (lift ()))

absorb : Translation (λ e → e) padded single
absorb = record
  { shape = λ c → c
  ; back = absorb-back
  ; inputs = absorb-input
  ; output = λ c → plus-zero (pr₁ c ⋆)
  }

shifted-back :
  (c : Shape single (indexed ℕ (λ e → e)))
  → Position single (indexed ℕ (λ e → e)) ((λ x → suc (pr₁ c x)) , lift ⋆)
  → Position single (indexed ℕ (λ e → e)) c
shifted-back c (inl x) = inl x
shifted-back c (inr (lift ()))

shifted-input :
  (c : Shape single (indexed ℕ (λ e → e)))
  (q :
    Position single (indexed ℕ (λ e → e)) ((λ x → suc (pr₁ c x)) , lift ⋆))
  → suc (input single (indexed ℕ (λ e → e)) c (shifted-back c q))
    ＝ input single (indexed ℕ (λ e → e)) ((λ x → suc (pr₁ c x)) , lift ⋆) q
shifted-input c (inl x) = refl
shifted-input c (inr (lift ()))

shifted : Translation suc single single
shifted = record
  { shape = λ c → (λ x → suc (pr₁ c x)) , lift ⋆
  ; back = shifted-back
  ; inputs = shifted-input
  ; output = λ c → refl
  }

------------------------------------------------------------------------
-- What the laws refute

-- Each position of the target must read back a position of the source, so
-- a code with no positions has no translation to one with a position. The
-- output law excludes a successor output at the shape whose input is 0.

no-position : Translation (λ e → e) (ι zero) single → 𝟘
no-position τ = lower (Translation.back τ (lift ⋆) (inl ⋆))

successor : Desc {s = lzero} ℕ
successor = δ 𝟙 (λ q → ι (suc (q ⋆)))

no-successor : Translation (λ e → e) single successor → 𝟘
no-successor τ =
  zero-is-not-suc (Translation.output τ ((λ x → zero) , lift ⋆) ⁻¹)

------------------------------------------------------------------------
-- Uniqueness needs a generated source

-- A description with no shapes: every map between its algebras commutes
-- vacuously, and an algebra with two points over the one output has two
-- different sections out of the one-point algebra.

absurd-code : 𝟘 → Desc {s = lzero} 𝟙
absurd-code ()

no-shapes : Desc {s = lzero} 𝟙
no-shapes = σ 𝟘 absurd-code

one-point : Algebra lzero no-shapes
one-point = record
  { K = 𝟙
  ; value = λ x → x
  ; operation = λ z → 𝟘-elim (pr₁ z)
  }

two-points : Algebra lzero no-shapes
two-points = record
  { K = 𝟚
  ; value = λ b → ⋆
  ; operation = λ z → 𝟘-elim (pr₁ z)
  }

one-point-law : Law one-point
one-point-law z = 𝟘-elim (pr₁ z)

two-points-law : Law two-points
two-points-law z = 𝟘-elim (pr₁ z)

module _ (arities : (A : Set) (B : A → Set) → FunExt A B) where

  constant-section :
    𝟚
    → Along arities (identity no-shapes) one-point two-points one-point-law
        two-points-law
  constant-section b = record
    { valuation = λ k → b , refl
    ; equations = λ z → 𝟘-elim (pr₁ z)
    }

  different :
    Section.valuation (constant-section ₀) ⋆
    ＝ Section.valuation (constant-section ₁) ⋆
    → 𝟘
  different e = ₀-is-not-₁ (ap pr₁ e)
