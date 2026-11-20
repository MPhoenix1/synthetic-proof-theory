{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Tree.Binding.Shift where

-- The arithmetic of moving variables under binders. At depth c, moving a
-- variable under d new binders fixes the c bound variables and adds d to
-- the others: on numbers this is `shifted c d` (`shifted`, `shifted-below`,
-- `shifted-above`). Binding's `moved` computes it on the variable's number
-- (`lift-cases`, `to-ℕ-lift`, `to-ℕ-moved`): a bound variable stays bound and
-- a free one passes the new binders (`moved-bound`, `moved-free`).
-- Shifting by e and then by d is
-- shifting by e + d (`shifted-compose`), so moving a variable under e and
-- then d binders is moving it under e + d, after transport along
-- associativity (`moved-compose`).

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Nat.Arithmetic using
  (+-commutes; +-right-preserves-≤ℕˢ; ≤ℕˢ-+-right; ≤ℕˢ-or-above)
import SPT.Cubical.Foundation.Tree.Binding as Binding

------------------------------------------------------------------------
-- On numbers

shifted : ℕ → ℕ → ℕ → ℕ
shifted c d n with ≤ℕˢ-or-above c n
... | inl _ = d + n
... | inr _ = n

shifted-below : {c n : ℕ} (d : ℕ) → n <ℕˢ c → shifted c d n ＝ n
shifted-below {c} {n} d below with ≤ℕˢ-or-above c n
... | inl above = 𝟘-elim (<ℕˢ-irrefl n (≤ℕˢ-trans below above))
... | inr _ = refl

shifted-above : {c n : ℕ} (d : ℕ) → c ≤ℕˢ n → shifted c d n ＝ d + n
shifted-above {c} {n} d above with ≤ℕˢ-or-above c n
... | inl _ = refl
... | inr below = 𝟘-elim (<ℕˢ-irrefl n (≤ℕˢ-trans below above))

-- Exchanging the first two summands under a third.
exchange : (d c t : ℕ) → d + (c + t) ＝ c + (d + t)
exchange d c t =
  +-assoc d c t ⁻¹ ∙
    (ap (λ x → x + t) (+-commutes d c) ∙ +-assoc c d t)

-- Below or above the bound variables.
decide : (n c : ℕ) → (n <ℕˢ c) ⊎ (c ≤ℕˢ n)
decide n c = cases inr inl (≤ℕˢ-or-above c n)

compose-cases :
  (c e d n : ℕ) → (n <ℕˢ c) ⊎ (c ≤ℕˢ n)
  → shifted (c + e) d (shifted c e n) ＝ shifted c (e + d) n
compose-cases c e d n (inl below) =
  ap (shifted (c + e) d) (shifted-below e below) ∙
    (shifted-below d (≤ℕˢ-trans below (≤ℕˢ-+-right c e)) ∙
      shifted-below (e + d) below ⁻¹)
compose-cases c e d n (inr above) =
  ap (shifted (c + e) d) (shifted-above e above) ∙
    (shifted-above d
        (transport (λ x → c + e ≤ℕˢ x) (+-commutes n e)
          (+-right-preserves-≤ℕˢ e above)) ∙
      (+-assoc d e n ⁻¹ ∙ ap (λ x → x + n) (+-commutes d e) ∙
        shifted-above (e + d) above ⁻¹))

shifted-compose :
  (c e d n : ℕ) → shifted (c + e) d (shifted c e n) ＝ shifted c (e + d) n
shifted-compose c e d n = compose-cases c e d n (decide n c)

-- Transport of a variable along a path of scopes keeps its number.
to-ℕ-transport :
  (F : ℕ → ℕ) {a b : ℕ} (q : a ＝ b) (y : Fin (F a))
  → to-ℕ (transport (λ j → Fin (F j)) q y) ＝ to-ℕ y
to-ℕ-transport F refl y = refl

------------------------------------------------------------------------
-- On variables

module _ {ℓo ℓp : Level} (B : Binding.Binding ℓo ℓp) where

  lift-cases :
    {m : ℕ} (c d : ℕ) (s : Fin c ⊎ Fin m)
    → to-ℕ (cases (λ j → j ↑ˡ (d + m)) (λ k → c ↑ʳ (d ↑ʳ k)) s)
      ＝ shifted c d (to-ℕ (join-at c m s))
  lift-cases {m} c d (inl j) =
    to-ℕ-↑ˡ j (d + m) ∙
      (ap (shifted c d) (to-ℕ-↑ˡ j m) ∙
          shifted-below d (to-ℕ-is-below j)) ⁻¹
  lift-cases {m} c d (inr k) =
    to-ℕ-↑ʳ c (d ↑ʳ k) ∙
      (ap (λ x → c + x) (to-ℕ-↑ʳ d k) ∙
        (ap (shifted c d) (to-ℕ-↑ʳ c k) ∙
            (shifted-above d (≤ℕˢ-+-right c (to-ℕ k)) ∙
              exchange d c (to-ℕ k))) ⁻¹)

  to-ℕ-lift :
    {m : ℕ} (c d : ℕ) (x : Fin (c + m))
    → to-ℕ (Binding.lift B c (λ y → d ↑ʳ y) x) ＝ shifted c d (to-ℕ x)
  to-ℕ-lift {m} c d x =
    lift-cases c d (split-at c m x) ∙
      ap (λ y → shifted c d (to-ℕ y)) (join-at-split-at c m x)

  to-ℕ-moved :
    {m : ℕ} (d c : ℕ) (x : Fin (c + m))
    → to-ℕ (Binding.moved B m d c x) ＝ shifted c d (to-ℕ x)
  to-ℕ-moved {m} d c x =
    to-ℕ-transport (λ j → j) (+-assoc c d m ⁻¹)
        (Binding.lift B c (λ y → d ↑ʳ y) x) ∙
      to-ℕ-lift c d x

  -- A bound variable stays bound; a free one passes the d new binders.
  moved-bound :
    {m : ℕ} (c d : ℕ) (j : Fin c)
    → Binding.moved B m d c (j ↑ˡ m) ＝ (j ↑ˡ d) ↑ˡ m
  moved-bound {m} c d j =
    to-ℕ-is-injective
      (to-ℕ-moved d c (j ↑ˡ m) ∙
        (ap (shifted c d) (to-ℕ-↑ˡ j m) ∙
          (shifted-below d (to-ℕ-is-below j) ∙
            (to-ℕ-↑ˡ (j ↑ˡ d) m ∙ to-ℕ-↑ˡ j d) ⁻¹)))

  moved-free :
    {m : ℕ} (c d : ℕ) (k : Fin m)
    → Binding.moved B m d c (c ↑ʳ k) ＝ (c + d) ↑ʳ k
  moved-free {m} c d k =
    to-ℕ-is-injective
      (to-ℕ-moved d c (c ↑ʳ k) ∙
        (ap (shifted c d) (to-ℕ-↑ʳ c k) ∙
          (shifted-above d (≤ℕˢ-+-right c (to-ℕ k)) ∙
            (exchange d c (to-ℕ k) ∙
              (+-assoc c d (to-ℕ k) ⁻¹ ∙
                to-ℕ-↑ʳ (c + d) k ⁻¹)))))

  moved-compose :
    {l : ℕ} (c e d : ℕ) (x : Fin (c + l))
    → transport (λ j → Fin (j + l)) (+-assoc c e d)
        (Binding.moved B l d (c + e) (Binding.moved B l e c x))
      ＝ Binding.moved B l (e + d) c x
  moved-compose {l} c e d x =
    to-ℕ-is-injective
      (to-ℕ-transport (λ j → j + l) (+-assoc c e d)
          (Binding.moved B l d (c + e) (Binding.moved B l e c x)) ∙
        (to-ℕ-moved d (c + e) (Binding.moved B l e c x) ∙
          (ap (shifted (c + e) d) (to-ℕ-moved e c x) ∙
            (shifted-compose c e d (to-ℕ x) ∙
              to-ℕ-moved (e + d) c x ⁻¹))))
