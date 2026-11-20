{-# OPTIONS --safe --without-K --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.OrdinalGeometry.ExactOrder.Comparison where

-- Under LPO any two exact orders are comparable: P is an initial segment
-- of Q, or Q is a proper segment of P (`comparable`).
--
-- The comparison is the Boolean relation x ∼ y, the lower cones of x and
-- y matched, by recursion on both orders:
--
--   x ∼ y = (∀ a < x. ∃ b < y. a ∼ b) ∧ (∀ b < y. ∃ a < x. a ∼ b).
--
-- LPO decides each bounded quantifier through the enumerations (Search),
-- so ∼ is a function into Bool and nothing is chosen. One recursion step
-- is the non-recursive `step`; `related` iterates it along both
-- accessibility proofs, and its value does not depend on them
-- (`irrelevant`). The relation is functional and injective, and preserves
-- and reflects order. A matched point lies below every point without a
-- partner or a source (`over`, `under`), so a minimal point of P without a
-- partner and a minimal point of Q without a source would be matched to
-- each other (`exclusive`). Hence one side is exhausted: every point of P
-- has a partner, which gives an initial map P → Q, or the least point of
-- P without one is the ceiling of a proper segment Q → P.

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Accessibility using (acc; is-accessible)
open import SPT.Cubical.Foundation.Two.Connectives using (_∧_; not)

import SPT.Cubical.OrdinalGeometry.ExactOrder.Base as Order
import SPT.Cubical.OrdinalGeometry.ExactOrder.Maps as Orders
open import SPT.Cubical.OrdinalGeometry.ExactOrder.Exponential.Embedding using
  (Segment)
open import SPT.Cubical.OrdinalGeometry.Presentation.Limit.Discriminator using
  (LPO; Hit)

private
  true≢false : ₁ ＝ ₀ → 𝟘
  true≢false ()

  conjuncts : (u v : 𝟚) → u ∧ v ＝ ₁ → (u ＝ ₁) × (v ＝ ₁)
  conjuncts ₁ ₁ _ = refl , refl
  conjuncts ₁ ₀ ()
  conjuncts ₀ v ()

  conjunction : {u v : 𝟚} → u ＝ ₁ → v ＝ ₁ → u ∧ v ＝ ₁
  conjunction refl refl = refl

  -- not u = true gives u = false; not u = false gives u = true.
  refute : (u : 𝟚) → not u ＝ ₁ → u ＝ ₀
  refute ₀ _ = refl
  refute ₁ ()

  confirm : (u : 𝟚) → not u ＝ ₀ → u ＝ ₁
  confirm ₁ _ = refl
  confirm ₀ ()

------------------------------------------------------------------------
-- Searches decided by LPO

module Search (lpo : LPO) where

  private
    Decision : (ℕ → 𝟚) → Set
    Decision s = Hit s ⊎ ((n : ℕ) → s n ＝ ₀)

    decided : {s : ℕ → 𝟚} → Decision s → 𝟚
    decided (inl _) = ₁
    decided (inr _) = ₀

  -- Mathematical shape: ∃ n. s n = true, as a Boolean.
  any : (ℕ → 𝟚) → 𝟚
  any s = decided (lpo s)

  any-true : (s : ℕ → 𝟚) → any s ＝ ₁ → Hit s
  any-true s = at (lpo s)
    where
    at : (d : Decision s) → decided d ＝ ₁ → Hit s
    at (inl h) _ = h
    at (inr _) ()

  any-false : (s : ℕ → 𝟚) → any s ＝ ₀ → (n : ℕ) → s n ＝ ₀
  any-false s = at (lpo s)
    where
    at : (d : Decision s) → decided d ＝ ₀ → (n : ℕ) → s n ＝ ₀
    at (inl _) ()
    at (inr none) _ = none

  any-intro : (s : ℕ → 𝟚) (n : ℕ) → s n ＝ ₁ → any s ＝ ₁
  any-intro s n p = at (lpo s)
    where
    at : (d : Decision s) → decided d ＝ ₁
    at (inl _) = refl
    at (inr none) = 𝟘-elim (true≢false (p ⁻¹ ∙ none n))

  any-ext : (s t : ℕ → 𝟚) → ((n : ℕ) → s n ＝ t n) → any s ＝ any t
  any-ext s t e = at (lpo s) (lpo t)
    where
    at : (d : Decision s) (d′ : Decision t) → decided d ＝ decided d′
    at (inl _) (inl _) = refl
    at (inr _) (inr _) = refl
    at (inl (n , p)) (inr none) =
      𝟘-elim (true≢false (p ⁻¹ ∙ (e n ∙ none n)))
    at (inr none) (inl (n , p)) =
      𝟘-elim (true≢false (p ⁻¹ ∙ (e n ⁻¹ ∙ none n)))

  -- Mathematical shape: ∃ a. t a = true, over the enumeration of O.
  some : {ℓ : Level} {A : Set ℓ} → Order.Order A → (A → 𝟚) → 𝟚
  some O t = any (λ n → maybe-rec ₀ t (Order.Order.enum O n))

  private
    found : {ℓ : Level} {A : Set ℓ} (t : A → 𝟚) (m : Maybe A)
      → maybe-rec ₀ t m ＝ ₁ → Σ A (λ a → t a ＝ ₁)
    found t (just a) p = a , p
    found t nothing ()

    agree : {ℓ : Level} {A : Set ℓ} (t u : A → 𝟚)
      → ((a : A) → t a ＝ u a) → (m : Maybe A)
      → maybe-rec ₀ t m ＝ maybe-rec ₀ u m
    agree t u e (just a) = e a
    agree t u e nothing = refl

  some-true : {ℓ : Level} {A : Set ℓ} (O : Order.Order A) (t : A → 𝟚)
    → some O t ＝ ₁ → Σ A (λ a → t a ＝ ₁)
  some-true O t p =
    let n , q = any-true (λ n → maybe-rec ₀ t (Order.Order.enum O n)) p
    in found t (Order.Order.enum O n) q

  some-intro : {ℓ : Level} {A : Set ℓ} (O : Order.Order A) (t : A → 𝟚)
    (a : A) → t a ＝ ₁ → some O t ＝ ₁
  some-intro O t a p =
    let n , q = Order.Order.covers O a
    in any-intro (λ n → maybe-rec ₀ t (Order.Order.enum O n)) n
         (ap (maybe-rec ₀ t) q ∙ p)

  some-false : {ℓ : Level} {A : Set ℓ} (O : Order.Order A) (t : A → 𝟚)
    → some O t ＝ ₀ → (a : A) → t a ＝ ₀
  some-false O t p a =
    let n , q = Order.Order.covers O a
    in ap (maybe-rec ₀ t) q ⁻¹
         ∙ any-false (λ n → maybe-rec ₀ t (Order.Order.enum O n)) p n

  some-none : {ℓ : Level} {A : Set ℓ} (O : Order.Order A) (t : A → 𝟚)
    → ((a : A) → t a ＝ ₀) → some O t ＝ ₀
  some-none O t none = settle (some O t) refl
    where
    settle : (u : 𝟚) → some O t ＝ u → some O t ＝ ₀
    settle ₀ p = p
    settle ₁ p =
      let a , q = some-true O t p
      in 𝟘-elim (true≢false (q ⁻¹ ∙ none a))

  some-ext : {ℓ : Level} {A : Set ℓ} (O : Order.Order A) (t u : A → 𝟚)
    → ((a : A) → t a ＝ u a) → some O t ＝ some O u
  some-ext O t u e =
    any-ext (λ n → maybe-rec ₀ t (Order.Order.enum O n))
      (λ n → maybe-rec ₀ u (Order.Order.enum O n))
      (λ n → agree t u e (Order.Order.enum O n))

  -- Mathematical shape: a ↦ t a p if p : a < x, and false otherwise.
  below : {ℓ : Level} {A : Set ℓ} (O : Order.Order A) (x : A)
    → ((a : A) → Order.Order._<_ O a x → 𝟚) → A → 𝟚
  below O x t a = cases (t a) (λ _ → ₀) (Order.Order.compare O a x)

  below-true : {ℓ : Level} {A : Set ℓ} (O : Order.Order A) (x : A)
    (t : (a : A) → Order.Order._<_ O a x → 𝟚) (a : A)
    → below O x t a ＝ ₁
    → Σ (Order.Order._<_ O a x) (λ p → t a p ＝ ₁)
  below-true {A = A} O x t a = at (Order.Order.compare O a x)
    where
    at : (d : Order.Order._<_ O a x ⊎ ((a ＝ x) ⊎ Order.Order._<_ O x a))
      → cases (t a) (λ _ → ₀) d ＝ ₁
      → Σ (Order.Order._<_ O a x) (λ p → t a p ＝ ₁)
    at (inl p) q = p , q
    at (inr _) ()

  below-at : {ℓ : Level} {A : Set ℓ} (O : Order.Order A) (x : A)
    (t : (a : A) → Order.Order._<_ O a x → 𝟚) (a : A)
    → Order.Order._<_ O a x
    → Σ (Order.Order._<_ O a x) (λ p → below O x t a ＝ t a p)
  below-at {A = A} O x t a p = at (Order.Order.compare O a x)
    where
    at : (d : Order.Order._<_ O a x ⊎ ((a ＝ x) ⊎ Order.Order._<_ O x a))
      → Σ (Order.Order._<_ O a x)
          (λ p′ → cases (t a) (λ _ → ₀) d ＝ t a p′)
    at (inl p′) = p′ , refl
    at (inr (inl e)) = 𝟘-elim (Order.Order.irrefl O x
      (transport (λ z → Order.Order._<_ O z x) e p))
    at (inr (inr q)) =
      𝟘-elim (Order.Order.irrefl O a (Order.Order.trans O p q))

  below-false : {ℓ : Level} {A : Set ℓ} (O : Order.Order A) (x : A)
    (t : (a : A) → Order.Order._<_ O a x → 𝟚)
    → ((a : A) (p : Order.Order._<_ O a x) → t a p ＝ ₀)
    → (a : A) → below O x t a ＝ ₀
  below-false {A = A} O x t e a = at (Order.Order.compare O a x)
    where
    at : (d : Order.Order._<_ O a x ⊎ ((a ＝ x) ⊎ Order.Order._<_ O x a))
      → cases (t a) (λ _ → ₀) d ＝ ₀
    at (inl p) = e a p
    at (inr _) = refl

  below-ext : {ℓ : Level} {A : Set ℓ} (O : Order.Order A) (x : A)
    (t u : (a : A) → Order.Order._<_ O a x → 𝟚)
    → ((a : A) (p : Order.Order._<_ O a x) → t a p ＝ u a p)
    → (a : A) → below O x t a ＝ below O x u a
  below-ext {A = A} O x t u e a = at (Order.Order.compare O a x)
    where
    at : (d : Order.Order._<_ O a x ⊎ ((a ＝ x) ⊎ Order.Order._<_ O x a))
      → cases (t a) (λ _ → ₀) d ＝ cases (u a) (λ _ → ₀) d
    at (inl p) = e a p
    at (inr _) = refl

  -- Mathematical shape: a least point m of O with t m = true.
  Minimal : {ℓ : Level} {A : Set ℓ} → Order.Order A → (A → 𝟚) → Set ℓ
  Minimal {A = A} O t = Σ A (λ m →
    (t m ＝ ₁) × ((a : A) → Order.Order._<_ O a m → t a ＝ ₀))

  private
    -- One descent step: a point below x satisfying t, or x is minimal.
    choose : {ℓ : Level} {A : Set ℓ} (O : Order.Order A) (t : A → 𝟚)
      (x : A) → t x ＝ ₁
      → ((a : A) → Order.Order._<_ O a x → t a ＝ ₁ → Minimal O t)
      → (u : 𝟚) → some O (below O x (λ a _ → t a)) ＝ u → Minimal O t
    choose O t x tx deeper ₁ p =
      let a , q = some-true O (below O x (λ a _ → t a)) p
          r , s = below-true O x (λ a _ → t a) a q
      in deeper a r s
    choose O t x tx deeper ₀ p =
      x , tx , λ a r →
        let r′ , e = below-at O x (λ a _ → t a) a r
        in e ⁻¹ ∙ some-false O (below O x (λ a _ → t a)) p a

    descend : {ℓ : Level} {A : Set ℓ} (O : Order.Order A) (t : A → 𝟚)
      (x : A) → is-accessible (Order.Order._<_ O) x → t x ＝ ₁ → Minimal O t
    descend O t x (acc smaller) tx =
      choose O t x tx (λ a r → descend O t a (smaller a r))
        (some O (below O x (λ a _ → t a))) refl

  minimal : {ℓ : Level} {A : Set ℓ} (O : Order.Order A) (t : A → 𝟚)
    (x : A) → t x ＝ ₁ → Minimal O t
  minimal O t x = descend O t x (Order.Order.wf O x)

------------------------------------------------------------------------
-- The matching of lower cones

module Matching (lpo : LPO) {ℓ : Level} {A B : Set ℓ}
  (P : Order.Order A) (Q : Order.Order B) where

  open Search lpo
  open Order.Order P using () renaming
    (_<_ to _<ᴬ_; compare to compareᴬ; irrefl to irreflᴬ; wf to wfᴬ)
  open Order.Order Q using () renaming
    (_<_ to _<ᴮ_; compare to compareᴮ; irrefl to irreflᴮ; wf to wfᴮ)

  -- A Boolean test on pairs of points below x and below y.
  Test : A → B → Set ℓ
  Test x y = (a : A) → a <ᴬ x → (b : B) → b <ᴮ y → 𝟚

  -- Mathematical shape: a < x ∧ b < y ∧ r a b.
  match : (x : A) (y : B) → Test x y → A → B → 𝟚
  match x y r a b =
    below P x (λ a′ p → below Q y (λ b′ q → r a′ p b′ q) b) a

  -- Mathematical shape: a < x ∧ ¬ ∃ b. match a b.
  unmatchedᴬ : (x : A) (y : B) → Test x y → A → 𝟚
  unmatchedᴬ x y r = below P x (λ a _ → not (some Q (match x y r a)))

  -- Mathematical shape: b < y ∧ ¬ ∃ a. match a b.
  unmatchedᴮ : (x : A) (y : B) → Test x y → B → 𝟚
  unmatchedᴮ x y r =
    below Q y (λ b _ → not (some P (λ a → match x y r a b)))

  -- One recursion step: every point below x is matched below y, and every
  -- point below y is matched below x.
  step : (x : A) (y : B) → Test x y → 𝟚
  step x y r =
    not (some P (unmatchedᴬ x y r)) ∧ not (some Q (unmatchedᴮ x y r))

  private
    match-ext : (x : A) (y : B) (r r′ : Test x y)
      → ((a : A) (p : a <ᴬ x) (b : B) (q : b <ᴮ y)
          → r a p b q ＝ r′ a p b q)
      → (a : A) (b : B) → match x y r a b ＝ match x y r′ a b
    match-ext x y r r′ e a b =
      below-ext P x
        (λ a′ p → below Q y (λ b′ q → r a′ p b′ q) b)
        (λ a′ p → below Q y (λ b′ q → r′ a′ p b′ q) b)
        (λ a′ p → below-ext Q y (λ b′ q → r a′ p b′ q)
          (λ b′ q → r′ a′ p b′ q) (λ b′ q → e a′ p b′ q) b)
        a

  step-ext : (x : A) (y : B) (r r′ : Test x y)
    → ((a : A) (p : a <ᴬ x) (b : B) (q : b <ᴮ y) → r a p b q ＝ r′ a p b q)
    → step x y r ＝ step x y r′
  step-ext x y r r′ e =
    ap₂ _∧_
      (ap not (some-ext P (unmatchedᴬ x y r) (unmatchedᴬ x y r′)
        (below-ext P x
          (λ a _ → not (some Q (match x y r a)))
          (λ a _ → not (some Q (match x y r′ a)))
          (λ a _ → ap not (some-ext Q (match x y r a) (match x y r′ a)
            (match-ext x y r r′ e a))))))
      (ap not (some-ext Q (unmatchedᴮ x y r) (unmatchedᴮ x y r′)
        (below-ext Q y
          (λ b _ → not (some P (λ a → match x y r a b)))
          (λ b _ → not (some P (λ a → match x y r′ a b)))
          (λ b _ → ap not (some-ext P (λ a → match x y r a b)
            (λ a → match x y r′ a b) (λ a → match-ext x y r r′ e a b))))))

  -- The step iterated along accessibility.
  related : (x : A) (y : B) → is-accessible _<ᴬ_ x → is-accessible _<ᴮ_ y → 𝟚
  related x y (acc smallerᴬ) (acc smallerᴮ) =
    step x y (λ a p b q → related a b (smallerᴬ a p) (smallerᴮ b q))

  -- The value does not depend on the accessibility proofs.
  irrelevant : (x : A) (y : B) (α α′ : is-accessible _<ᴬ_ x)
    (β β′ : is-accessible _<ᴮ_ y)
    → related x y α β ＝ related x y α′ β′
  irrelevant x y (acc smallerᴬ) (acc smallerᴬ′) (acc smallerᴮ)
    (acc smallerᴮ′) =
    step-ext x y
      (λ a p b q → related a b (smallerᴬ a p) (smallerᴮ b q))
      (λ a p b q → related a b (smallerᴬ′ a p) (smallerᴮ′ b q))
      (λ a p b q → irrelevant a b (smallerᴬ a p) (smallerᴬ′ a p)
        (smallerᴮ b q) (smallerᴮ′ b q))

  -- Mathematical shape: x ∼ y, the lower cones of x and y matched.
  infix 30 _∼_
  _∼_ : A → B → 𝟚
  x ∼ y = related x y (wfᴬ x) (wfᴮ y)

  unfold : (x : A) (y : B) → x ∼ y ＝ step x y (λ a _ b _ → a ∼ b)
  unfold x y = at (wfᴬ x) (wfᴮ y)
    where
    at : (α : is-accessible _<ᴬ_ x) (β : is-accessible _<ᴮ_ y)
      → related x y α β ＝ step x y (λ a _ b _ → a ∼ b)
    at (acc smallerᴬ) (acc smallerᴮ) =
      step-ext x y
        (λ a p b q → related a b (smallerᴬ a p) (smallerᴮ b q))
        (λ a _ b _ → a ∼ b)
        (λ a p b q → irrelevant a b (smallerᴬ a p) (wfᴬ a)
          (smallerᴮ b q) (wfᴮ b))

  -- A step for a test that ignores the witnesses, read forth.
  step-forth : (x : A) (y : B) (s : A → B → 𝟚)
    → step x y (λ a _ b _ → s a b) ＝ ₁
    → (a : A) → a <ᴬ x → Σ B (λ b → b <ᴮ y × (s a b ＝ ₁))
  step-forth x y s e a p =
    let p′ , u = below-at P x (λ a′ _ → not (some Q (match x y r a′))) a p
        b , m = some-true Q (match x y r a)
          (confirm (some Q (match x y r a)) (u ⁻¹ ∙ none))
        p″ , m′ = below-true P x
          (λ a′ p‴ → below Q y (λ b′ q → r a′ p‴ b′ q) b) a m
        q , t = below-true Q y (λ b′ q → r a p″ b′ q) b m′
    in b , q , t
    where
    r : Test x y
    r a _ b _ = s a b

    none : unmatchedᴬ x y r a ＝ ₀
    none = some-false P (unmatchedᴬ x y r)
      (refute (some P (unmatchedᴬ x y r))
        (pr₁ (conjuncts (not (some P (unmatchedᴬ x y r)))
          (not (some Q (unmatchedᴮ x y r))) e)))
      a

  -- The same step, read back.
  step-back : (x : A) (y : B) (s : A → B → 𝟚)
    → step x y (λ a _ b _ → s a b) ＝ ₁
    → (b : B) → b <ᴮ y → Σ A (λ a → a <ᴬ x × (s a b ＝ ₁))
  step-back x y s e b q =
    let q′ , u = below-at Q y
          (λ b′ _ → not (some P (λ a → match x y r a b′))) b q
        a , m = some-true P (λ a → match x y r a b)
          (confirm (some P (λ a → match x y r a b)) (u ⁻¹ ∙ none))
        p , m′ = below-true P x
          (λ a′ p′ → below Q y (λ b′ q″ → r a′ p′ b′ q″) b) a m
        q″ , t = below-true Q y (λ b′ q‴ → r a p b′ q‴) b m′
    in a , p , t
    where
    r : Test x y
    r a _ b _ = s a b

    none : unmatchedᴮ x y r b ＝ ₀
    none = some-false Q (unmatchedᴮ x y r)
      (refute (some Q (unmatchedᴮ x y r))
        (pr₂ (conjuncts (not (some P (unmatchedᴬ x y r)))
          (not (some Q (unmatchedᴮ x y r))) e)))
      b

  -- Partners in both directions make the step true.
  step-intro : (x : A) (y : B) (s : A → B → 𝟚)
    → ((a : A) → a <ᴬ x → Σ B (λ b → b <ᴮ y × (s a b ＝ ₁)))
    → ((b : B) → b <ᴮ y → Σ A (λ a → a <ᴬ x × (s a b ＝ ₁)))
    → step x y (λ a _ b _ → s a b) ＝ ₁
  step-intro x y s partnersᴬ partnersᴮ =
    conjunction
      (ap not (some-none P (unmatchedᴬ x y r)
        (below-false P x (λ a _ → not (some Q (match x y r a)))
          λ a p → let b , q , t = partnersᴬ a p in
            ap not (some-intro Q (match x y r a) b (matched a b p q t)))))
      (ap not (some-none Q (unmatchedᴮ x y r)
        (below-false Q y (λ b _ → not (some P (λ a → match x y r a b)))
          λ b q → let a , p , t = partnersᴮ b q in
            ap not (some-intro P (λ a → match x y r a b) a
              (matched a b p q t)))))
    where
    r : Test x y
    r a _ b _ = s a b

    matched : (a : A) (b : B) → a <ᴬ x → b <ᴮ y → s a b ＝ ₁
      → match x y r a b ＝ ₁
    matched a b p q t =
      let p′ , u = below-at P x
            (λ a′ p″ → below Q y (λ b′ q′ → r a′ p″ b′ q′) b) a p
          q′ , v = below-at Q y (λ b′ q″ → r a p′ b′ q″) b q
      in u ∙ (v ∙ t)

  -- Mathematical shape: x ∼ y → a < x → ∃ b < y. a ∼ b.
  forth : (x : A) (y : B) → x ∼ y ＝ ₁
    → (a : A) → a <ᴬ x → Σ B (λ b → b <ᴮ y × (a ∼ b ＝ ₁))
  forth x y e = step-forth x y _∼_ (unfold x y ⁻¹ ∙ e)

  -- Mathematical shape: x ∼ y → b < y → ∃ a < x. a ∼ b.
  back : (x : A) (y : B) → x ∼ y ＝ ₁
    → (b : B) → b <ᴮ y → Σ A (λ a → a <ᴬ x × (a ∼ b ＝ ₁))
  back x y e = step-back x y _∼_ (unfold x y ⁻¹ ∙ e)

  intro : (x : A) (y : B)
    → ((a : A) → a <ᴬ x → Σ B (λ b → b <ᴮ y × (a ∼ b ＝ ₁)))
    → ((b : B) → b <ᴮ y → Σ A (λ a → a <ᴬ x × (a ∼ b ＝ ₁)))
    → x ∼ y ＝ ₁
  intro x y partnersᴬ partnersᴮ =
    unfold x y ∙ (step-intro x y _∼_ partnersᴬ partnersᴮ)

  functional : (x : A) → is-accessible _<ᴬ_ x → (b b′ : B)
    → x ∼ b ＝ ₁ → x ∼ b′ ＝ ₁ → b ＝ b′
  functional x (acc smaller) b b′ e e′ =
    settle (λ a p → functional a (smaller a p)) (compareᴮ b b′)
    where
    settle : ((a : A) → a <ᴬ x → (c d : B)
        → a ∼ c ＝ ₁ → a ∼ d ＝ ₁ → c ＝ d)
      → b <ᴮ b′ ⊎ ((b ＝ b′) ⊎ b′ <ᴮ b) → b ＝ b′
    settle ih (inr (inl same)) = same
    settle ih (inl b<b′) =
      let a , a<x , f = back x b′ e′ b b<b′
          c , c<b , g = forth x b e a a<x
      in 𝟘-elim (irreflᴮ b
           (transport (λ z → z <ᴮ b) (ih a a<x c b g f) c<b))
    settle ih (inr (inr b′<b)) =
      let a , a<x , f = back x b e b′ b′<b
          c , c<b′ , g = forth x b′ e′ a a<x
      in 𝟘-elim (irreflᴮ b′
           (transport (λ z → z <ᴮ b′) (ih a a<x c b′ g f) c<b′))

  injective : (y : B) → is-accessible _<ᴮ_ y → (a a′ : A)
    → a ∼ y ＝ ₁ → a′ ∼ y ＝ ₁ → a ＝ a′
  injective y (acc smaller) a a′ e e′ =
    settle (λ b q → injective b (smaller b q)) (compareᴬ a a′)
    where
    settle : ((b : B) → b <ᴮ y → (c d : A)
        → c ∼ b ＝ ₁ → d ∼ b ＝ ₁ → c ＝ d)
      → a <ᴬ a′ ⊎ ((a ＝ a′) ⊎ a′ <ᴬ a) → a ＝ a′
    settle ih (inr (inl same)) = same
    settle ih (inl a<a′) =
      let b , b<y , f = forth a′ y e′ a a<a′
          c , c<a , g = back a y e b b<y
      in 𝟘-elim (irreflᴬ a
           (transport (λ z → z <ᴬ a) (ih b b<y c a g f) c<a))
    settle ih (inr (inr a′<a)) =
      let b , b<y , f = forth a y e a′ a′<a
          c , c<a′ , g = back a′ y e′ b b<y
      in 𝟘-elim (irreflᴬ a′
           (transport (λ z → z <ᴬ a′) (ih b b<y c a′ g f) c<a′))

  preserves : (a a′ : A) (b b′ : B) → a ∼ b ＝ ₁ → a′ ∼ b′ ＝ ₁
    → a <ᴬ a′ → b <ᴮ b′
  preserves a a′ b b′ e e′ p =
    let c , c<b′ , f = forth a′ b′ e′ a p
    in transport (λ z → z <ᴮ b′) (functional a (wfᴬ a) c b f e) c<b′

  reflects : (a a′ : A) (b b′ : B) → a ∼ b ＝ ₁ → a′ ∼ b′ ＝ ₁
    → b <ᴮ b′ → a <ᴬ a′
  reflects a a′ b b′ e e′ q =
    let c , c<a′ , f = back a′ b′ e′ b q
    in transport (λ z → z <ᴬ a′) (injective b (wfᴮ b) c a f e) c<a′

  -- Mathematical shape: ∃ b. x ∼ b.
  partner : A → 𝟚
  partner x = some Q (λ b → x ∼ b)

  -- Mathematical shape: ∃ a. a ∼ y.
  source : B → 𝟚
  source y = some P (λ a → a ∼ y)

  -- A matched point of Q lies below every point without a source.
  under : (y : B) → source y ＝ ₀ → (a : A) (b : B) → a ∼ b ＝ ₁
    → b <ᴮ y
  under y none a b e = place (compareᴮ b y)
    where
    place : b <ᴮ y ⊎ ((b ＝ y) ⊎ y <ᴮ b) → b <ᴮ y
    place (inl q) = q
    place (inr (inl same)) = 𝟘-elim (true≢false (
      ((some-intro P (λ c → c ∼ y) a
        (transport (λ z → a ∼ z ＝ ₁) same e)) ⁻¹)
      ∙ none))
    place (inr (inr q)) =
      let c , c<a , f = back a b e y q
      in 𝟘-elim (true≢false
           (some-intro P (λ c → c ∼ y) c f ⁻¹ ∙ none))

  -- A matched point of P lies below every point without a partner.
  over : (x : A) → partner x ＝ ₀ → (a : A) (b : B) → a ∼ b ＝ ₁
    → a <ᴬ x
  over x none a b e = place (compareᴬ a x)
    where
    place : a <ᴬ x ⊎ ((a ＝ x) ⊎ x <ᴬ a) → a <ᴬ x
    place (inl p) = p
    place (inr (inl same)) = 𝟘-elim (true≢false (
      ((some-intro Q (λ d → x ∼ d) b
        (transport (λ z → z ∼ b ＝ ₁) same e)) ⁻¹)
      ∙ none))
    place (inr (inr p)) =
      let d , d<b , f = forth a b e x p
      in 𝟘-elim (true≢false
           (some-intro Q (λ d → x ∼ d) d f ⁻¹ ∙ none))

  -- Minimal points without a partner and without a source would be
  -- matched to each other.
  exclusive : (x : A) (y : B)
    → partner x ＝ ₀ → ((a : A) → a <ᴬ x → partner a ＝ ₁)
    → source y ＝ ₀ → ((b : B) → b <ᴮ y → source b ＝ ₁)
    → 𝟘
  exclusive x y lonelyᴬ pairedᴬ lonelyᴮ pairedᴮ =
    true≢false (((some-intro Q (λ b → x ∼ b) y
      (intro x y partnered sourced)) ⁻¹) ∙ lonelyᴬ)
    where
    partnered : (a : A) → a <ᴬ x → Σ B (λ b → b <ᴮ y × (a ∼ b ＝ ₁))
    partnered a p =
      let b , e = some-true Q (λ b → a ∼ b) (pairedᴬ a p)
      in b , under y lonelyᴮ a b e , e

    sourced : (b : B) → b <ᴮ y → Σ A (λ a → a <ᴬ x × (a ∼ b ＝ ₁))
    sourced b q =
      let a , e = some-true P (λ a → a ∼ b) (pairedᴮ b q)
      in a , over x lonelyᴬ a b e , e

  -- Every point of P has a partner: an initial map P → Q.
  initial : ((x : A) → partner x ＝ ₁) → Orders.Initial P Q
  initial total = record
    { map = image
    ; strict = λ {x} {x′} p → preserves x x′ (image x) (image x′)
        (image-matched x) (image-matched x′) p
    ; lower = λ x b q →
        let a , a<x , e = back x (image x) (image-matched x) b q
        in a , functional a (wfᴬ a) (image a) b (image-matched a) e
    }
    where
    image : A → B
    image x = pr₁ (some-true Q (λ b → x ∼ b) (total x))

    image-matched : (x : A) → x ∼ image x ＝ ₁
    image-matched x = pr₂ (some-true Q (λ b → x ∼ b) (total x))

  -- A point of P without a partner: the least one is the ceiling of a
  -- proper segment Q → P, since then every point of Q has a source.
  segment : (x : A) → not (partner x) ＝ ₁ → Segment Q P
  segment x g = record
    { embed = origin
    ; cut = ceiling
    ; below = λ y → over ceiling lonely (origin y) y (origin-matched y)
    ; preserve = λ {y} {y′} q → reflects (origin y) (origin y′) y y′
        (origin-matched y) (origin-matched y′) q
    ; cover = λ a p →
        let b , e = some-true Q (λ b → a ∼ b) (paired a p)
        in b , injective b (wfᴮ b) (origin b) a (origin-matched b) e
    }
    where
    least : Minimal P (λ x → not (partner x))
    least = minimal P (λ x → not (partner x)) x g

    ceiling : A
    ceiling = pr₁ least

    lonely : partner ceiling ＝ ₀
    lonely = refute (partner ceiling) (pr₁ (pr₂ least))

    paired : (a : A) → a <ᴬ ceiling → partner a ＝ ₁
    paired a p = confirm (partner a) (pr₂ (pr₂ least) a p)

    sourced : (y : B) → source y ＝ ₁
    sourced y = settle (source y) refl
      where
      settle : (u : 𝟚) → source y ＝ u → source y ＝ ₁
      settle ₁ p = p
      settle ₀ p =
        let b , h , k = minimal Q (λ b → not (source b)) y (ap not p)
        in 𝟘-elim (exclusive ceiling b lonely paired
             (refute (source b) h)
             (λ b′ q → confirm (source b′) (k b′ q)))

    origin : B → A
    origin y = pr₁ (some-true P (λ a → a ∼ y) (sourced y))

    origin-matched : (y : B) → origin y ∼ y ＝ ₁
    origin-matched y = pr₂ (some-true P (λ a → a ∼ y) (sourced y))

  -- Mathematical shape: P ≤ Q ⊎ Q < P.
  comparable : Orders.Initial P Q ⊎ Segment Q P
  comparable = settle (some P (λ x → not (partner x))) refl
    where
    settle : (u : 𝟚) → some P (λ x → not (partner x)) ＝ u
      → Orders.Initial P Q ⊎ Segment Q P
    settle ₀ none = inl (initial λ x →
      confirm (partner x) (some-false P (λ x → not (partner x)) none x))
    settle ₁ found =
      let x , g = some-true P (λ x → not (partner x)) found
      in inr (segment x g)

-- Mathematical shape: LPO → P ≤ Q ⊎ Q < P, for exact orders P and Q.
comparable : LPO → {ℓ : Level} {A B : Set ℓ}
  (P : Order.Order A) (Q : Order.Order B)
  → Orders.Initial P Q ⊎ Segment Q P
comparable lpo P Q = Matching.comparable lpo P Q
