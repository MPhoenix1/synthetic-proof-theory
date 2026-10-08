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

open import Agda.Primitive using (Level)
open import Data.Bool using (Bool; true; false; _∧_; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing; maybe′)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)

open import SPT.Cubical.Core.WellFounded using (Acc; acc)
import SPT.Cubical.OrdinalGeometry.ExactOrder.Base as Order
import SPT.Cubical.OrdinalGeometry.ExactOrder.Maps as Orders
open import SPT.Cubical.OrdinalGeometry.ExactOrder.Exponential.Embedding using
  (Segment)
open import SPT.Cubical.OrdinalGeometry.Presentation.Limit.Discriminator using
  (LPO; Hit)

private
  true≢false : true ≡ false → ⊥
  true≢false ()

  conjuncts : (u v : Bool) → u ∧ v ≡ true → u ≡ true × v ≡ true
  conjuncts true true _ = refl , refl
  conjuncts true false ()
  conjuncts false v ()

  conjunction : {u v : Bool} → u ≡ true → v ≡ true → u ∧ v ≡ true
  conjunction refl refl = refl

  -- not u = true gives u = false; not u = false gives u = true.
  refute : (u : Bool) → not u ≡ true → u ≡ false
  refute false _ = refl
  refute true ()

  confirm : (u : Bool) → not u ≡ false → u ≡ true
  confirm true _ = refl
  confirm false ()

------------------------------------------------------------------------
-- Searches decided by LPO

module Search (lpo : LPO) where

  private
    Decision : (ℕ → Bool) → Set
    Decision s = Hit s ⊎ ((n : ℕ) → s n ≡ false)

    decided : {s : ℕ → Bool} → Decision s → Bool
    decided (inj₁ _) = true
    decided (inj₂ _) = false

  -- Mathematical shape: ∃ n. s n = true, as a Boolean.
  any : (ℕ → Bool) → Bool
  any s = decided (lpo s)

  any-true : (s : ℕ → Bool) → any s ≡ true → Hit s
  any-true s = at (lpo s)
    where
    at : (d : Decision s) → decided d ≡ true → Hit s
    at (inj₁ h) _ = h
    at (inj₂ _) ()

  any-false : (s : ℕ → Bool) → any s ≡ false → (n : ℕ) → s n ≡ false
  any-false s = at (lpo s)
    where
    at : (d : Decision s) → decided d ≡ false → (n : ℕ) → s n ≡ false
    at (inj₁ _) ()
    at (inj₂ none) _ = none

  any-intro : (s : ℕ → Bool) (n : ℕ) → s n ≡ true → any s ≡ true
  any-intro s n p = at (lpo s)
    where
    at : (d : Decision s) → decided d ≡ true
    at (inj₁ _) = refl
    at (inj₂ none) = ⊥-elim (true≢false (trans (sym p) (none n)))

  any-ext : (s t : ℕ → Bool) → ((n : ℕ) → s n ≡ t n) → any s ≡ any t
  any-ext s t e = at (lpo s) (lpo t)
    where
    at : (d : Decision s) (d′ : Decision t) → decided d ≡ decided d′
    at (inj₁ _) (inj₁ _) = refl
    at (inj₂ _) (inj₂ _) = refl
    at (inj₁ (n , p)) (inj₂ none) =
      ⊥-elim (true≢false (trans (sym p) (trans (e n) (none n))))
    at (inj₂ none) (inj₁ (n , p)) =
      ⊥-elim (true≢false (trans (sym p) (trans (sym (e n)) (none n))))

  -- Mathematical shape: ∃ a. t a = true, over the enumeration of O.
  some : {ℓ : Level} {A : Set ℓ} → Order.Order A → (A → Bool) → Bool
  some O t = any (λ n → maybe′ t false (Order.Order.enum O n))

  private
    found : {ℓ : Level} {A : Set ℓ} (t : A → Bool) (m : Maybe A)
      → maybe′ t false m ≡ true → Σ A (λ a → t a ≡ true)
    found t (just a) p = a , p
    found t nothing ()

    agree : {ℓ : Level} {A : Set ℓ} (t u : A → Bool)
      → ((a : A) → t a ≡ u a) → (m : Maybe A)
      → maybe′ t false m ≡ maybe′ u false m
    agree t u e (just a) = e a
    agree t u e nothing = refl

  some-true : {ℓ : Level} {A : Set ℓ} (O : Order.Order A) (t : A → Bool)
    → some O t ≡ true → Σ A (λ a → t a ≡ true)
  some-true O t p =
    let n , q = any-true (λ n → maybe′ t false (Order.Order.enum O n)) p
    in found t (Order.Order.enum O n) q

  some-intro : {ℓ : Level} {A : Set ℓ} (O : Order.Order A) (t : A → Bool)
    (a : A) → t a ≡ true → some O t ≡ true
  some-intro O t a p =
    let n , q = Order.Order.covers O a
    in any-intro (λ n → maybe′ t false (Order.Order.enum O n)) n
         (trans (cong (maybe′ t false) q) p)

  some-false : {ℓ : Level} {A : Set ℓ} (O : Order.Order A) (t : A → Bool)
    → some O t ≡ false → (a : A) → t a ≡ false
  some-false O t p a =
    let n , q = Order.Order.covers O a
    in trans (sym (cong (maybe′ t false) q))
         (any-false (λ n → maybe′ t false (Order.Order.enum O n)) p n)

  some-none : {ℓ : Level} {A : Set ℓ} (O : Order.Order A) (t : A → Bool)
    → ((a : A) → t a ≡ false) → some O t ≡ false
  some-none O t none = settle (some O t) refl
    where
    settle : (u : Bool) → some O t ≡ u → some O t ≡ false
    settle false p = p
    settle true p =
      let a , q = some-true O t p
      in ⊥-elim (true≢false (trans (sym q) (none a)))

  some-ext : {ℓ : Level} {A : Set ℓ} (O : Order.Order A) (t u : A → Bool)
    → ((a : A) → t a ≡ u a) → some O t ≡ some O u
  some-ext O t u e =
    any-ext (λ n → maybe′ t false (Order.Order.enum O n))
      (λ n → maybe′ u false (Order.Order.enum O n))
      (λ n → agree t u e (Order.Order.enum O n))

  -- Mathematical shape: a ↦ t a p if p : a < x, and false otherwise.
  below : {ℓ : Level} {A : Set ℓ} (O : Order.Order A) (x : A)
    → ((a : A) → Order.Order._<_ O a x → Bool) → A → Bool
  below O x t a = [ t a , (λ _ → false) ]′ (Order.Order.compare O a x)

  below-true : {ℓ : Level} {A : Set ℓ} (O : Order.Order A) (x : A)
    (t : (a : A) → Order.Order._<_ O a x → Bool) (a : A)
    → below O x t a ≡ true
    → Σ (Order.Order._<_ O a x) (λ p → t a p ≡ true)
  below-true {A = A} O x t a = at (Order.Order.compare O a x)
    where
    at : (d : Order.Order._<_ O a x ⊎ (a ≡ x ⊎ Order.Order._<_ O x a))
      → [ t a , (λ _ → false) ]′ d ≡ true
      → Σ (Order.Order._<_ O a x) (λ p → t a p ≡ true)
    at (inj₁ p) q = p , q
    at (inj₂ _) ()

  below-at : {ℓ : Level} {A : Set ℓ} (O : Order.Order A) (x : A)
    (t : (a : A) → Order.Order._<_ O a x → Bool) (a : A)
    → Order.Order._<_ O a x
    → Σ (Order.Order._<_ O a x) (λ p → below O x t a ≡ t a p)
  below-at {A = A} O x t a p = at (Order.Order.compare O a x)
    where
    at : (d : Order.Order._<_ O a x ⊎ (a ≡ x ⊎ Order.Order._<_ O x a))
      → Σ (Order.Order._<_ O a x)
          (λ p′ → [ t a , (λ _ → false) ]′ d ≡ t a p′)
    at (inj₁ p′) = p′ , refl
    at (inj₂ (inj₁ e)) = ⊥-elim (Order.Order.irrefl O x
      (subst (λ z → Order.Order._<_ O z x) e p))
    at (inj₂ (inj₂ q)) =
      ⊥-elim (Order.Order.irrefl O a (Order.Order.trans O p q))

  below-false : {ℓ : Level} {A : Set ℓ} (O : Order.Order A) (x : A)
    (t : (a : A) → Order.Order._<_ O a x → Bool)
    → ((a : A) (p : Order.Order._<_ O a x) → t a p ≡ false)
    → (a : A) → below O x t a ≡ false
  below-false {A = A} O x t e a = at (Order.Order.compare O a x)
    where
    at : (d : Order.Order._<_ O a x ⊎ (a ≡ x ⊎ Order.Order._<_ O x a))
      → [ t a , (λ _ → false) ]′ d ≡ false
    at (inj₁ p) = e a p
    at (inj₂ _) = refl

  below-ext : {ℓ : Level} {A : Set ℓ} (O : Order.Order A) (x : A)
    (t u : (a : A) → Order.Order._<_ O a x → Bool)
    → ((a : A) (p : Order.Order._<_ O a x) → t a p ≡ u a p)
    → (a : A) → below O x t a ≡ below O x u a
  below-ext {A = A} O x t u e a = at (Order.Order.compare O a x)
    where
    at : (d : Order.Order._<_ O a x ⊎ (a ≡ x ⊎ Order.Order._<_ O x a))
      → [ t a , (λ _ → false) ]′ d ≡ [ u a , (λ _ → false) ]′ d
    at (inj₁ p) = e a p
    at (inj₂ _) = refl

  -- Mathematical shape: a least point m of O with t m = true.
  Minimal : {ℓ : Level} {A : Set ℓ} → Order.Order A → (A → Bool) → Set ℓ
  Minimal {A = A} O t = Σ A (λ m →
    t m ≡ true × ((a : A) → Order.Order._<_ O a m → t a ≡ false))

  private
    -- One descent step: a point below x satisfying t, or x is minimal.
    choose : {ℓ : Level} {A : Set ℓ} (O : Order.Order A) (t : A → Bool)
      (x : A) → t x ≡ true
      → ((a : A) → Order.Order._<_ O a x → t a ≡ true → Minimal O t)
      → (u : Bool) → some O (below O x (λ a _ → t a)) ≡ u → Minimal O t
    choose O t x tx deeper true p =
      let a , q = some-true O (below O x (λ a _ → t a)) p
          r , s = below-true O x (λ a _ → t a) a q
      in deeper a r s
    choose O t x tx deeper false p =
      x , tx , λ a r →
        let r′ , e = below-at O x (λ a _ → t a) a r
        in trans (sym e) (some-false O (below O x (λ a _ → t a)) p a)

    descend : {ℓ : Level} {A : Set ℓ} (O : Order.Order A) (t : A → Bool)
      (x : A) → Acc (Order.Order._<_ O) x → t x ≡ true → Minimal O t
    descend O t x (acc smaller) tx =
      choose O t x tx (λ a r → descend O t a (smaller a r))
        (some O (below O x (λ a _ → t a))) refl

  minimal : {ℓ : Level} {A : Set ℓ} (O : Order.Order A) (t : A → Bool)
    (x : A) → t x ≡ true → Minimal O t
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
  Test x y = (a : A) → a <ᴬ x → (b : B) → b <ᴮ y → Bool

  -- Mathematical shape: a < x ∧ b < y ∧ r a b.
  match : (x : A) (y : B) → Test x y → A → B → Bool
  match x y r a b =
    below P x (λ a′ p → below Q y (λ b′ q → r a′ p b′ q) b) a

  -- Mathematical shape: a < x ∧ ¬ ∃ b. match a b.
  unmatchedᴬ : (x : A) (y : B) → Test x y → A → Bool
  unmatchedᴬ x y r = below P x (λ a _ → not (some Q (match x y r a)))

  -- Mathematical shape: b < y ∧ ¬ ∃ a. match a b.
  unmatchedᴮ : (x : A) (y : B) → Test x y → B → Bool
  unmatchedᴮ x y r =
    below Q y (λ b _ → not (some P (λ a → match x y r a b)))

  -- One recursion step: every point below x is matched below y, and every
  -- point below y is matched below x.
  step : (x : A) (y : B) → Test x y → Bool
  step x y r =
    not (some P (unmatchedᴬ x y r)) ∧ not (some Q (unmatchedᴮ x y r))

  private
    match-ext : (x : A) (y : B) (r r′ : Test x y)
      → ((a : A) (p : a <ᴬ x) (b : B) (q : b <ᴮ y)
          → r a p b q ≡ r′ a p b q)
      → (a : A) (b : B) → match x y r a b ≡ match x y r′ a b
    match-ext x y r r′ e a b =
      below-ext P x
        (λ a′ p → below Q y (λ b′ q → r a′ p b′ q) b)
        (λ a′ p → below Q y (λ b′ q → r′ a′ p b′ q) b)
        (λ a′ p → below-ext Q y (λ b′ q → r a′ p b′ q)
          (λ b′ q → r′ a′ p b′ q) (λ b′ q → e a′ p b′ q) b)
        a

  step-ext : (x : A) (y : B) (r r′ : Test x y)
    → ((a : A) (p : a <ᴬ x) (b : B) (q : b <ᴮ y) → r a p b q ≡ r′ a p b q)
    → step x y r ≡ step x y r′
  step-ext x y r r′ e =
    cong₂ _∧_
      (cong not (some-ext P (unmatchedᴬ x y r) (unmatchedᴬ x y r′)
        (below-ext P x
          (λ a _ → not (some Q (match x y r a)))
          (λ a _ → not (some Q (match x y r′ a)))
          (λ a _ → cong not (some-ext Q (match x y r a) (match x y r′ a)
            (match-ext x y r r′ e a))))))
      (cong not (some-ext Q (unmatchedᴮ x y r) (unmatchedᴮ x y r′)
        (below-ext Q y
          (λ b _ → not (some P (λ a → match x y r a b)))
          (λ b _ → not (some P (λ a → match x y r′ a b)))
          (λ b _ → cong not (some-ext P (λ a → match x y r a b)
            (λ a → match x y r′ a b) (λ a → match-ext x y r r′ e a b))))))

  -- The step iterated along accessibility.
  related : (x : A) (y : B) → Acc _<ᴬ_ x → Acc _<ᴮ_ y → Bool
  related x y (acc smallerᴬ) (acc smallerᴮ) =
    step x y (λ a p b q → related a b (smallerᴬ a p) (smallerᴮ b q))

  -- The value does not depend on the accessibility proofs.
  irrelevant : (x : A) (y : B) (α α′ : Acc _<ᴬ_ x) (β β′ : Acc _<ᴮ_ y)
    → related x y α β ≡ related x y α′ β′
  irrelevant x y (acc smallerᴬ) (acc smallerᴬ′) (acc smallerᴮ)
    (acc smallerᴮ′) =
    step-ext x y
      (λ a p b q → related a b (smallerᴬ a p) (smallerᴮ b q))
      (λ a p b q → related a b (smallerᴬ′ a p) (smallerᴮ′ b q))
      (λ a p b q → irrelevant a b (smallerᴬ a p) (smallerᴬ′ a p)
        (smallerᴮ b q) (smallerᴮ′ b q))

  -- Mathematical shape: x ∼ y, the lower cones of x and y matched.
  infix 5 _∼_
  _∼_ : A → B → Bool
  x ∼ y = related x y (wfᴬ x) (wfᴮ y)

  unfold : (x : A) (y : B) → x ∼ y ≡ step x y (λ a _ b _ → a ∼ b)
  unfold x y = at (wfᴬ x) (wfᴮ y)
    where
    at : (α : Acc _<ᴬ_ x) (β : Acc _<ᴮ_ y)
      → related x y α β ≡ step x y (λ a _ b _ → a ∼ b)
    at (acc smallerᴬ) (acc smallerᴮ) =
      step-ext x y
        (λ a p b q → related a b (smallerᴬ a p) (smallerᴮ b q))
        (λ a _ b _ → a ∼ b)
        (λ a p b q → irrelevant a b (smallerᴬ a p) (wfᴬ a)
          (smallerᴮ b q) (wfᴮ b))

  -- A step for a test that ignores the witnesses, read forth.
  step-forth : (x : A) (y : B) (s : A → B → Bool)
    → step x y (λ a _ b _ → s a b) ≡ true
    → (a : A) → a <ᴬ x → Σ B (λ b → b <ᴮ y × s a b ≡ true)
  step-forth x y s e a p =
    let p′ , u = below-at P x (λ a′ _ → not (some Q (match x y r a′))) a p
        b , m = some-true Q (match x y r a)
          (confirm (some Q (match x y r a)) (trans (sym u) none))
        p″ , m′ = below-true P x
          (λ a′ p‴ → below Q y (λ b′ q → r a′ p‴ b′ q) b) a m
        q , t = below-true Q y (λ b′ q → r a p″ b′ q) b m′
    in b , q , t
    where
    r : Test x y
    r a _ b _ = s a b

    none : unmatchedᴬ x y r a ≡ false
    none = some-false P (unmatchedᴬ x y r)
      (refute (some P (unmatchedᴬ x y r))
        (proj₁ (conjuncts (not (some P (unmatchedᴬ x y r)))
          (not (some Q (unmatchedᴮ x y r))) e)))
      a

  -- The same step, read back.
  step-back : (x : A) (y : B) (s : A → B → Bool)
    → step x y (λ a _ b _ → s a b) ≡ true
    → (b : B) → b <ᴮ y → Σ A (λ a → a <ᴬ x × s a b ≡ true)
  step-back x y s e b q =
    let q′ , u = below-at Q y
          (λ b′ _ → not (some P (λ a → match x y r a b′))) b q
        a , m = some-true P (λ a → match x y r a b)
          (confirm (some P (λ a → match x y r a b)) (trans (sym u) none))
        p , m′ = below-true P x
          (λ a′ p′ → below Q y (λ b′ q″ → r a′ p′ b′ q″) b) a m
        q″ , t = below-true Q y (λ b′ q‴ → r a p b′ q‴) b m′
    in a , p , t
    where
    r : Test x y
    r a _ b _ = s a b

    none : unmatchedᴮ x y r b ≡ false
    none = some-false Q (unmatchedᴮ x y r)
      (refute (some Q (unmatchedᴮ x y r))
        (proj₂ (conjuncts (not (some P (unmatchedᴬ x y r)))
          (not (some Q (unmatchedᴮ x y r))) e)))
      b

  -- Partners in both directions make the step true.
  step-intro : (x : A) (y : B) (s : A → B → Bool)
    → ((a : A) → a <ᴬ x → Σ B (λ b → b <ᴮ y × s a b ≡ true))
    → ((b : B) → b <ᴮ y → Σ A (λ a → a <ᴬ x × s a b ≡ true))
    → step x y (λ a _ b _ → s a b) ≡ true
  step-intro x y s partnersᴬ partnersᴮ =
    conjunction
      (cong not (some-none P (unmatchedᴬ x y r)
        (below-false P x (λ a _ → not (some Q (match x y r a)))
          λ a p → let b , q , t = partnersᴬ a p in
            cong not (some-intro Q (match x y r a) b (matched a b p q t)))))
      (cong not (some-none Q (unmatchedᴮ x y r)
        (below-false Q y (λ b _ → not (some P (λ a → match x y r a b)))
          λ b q → let a , p , t = partnersᴮ b q in
            cong not (some-intro P (λ a → match x y r a b) a
              (matched a b p q t)))))
    where
    r : Test x y
    r a _ b _ = s a b

    matched : (a : A) (b : B) → a <ᴬ x → b <ᴮ y → s a b ≡ true
      → match x y r a b ≡ true
    matched a b p q t =
      let p′ , u = below-at P x
            (λ a′ p″ → below Q y (λ b′ q′ → r a′ p″ b′ q′) b) a p
          q′ , v = below-at Q y (λ b′ q″ → r a p′ b′ q″) b q
      in trans u (trans v t)

  -- Mathematical shape: x ∼ y → a < x → ∃ b < y. a ∼ b.
  forth : (x : A) (y : B) → x ∼ y ≡ true
    → (a : A) → a <ᴬ x → Σ B (λ b → b <ᴮ y × a ∼ b ≡ true)
  forth x y e = step-forth x y _∼_ (trans (sym (unfold x y)) e)

  -- Mathematical shape: x ∼ y → b < y → ∃ a < x. a ∼ b.
  back : (x : A) (y : B) → x ∼ y ≡ true
    → (b : B) → b <ᴮ y → Σ A (λ a → a <ᴬ x × a ∼ b ≡ true)
  back x y e = step-back x y _∼_ (trans (sym (unfold x y)) e)

  intro : (x : A) (y : B)
    → ((a : A) → a <ᴬ x → Σ B (λ b → b <ᴮ y × a ∼ b ≡ true))
    → ((b : B) → b <ᴮ y → Σ A (λ a → a <ᴬ x × a ∼ b ≡ true))
    → x ∼ y ≡ true
  intro x y partnersᴬ partnersᴮ =
    trans (unfold x y) (step-intro x y _∼_ partnersᴬ partnersᴮ)

  functional : (x : A) → Acc _<ᴬ_ x → (b b′ : B)
    → x ∼ b ≡ true → x ∼ b′ ≡ true → b ≡ b′
  functional x (acc smaller) b b′ e e′ =
    settle (λ a p → functional a (smaller a p)) (compareᴮ b b′)
    where
    settle : ((a : A) → a <ᴬ x → (c d : B)
        → a ∼ c ≡ true → a ∼ d ≡ true → c ≡ d)
      → b <ᴮ b′ ⊎ (b ≡ b′ ⊎ b′ <ᴮ b) → b ≡ b′
    settle ih (inj₂ (inj₁ same)) = same
    settle ih (inj₁ b<b′) =
      let a , a<x , f = back x b′ e′ b b<b′
          c , c<b , g = forth x b e a a<x
      in ⊥-elim (irreflᴮ b
           (subst (λ z → z <ᴮ b) (ih a a<x c b g f) c<b))
    settle ih (inj₂ (inj₂ b′<b)) =
      let a , a<x , f = back x b e b′ b′<b
          c , c<b′ , g = forth x b′ e′ a a<x
      in ⊥-elim (irreflᴮ b′
           (subst (λ z → z <ᴮ b′) (ih a a<x c b′ g f) c<b′))

  injective : (y : B) → Acc _<ᴮ_ y → (a a′ : A)
    → a ∼ y ≡ true → a′ ∼ y ≡ true → a ≡ a′
  injective y (acc smaller) a a′ e e′ =
    settle (λ b q → injective b (smaller b q)) (compareᴬ a a′)
    where
    settle : ((b : B) → b <ᴮ y → (c d : A)
        → c ∼ b ≡ true → d ∼ b ≡ true → c ≡ d)
      → a <ᴬ a′ ⊎ (a ≡ a′ ⊎ a′ <ᴬ a) → a ≡ a′
    settle ih (inj₂ (inj₁ same)) = same
    settle ih (inj₁ a<a′) =
      let b , b<y , f = forth a′ y e′ a a<a′
          c , c<a , g = back a y e b b<y
      in ⊥-elim (irreflᴬ a
           (subst (λ z → z <ᴬ a) (ih b b<y c a g f) c<a))
    settle ih (inj₂ (inj₂ a′<a)) =
      let b , b<y , f = forth a y e a′ a′<a
          c , c<a′ , g = back a′ y e′ b b<y
      in ⊥-elim (irreflᴬ a′
           (subst (λ z → z <ᴬ a′) (ih b b<y c a′ g f) c<a′))

  preserves : (a a′ : A) (b b′ : B) → a ∼ b ≡ true → a′ ∼ b′ ≡ true
    → a <ᴬ a′ → b <ᴮ b′
  preserves a a′ b b′ e e′ p =
    let c , c<b′ , f = forth a′ b′ e′ a p
    in subst (λ z → z <ᴮ b′) (functional a (wfᴬ a) c b f e) c<b′

  reflects : (a a′ : A) (b b′ : B) → a ∼ b ≡ true → a′ ∼ b′ ≡ true
    → b <ᴮ b′ → a <ᴬ a′
  reflects a a′ b b′ e e′ q =
    let c , c<a′ , f = back a′ b′ e′ b q
    in subst (λ z → z <ᴬ a′) (injective b (wfᴮ b) c a f e) c<a′

  -- Mathematical shape: ∃ b. x ∼ b.
  partner : A → Bool
  partner x = some Q (λ b → x ∼ b)

  -- Mathematical shape: ∃ a. a ∼ y.
  source : B → Bool
  source y = some P (λ a → a ∼ y)

  -- A matched point of Q lies below every point without a source.
  under : (y : B) → source y ≡ false → (a : A) (b : B) → a ∼ b ≡ true
    → b <ᴮ y
  under y none a b e = place (compareᴮ b y)
    where
    place : b <ᴮ y ⊎ (b ≡ y ⊎ y <ᴮ b) → b <ᴮ y
    place (inj₁ q) = q
    place (inj₂ (inj₁ same)) = ⊥-elim (true≢false (trans
      (sym (some-intro P (λ c → c ∼ y) a
        (subst (λ z → a ∼ z ≡ true) same e)))
      none))
    place (inj₂ (inj₂ q)) =
      let c , c<a , f = back a b e y q
      in ⊥-elim (true≢false
           (trans (sym (some-intro P (λ c → c ∼ y) c f)) none))

  -- A matched point of P lies below every point without a partner.
  over : (x : A) → partner x ≡ false → (a : A) (b : B) → a ∼ b ≡ true
    → a <ᴬ x
  over x none a b e = place (compareᴬ a x)
    where
    place : a <ᴬ x ⊎ (a ≡ x ⊎ x <ᴬ a) → a <ᴬ x
    place (inj₁ p) = p
    place (inj₂ (inj₁ same)) = ⊥-elim (true≢false (trans
      (sym (some-intro Q (λ d → x ∼ d) b
        (subst (λ z → z ∼ b ≡ true) same e)))
      none))
    place (inj₂ (inj₂ p)) =
      let d , d<b , f = forth a b e x p
      in ⊥-elim (true≢false
           (trans (sym (some-intro Q (λ d → x ∼ d) d f)) none))

  -- Minimal points without a partner and without a source would be
  -- matched to each other.
  exclusive : (x : A) (y : B)
    → partner x ≡ false → ((a : A) → a <ᴬ x → partner a ≡ true)
    → source y ≡ false → ((b : B) → b <ᴮ y → source b ≡ true)
    → ⊥
  exclusive x y lonelyᴬ pairedᴬ lonelyᴮ pairedᴮ =
    true≢false (trans (sym (some-intro Q (λ b → x ∼ b) y
      (intro x y partnered sourced))) lonelyᴬ)
    where
    partnered : (a : A) → a <ᴬ x → Σ B (λ b → b <ᴮ y × a ∼ b ≡ true)
    partnered a p =
      let b , e = some-true Q (λ b → a ∼ b) (pairedᴬ a p)
      in b , under y lonelyᴮ a b e , e

    sourced : (b : B) → b <ᴮ y → Σ A (λ a → a <ᴬ x × a ∼ b ≡ true)
    sourced b q =
      let a , e = some-true P (λ a → a ∼ b) (pairedᴮ b q)
      in a , over x lonelyᴬ a b e , e

  -- Every point of P has a partner: an initial map P → Q.
  initial : ((x : A) → partner x ≡ true) → Orders.Initial P Q
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
    image x = proj₁ (some-true Q (λ b → x ∼ b) (total x))

    image-matched : (x : A) → x ∼ image x ≡ true
    image-matched x = proj₂ (some-true Q (λ b → x ∼ b) (total x))

  -- A point of P without a partner: the least one is the ceiling of a
  -- proper segment Q → P, since then every point of Q has a source.
  segment : (x : A) → not (partner x) ≡ true → Segment Q P
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
    ceiling = proj₁ least

    lonely : partner ceiling ≡ false
    lonely = refute (partner ceiling) (proj₁ (proj₂ least))

    paired : (a : A) → a <ᴬ ceiling → partner a ≡ true
    paired a p = confirm (partner a) (proj₂ (proj₂ least) a p)

    sourced : (y : B) → source y ≡ true
    sourced y = settle (source y) refl
      where
      settle : (u : Bool) → source y ≡ u → source y ≡ true
      settle true p = p
      settle false p =
        let b , h , k = minimal Q (λ b → not (source b)) y (cong not p)
        in ⊥-elim (exclusive ceiling b lonely paired
             (refute (source b) h)
             (λ b′ q → confirm (source b′) (k b′ q)))

    origin : B → A
    origin y = proj₁ (some-true P (λ a → a ∼ y) (sourced y))

    origin-matched : (y : B) → origin y ∼ y ≡ true
    origin-matched y = proj₂ (some-true P (λ a → a ∼ y) (sourced y))

  -- Mathematical shape: P ≤ Q ⊎ Q < P.
  comparable : Orders.Initial P Q ⊎ Segment Q P
  comparable = settle (some P (λ x → not (partner x))) refl
    where
    settle : (u : Bool) → some P (λ x → not (partner x)) ≡ u
      → Orders.Initial P Q ⊎ Segment Q P
    settle false none = inj₁ (initial λ x →
      confirm (partner x) (some-false P (λ x → not (partner x)) none x))
    settle true found =
      let x , g = some-true P (λ x → not (partner x)) found
      in inj₂ (segment x g)

-- Mathematical shape: LPO → P ≤ Q ⊎ Q < P, for exact orders P and Q.
comparable : LPO → {ℓ : Level} {A B : Set ℓ}
  (P : Order.Order A) (Q : Order.Order B)
  → Orders.Initial P Q ⊎ Segment Q P
comparable lpo P Q = Matching.comparable lpo P Q
