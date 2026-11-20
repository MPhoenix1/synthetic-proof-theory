{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Vectors.Tabulation where

-- A function on the positions below n is the vector of its values
-- (`tabulate`), and maps of vectors act entrywise (`vector-map`).
-- Tabulating and reading entries are inverse,
--
--   vector-lookup (tabulate f) i ＝ f i,   tabulate (vector-lookup xs) ＝ xs,
--
-- tabulation respects pointwise identifications (`tabulate-cong`) and
-- takes composites to maps (`tabulate-∘`). A map reads entrywise
-- (`lookup-vector-map`), respects pointwise identifications
-- (`vector-map-cong`), and is functorial (`vector-map-∘`,
-- `vector-map-id`).

open import SPT.Cubical.Base

------------------------------------------------------------------------
-- Tabulation

module _ {ℓ : Level} {A : Set ℓ} where

  tabulate : {n : ℕ} → (Fin n → A) → Vec A n
  tabulate {zero} f = []
  tabulate {suc n} f = f fzero ∷ tabulate (λ i → f (fsuc i))

  lookup-tabulate : {n : ℕ} (f : Fin n → A) (i : Fin n) →
    vector-lookup (tabulate f) i ＝ f i
  lookup-tabulate f fzero = refl
  lookup-tabulate f (fsuc i) = lookup-tabulate (λ j → f (fsuc j)) i

  tabulate-lookup : {n : ℕ} (xs : Vec A n) → tabulate (vector-lookup xs) ＝ xs
  tabulate-lookup [] = refl
  tabulate-lookup (x ∷ xs) = ap (λ ys → x ∷ ys) (tabulate-lookup xs)

  tabulate-cong : {n : ℕ} {f g : Fin n → A} → ((i : Fin n) → f i ＝ g i) →
    tabulate f ＝ tabulate g
  tabulate-cong {zero} e = refl
  tabulate-cong {suc n} e =
    ap₂ (λ y ys → y ∷ ys) (e fzero) (tabulate-cong (λ i → e (fsuc i)))

------------------------------------------------------------------------
-- Maps of vectors

module _ {ℓ κ : Level} {A : Set ℓ} {B : Set κ} where

  vector-map : {n : ℕ} → (A → B) → Vec A n → Vec B n
  vector-map f [] = []
  vector-map f (x ∷ xs) = f x ∷ vector-map f xs

  tabulate-∘ : {n : ℕ} (f : A → B) (g : Fin n → A) →
    tabulate (f ∘ g) ＝ vector-map f (tabulate g)
  tabulate-∘ {zero} f g = refl
  tabulate-∘ {suc n} f g =
    ap (λ ys → f (g fzero) ∷ ys) (tabulate-∘ f (λ i → g (fsuc i)))

  lookup-vector-map : {n : ℕ} (i : Fin n) (f : A → B) (xs : Vec A n) →
    vector-lookup (vector-map f xs) i ＝ f (vector-lookup xs i)
  lookup-vector-map fzero f (x ∷ xs) = refl
  lookup-vector-map (fsuc i) f (x ∷ xs) = lookup-vector-map i f xs

  vector-map-cong : {n : ℕ} {f g : A → B} → ((x : A) → f x ＝ g x) →
    (xs : Vec A n) → vector-map f xs ＝ vector-map g xs
  vector-map-cong e [] = refl
  vector-map-cong e (x ∷ xs) =
    ap₂ (λ y ys → y ∷ ys) (e x) (vector-map-cong e xs)

module _ {ℓ κ μ : Level} {A : Set ℓ} {B : Set κ} {C : Set μ} where

  vector-map-∘ : {n : ℕ} (f : B → C) (g : A → B) (xs : Vec A n) →
    vector-map (f ∘ g) xs ＝ vector-map f (vector-map g xs)
  vector-map-∘ f g [] = refl
  vector-map-∘ f g (x ∷ xs) = ap (λ ys → f (g x) ∷ ys) (vector-map-∘ f g xs)

module _ {ℓ : Level} {A : Set ℓ} where

  vector-map-id : {n : ℕ} (xs : Vec A n) → vector-map id xs ＝ xs
  vector-map-id [] = refl
  vector-map-id (x ∷ xs) = ap (λ ys → x ∷ ys) (vector-map-id xs)
