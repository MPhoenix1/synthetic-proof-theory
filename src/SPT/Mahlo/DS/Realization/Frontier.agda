{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Realization.Frontier where

-- Partial paths through a type-valued Dybjer–Setzer description. A path
-- ends at the arity of a σ or δ node or at a completed output, and its
-- value is that type of level ℓ, which names itself (`Path`, `value`). The
-- description of paths has these values as outputs (`paths`, `argument-β`),
-- and `description` joins it to the original one. Moving a path along maps
-- and identities keeps its value (`map-β`, `change-β`, `shift-β`).

open import SPT.Base

open import SPT.IR.Description using
  (Desc; ι; σ; δ; Indexed; indexed; carrier; index; Shape; Mark)

------------------------------------------------------------------------
-- Paths and their values

-- A path either stops at the current node or continues into the
-- continuation selected by its literal arguments. At δ the continuation is
-- selected by the decoded family index ∘ f, as in Shape.

Path :
  {ℓ : Level} → Desc {s = ℓ} (Set ℓ) → Indexed ℓ (Set ℓ) → Set ℓ
Path {ℓ} (ι e) Z = Lift ℓ 𝟙
Path {ℓ} (σ A H) Z = Lift ℓ 𝟙 ⊎ Σ A (λ a → Path (H a) Z)
Path {ℓ} (δ A H) Z =
  Lift ℓ 𝟙 ⊎ Σ (A → carrier Z) (λ f → Path (H (λ a → index Z (f a))) Z)

value :
  {ℓ : Level} (S : Desc {s = ℓ} (Set ℓ)) (Z : Indexed ℓ (Set ℓ))
  → Path S Z → Set ℓ
value (ι e) Z _ = e
value (σ A H) Z (inl _) = A
value (σ A H) Z (inr (a , p)) = value (H a) Z p
value (δ A H) Z (inl _) = A
value (δ A H) Z (inr (f , p)) = value (H (λ a → index Z (f a))) Z p

-- A complete shape ends at its own output.
leaf :
  {ℓ : Level} (S : Desc {s = ℓ} (Set ℓ)) (Z : Indexed ℓ (Set ℓ))
  → Shape S Z → Path S Z
leaf (ι e) Z _ = lift ⋆
leaf (σ A H) Z (a , z) = inr (a , leaf (H a) Z z)
leaf (δ A H) Z (f , z) = inr (f , leaf (H (λ a → index Z (f a))) Z z)

leaf-β :
  {ℓ : Level} (S : Desc {s = ℓ} (Set ℓ)) (Z : Indexed ℓ (Set ℓ))
  (z : Shape S Z) → value S Z (leaf S Z z) ＝ Mark S Z z
leaf-β (ι e) Z _ = refl
leaf-β (σ A H) Z (a , z) = leaf-β (H a) Z z
leaf-β (δ A H) Z (f , z) = leaf-β (H (λ a → index Z (f a))) Z z

------------------------------------------------------------------------
-- Moving a path

-- Along a map of carriers that keeps the decoding, along an identity of
-- decodings, and along an identity of descriptions. Each keeps the value.

map :
  {ℓ : Level} (S : Desc {s = ℓ} (Set ℓ)) {X Y : Set ℓ}
  (v : Y → Set ℓ) (f : X → Y)
  → Path S (indexed X (λ x → v (f x))) → Path S (indexed Y v)
map (ι e) v f p = p
map (σ A H) v f (inl u) = inl u
map (σ A H) v f (inr (a , p)) = inr (a , map (H a) v f p)
map (δ A H) v f (inl u) = inl u
map (δ A H) v f (inr (q , p)) =
  inr ((λ a → f (q a)) , map (H (λ a → v (f (q a)))) v f p)

map-β :
  {ℓ : Level} (S : Desc {s = ℓ} (Set ℓ)) {X Y : Set ℓ}
  (v : Y → Set ℓ) (f : X → Y)
  (p : Path S (indexed X (λ x → v (f x))))
  → value S (indexed Y v) (map S v f p)
    ＝ value S (indexed X (λ x → v (f x))) p
map-β (ι e) v f p = refl
map-β (σ A H) v f (inl u) = refl
map-β (σ A H) v f (inr (a , p)) = map-β (H a) v f p
map-β (δ A H) v f (inl u) = refl
map-β (δ A H) v f (inr (q , p)) = map-β (H (λ a → v (f (q a)))) v f p

change :
  {ℓ : Level} (S : Desc {s = ℓ} (Set ℓ)) {X : Set ℓ}
  {v w : X → Set ℓ} → v ＝ w
  → Path S (indexed X v) → Path S (indexed X w)
change S refl p = p

change-β :
  {ℓ : Level} (S : Desc {s = ℓ} (Set ℓ)) {X : Set ℓ}
  {v w : X → Set ℓ} (e : v ＝ w) (p : Path S (indexed X v))
  → value S (indexed X w) (change S e p) ＝ value S (indexed X v) p
change-β S refl p = refl

shift :
  {ℓ : Level} (Z : Indexed ℓ (Set ℓ))
  {S T : Desc {s = ℓ} (Set ℓ)} → S ＝ T → Path S Z → Path T Z
shift Z refl p = p

shift-β :
  {ℓ : Level} (Z : Indexed ℓ (Set ℓ))
  {S T : Desc {s = ℓ} (Set ℓ)} (e : S ＝ T) (p : Path S Z)
  → value T Z (shift Z e p) ＝ value S Z p
shift-β Z refl p = refl

------------------------------------------------------------------------
-- The description of paths

-- Every node gains a summand that stops there with its arity as output.
-- The frontier description offers the paths and the original shapes.

either :
  {ℓ : Level} → Desc {s = ℓ} (Set ℓ) → Desc {s = ℓ} (Set ℓ)
  → Lift ℓ 𝟚 → Desc {s = ℓ} (Set ℓ)
either S T (lift ₀) = S
either S T (lift ₁) = T

paths : {ℓ : Level} → Desc {s = ℓ} (Set ℓ) → Desc {s = ℓ} (Set ℓ)
paths (ι e) = ι e
paths {ℓ} (σ A H) = σ (Lift ℓ 𝟚) (either (ι A) (σ A (λ a → paths (H a))))
paths {ℓ} (δ A H) = σ (Lift ℓ 𝟚) (either (ι A) (δ A (λ q → paths (H q))))

argument :
  {ℓ : Level} (S : Desc {s = ℓ} (Set ℓ)) (Z : Indexed ℓ (Set ℓ))
  → Path S Z → Shape (paths S) Z
argument (ι e) Z _ = lift ⋆
argument (σ A H) Z (inl _) = lift ₀ , lift ⋆
argument (σ A H) Z (inr (a , p)) = lift ₁ , (a , argument (H a) Z p)
argument (δ A H) Z (inl _) = lift ₀ , lift ⋆
argument (δ A H) Z (inr (q , p)) =
  lift ₁ , (q , argument (H (λ a → index Z (q a))) Z p)

argument-β :
  {ℓ : Level} (S : Desc {s = ℓ} (Set ℓ)) (Z : Indexed ℓ (Set ℓ))
  (p : Path S Z) → Mark (paths S) Z (argument S Z p) ＝ value S Z p
argument-β (ι e) Z _ = refl
argument-β (σ A H) Z (inl _) = refl
argument-β (σ A H) Z (inr (a , p)) = argument-β (H a) Z p
argument-β (δ A H) Z (inl _) = refl
argument-β (δ A H) Z (inr (q , p)) =
  argument-β (H (λ a → index Z (q a))) Z p

description :
  {ℓ : Level} → Desc {s = ℓ} (Set ℓ) → Desc {s = ℓ} (Set ℓ)
description {ℓ} γ = σ (Lift ℓ 𝟚) (either (paths γ) γ)
