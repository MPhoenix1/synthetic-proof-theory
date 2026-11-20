{-# OPTIONS --safe --without-K #-}

module SPT.Mahlo.DS.Sorted.Frontier where

-- Partial paths through a description with outputs in Sort ℓ O. A path
-- ends at the arity of a σ or δ node, valued by that type as a name, or at
-- a completed output (`Path`, `value`). The description of paths has these
-- values as outputs (`paths`, `argument-β`), and `description` joins it to
-- the original one. Moving a path along maps and identities keeps its
-- value (`map-β`, `change-β`, `shift-β`). A copy of
-- Realization.Frontier for the two-sorted family, with
-- arities valued by inl; the ambient modules are kept as they are, so
-- that their closed descriptions still decode by conversion.

open import SPT.Base

open import SPT.IR.Description using
  (Desc; ι; σ; δ; Indexed; indexed; carrier; index; Shape; Mark)
open import SPT.Mahlo.DS.Sorted using (Sort)

module _ {ℓ κ : Level} {O : Set κ} where

  ----------------------------------------------------------------------
  -- Paths and their values

  Path : Desc {s = ℓ} (Sort ℓ O) → Indexed ℓ (Sort ℓ O) → Set ℓ
  Path (ι e) Z = Lift ℓ 𝟙
  Path (σ A H) Z = Lift ℓ 𝟙 ⊎ Σ A (λ a → Path (H a) Z)
  Path (δ A H) Z =
    Lift ℓ 𝟙 ⊎ Σ (A → carrier Z) (λ f → Path (H (λ a → index Z (f a))) Z)

  value :
    (S : Desc {s = ℓ} (Sort ℓ O)) (Z : Indexed ℓ (Sort ℓ O))
    → Path S Z → Sort ℓ O
  value (ι e) Z _ = e
  value (σ A H) Z (inl _) = inl A
  value (σ A H) Z (inr (a , p)) = value (H a) Z p
  value (δ A H) Z (inl _) = inl A
  value (δ A H) Z (inr (f , p)) = value (H (λ a → index Z (f a))) Z p

  -- A complete shape ends at its own output.
  leaf :
    (S : Desc {s = ℓ} (Sort ℓ O)) (Z : Indexed ℓ (Sort ℓ O))
    → Shape S Z → Path S Z
  leaf (ι e) Z _ = lift ⋆
  leaf (σ A H) Z (a , z) = inr (a , leaf (H a) Z z)
  leaf (δ A H) Z (f , z) = inr (f , leaf (H (λ a → index Z (f a))) Z z)

  leaf-β :
    (S : Desc {s = ℓ} (Sort ℓ O)) (Z : Indexed ℓ (Sort ℓ O))
    (z : Shape S Z) → value S Z (leaf S Z z) ＝ Mark S Z z
  leaf-β (ι e) Z _ = refl
  leaf-β (σ A H) Z (a , z) = leaf-β (H a) Z z
  leaf-β (δ A H) Z (f , z) = leaf-β (H (λ a → index Z (f a))) Z z

  ----------------------------------------------------------------------
  -- Moving a path

  map :
    (S : Desc {s = ℓ} (Sort ℓ O)) {X Y : Set ℓ}
    (v : Y → Sort ℓ O) (f : X → Y)
    → Path S (indexed X (λ x → v (f x))) → Path S (indexed Y v)
  map (ι e) v f p = p
  map (σ A H) v f (inl u) = inl u
  map (σ A H) v f (inr (a , p)) = inr (a , map (H a) v f p)
  map (δ A H) v f (inl u) = inl u
  map (δ A H) v f (inr (q , p)) =
    inr ((λ a → f (q a)) , map (H (λ a → v (f (q a)))) v f p)

  map-β :
    (S : Desc {s = ℓ} (Sort ℓ O)) {X Y : Set ℓ}
    (v : Y → Sort ℓ O) (f : X → Y)
    (p : Path S (indexed X (λ x → v (f x))))
    → value S (indexed Y v) (map S v f p)
      ＝ value S (indexed X (λ x → v (f x))) p
  map-β (ι e) v f p = refl
  map-β (σ A H) v f (inl u) = refl
  map-β (σ A H) v f (inr (a , p)) = map-β (H a) v f p
  map-β (δ A H) v f (inl u) = refl
  map-β (δ A H) v f (inr (q , p)) = map-β (H (λ a → v (f (q a)))) v f p

  change :
    (S : Desc {s = ℓ} (Sort ℓ O)) {X : Set ℓ} {v w : X → Sort ℓ O}
    → v ＝ w → Path S (indexed X v) → Path S (indexed X w)
  change S refl p = p

  change-β :
    (S : Desc {s = ℓ} (Sort ℓ O)) {X : Set ℓ} {v w : X → Sort ℓ O}
    (e : v ＝ w) (p : Path S (indexed X v))
    → value S (indexed X w) (change S e p) ＝ value S (indexed X v) p
  change-β S refl p = refl

  shift :
    (Z : Indexed ℓ (Sort ℓ O)) {S T : Desc {s = ℓ} (Sort ℓ O)}
    → S ＝ T → Path S Z → Path T Z
  shift Z refl p = p

  shift-β :
    (Z : Indexed ℓ (Sort ℓ O)) {S T : Desc {s = ℓ} (Sort ℓ O)}
    (e : S ＝ T) (p : Path S Z) → value T Z (shift Z e p) ＝ value S Z p
  shift-β Z refl p = refl

  ----------------------------------------------------------------------
  -- The description of paths

  either :
    Desc {s = ℓ} (Sort ℓ O) → Desc {s = ℓ} (Sort ℓ O) → Lift ℓ 𝟚
    → Desc {s = ℓ} (Sort ℓ O)
  either S T (lift ₀) = S
  either S T (lift ₁) = T

  paths : Desc {s = ℓ} (Sort ℓ O) → Desc {s = ℓ} (Sort ℓ O)
  paths (ι e) = ι e
  paths (σ A H) =
    σ (Lift ℓ 𝟚) (either (ι (inl A)) (σ A (λ a → paths (H a))))
  paths (δ A H) =
    σ (Lift ℓ 𝟚) (either (ι (inl A)) (δ A (λ q → paths (H q))))

  argument :
    (S : Desc {s = ℓ} (Sort ℓ O)) (Z : Indexed ℓ (Sort ℓ O))
    → Path S Z → Shape (paths S) Z
  argument (ι e) Z _ = lift ⋆
  argument (σ A H) Z (inl _) = lift ₀ , lift ⋆
  argument (σ A H) Z (inr (a , p)) = lift ₁ , (a , argument (H a) Z p)
  argument (δ A H) Z (inl _) = lift ₀ , lift ⋆
  argument (δ A H) Z (inr (q , p)) =
    lift ₁ , (q , argument (H (λ a → index Z (q a))) Z p)

  argument-β :
    (S : Desc {s = ℓ} (Sort ℓ O)) (Z : Indexed ℓ (Sort ℓ O))
    (p : Path S Z) → Mark (paths S) Z (argument S Z p) ＝ value S Z p
  argument-β (ι e) Z _ = refl
  argument-β (σ A H) Z (inl _) = refl
  argument-β (σ A H) Z (inr (a , p)) = argument-β (H a) Z p
  argument-β (δ A H) Z (inl _) = refl
  argument-β (δ A H) Z (inr (q , p)) =
    argument-β (H (λ a → index Z (q a))) Z p

  description : Desc {s = ℓ} (Sort ℓ O) → Desc {s = ℓ} (Sort ℓ O)
  description γ = σ (Lift ℓ 𝟚) (either (paths γ) γ)
