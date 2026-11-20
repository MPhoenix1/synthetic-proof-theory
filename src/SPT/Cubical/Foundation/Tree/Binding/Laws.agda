{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Tree.Binding.Laws where

-- Laws of renaming and substitution of binding-signature expressions,
-- specialized from the laws of map and bind on trees. For any signature: a
-- map is the bind of its holes, structurally (`map-bind-rel`), equal trees
-- are related (`equal-related`), and either side of a relation can be
-- rewritten by an identification (`related-by`, `related-to`). Lifted
-- renamings are joins of maps on the split variable (`lift-join`); lifting
-- the identity is the identity and lifting a composite is the composite
-- (`lift-identity`, `lift-compose`). So renaming is functorial
-- (`rename-identity-rel`, `rename-compose-rel`, from `map-cong`,
-- `map-id-rel`, `map-compose-rel`). A variable moved under binders is the
-- shifted variable, by refl, so substituting variables is the identity
-- (`substitute-identity-rel`, from `bind-cong` and `bind-right-unit-rel`),
-- and renaming is substitution of variables (`rename-substitute-rel`). All
-- laws hold as the structural relation TreeRel _＝_, with no
-- extensionality.

open import SPT.Cubical.Base
import SPT.Cubical.Foundation.Tree.LaxTranslation as LaxTranslation
import SPT.Cubical.Foundation.Signature.Sum as Sig
import SPT.Cubical.Foundation.Tree as Tree
import SPT.Cubical.Foundation.Tree.Map as Map
import SPT.Cubical.Foundation.Tree.Relation as Relation
import SPT.Cubical.Foundation.Tree.Substitution as Substitution
import SPT.Cubical.Foundation.Tree.Binding as Binding

------------------------------------------------------------------------
-- Any signature

-- Equal trees are structurally related.
equal-related :
  {ℓj ℓo ℓp ℓx : Level} {Σ : Tree.Signature ℓj ℓo ℓp}
  {X : Tree.Judgment Σ → Set ℓx} {j : Tree.Judgment Σ}
  {t u : Tree.Tree Σ X j} → t ＝ u → Relation.TreeRel _＝_ t u
equal-related {t = t} refl = Relation.rel-refl (λ x → refl) t

-- An equality on either side of a structural relation.
related-by :
  {ℓj ℓo ℓp ℓx ℓy ℓr : Level} {Σ : Tree.Signature ℓj ℓo ℓp}
  {X : Tree.Judgment Σ → Set ℓx} {Y : Tree.Judgment Σ → Set ℓy}
  {R : {j : Tree.Judgment Σ} → X j → Y j → Set ℓr} {j : Tree.Judgment Σ}
  {t t' : Tree.Tree Σ X j} {u : Tree.Tree Σ Y j}
  → t ＝ t' → Relation.TreeRel R t' u → Relation.TreeRel R t u
related-by refl related = related

related-to :
  {ℓj ℓo ℓp ℓx ℓy ℓr : Level} {Σ : Tree.Signature ℓj ℓo ℓp}
  {X : Tree.Judgment Σ → Set ℓx} {Y : Tree.Judgment Σ → Set ℓy}
  {R : {j : Tree.Judgment Σ} → X j → Y j → Set ℓr} {j : Tree.Judgment Σ}
  {t : Tree.Tree Σ X j} {u u' : Tree.Tree Σ Y j}
  → u ＝ u' → Relation.TreeRel R t u' → Relation.TreeRel R t u
related-to refl related = related

-- A map is the bind of its holes, structurally.
map-bind-rel :
  {ℓj ℓo ℓp ℓx ℓy : Level} {Σ : Tree.Signature ℓj ℓo ℓp}
  {X : Tree.Judgment Σ → Set ℓx} {Y : Tree.Judgment Σ → Set ℓy}
  (f : (j : Tree.Judgment Σ) → X j → Y j)
  (g : (j : Tree.Judgment Σ) → X j → Tree.Tree Σ Y j)
  → ((j : Tree.Judgment Σ) (x : X j)
      → Relation.TreeRel _＝_ (Tree.hole (f j x)) (g j x))
  → {j : Tree.Judgment Σ} (t : Tree.Tree Σ X j)
  → Relation.TreeRel _＝_ (Map.map f t) (Substitution.bind g t)
map-bind-rel f g holes (Tree.hole {j} x) = holes j x
map-bind-rel f g holes (Tree.node o child) =
  Relation.node-rel (λ p → map-bind-rel f g holes (child p))

------------------------------------------------------------------------
-- Lifted renamings

-- A lifted renaming is a join of a map on the split variable.
lift-join :
  {n m : ℕ} (d : ℕ) (ρ : Fin n → Fin m) (s : Fin d ⊎ Fin n)
  → cases (λ j → j ↑ˡ m) (λ k → d ↑ʳ ρ k) s
    ＝ join-at d m (⊎-map (λ j → j) ρ s)
lift-join d ρ (inl j) = refl
lift-join d ρ (inr k) = refl

-- Mapping by identities and by composites, on a split variable.
map-identity :
  {d n : ℕ} (s : Fin d ⊎ Fin n) → ⊎-map (λ j → j) (λ k → k) s ＝ s
map-identity (inl j) = refl
map-identity (inr k) = refl

composite-cases :
  {n m l : ℕ} (d : ℕ) (ρ : Fin n → Fin m) (τ : Fin m → Fin l)
  (s : Fin d ⊎ Fin n)
  → cases (λ j → j ↑ˡ l) (λ k → d ↑ʳ τ k) (⊎-map (λ j → j) ρ s)
    ＝ cases (λ j → j ↑ˡ l) (λ k → d ↑ʳ τ (ρ k)) s
composite-cases d ρ τ (inl j) = refl
composite-cases d ρ τ (inr k) = refl

module _ {ℓo ℓp : Level} (B : Binding.Binding ℓo ℓp) where

  lift-identity :
    {n : ℕ} (d : ℕ) (i : Fin (d + n))
    → Binding.lift B d (λ k → k) i ＝ i
  lift-identity {n} d i =
    lift-join d (λ k → k) (split-at d n i) ∙
      (ap (join-at d n) (map-identity (split-at d n i)) ∙
        join-at-split-at d n i)

  lift-compose :
    {n m l : ℕ} (d : ℕ) (ρ : Fin n → Fin m) (τ : Fin m → Fin l)
    (i : Fin (d + n))
    → Binding.lift B d τ (Binding.lift B d ρ i)
      ＝ Binding.lift B d (λ k → τ (ρ k)) i
  lift-compose {n} {m} {l} d ρ τ i =
    ap (Binding.lift B d τ) (lift-join d ρ (split-at d n i)) ∙
      (ap (cases (λ j → j ↑ˡ l) (λ k → d ↑ʳ τ k))
          (split-at-join-at d m (⊎-map (λ j → j) ρ (split-at d n i))) ∙
        composite-cases d ρ τ (split-at d n i))

  ----------------------------------------------------------------------
  -- Renaming is functorial

  rename-identity-rel :
    {n : ℕ} (e : Binding.Expression B n)
    → Relation.TreeRel _＝_ (Binding.rename B (λ i → i) e) e
  rename-identity-rel e =
    Relation.rel-compose (λ p q → p ∙ q)
      (Relation.map-cong
        (λ d i → Binding.lift B d (λ k → k) i) (λ d i → i)
        (λ {d} {x} p → lift-identity d x ∙ p)
        (Relation.rel-refl (λ x → refl) e))
      (Relation.map-id-rel e)

  rename-compose-rel :
    {n m l : ℕ} (ρ : Fin n → Fin m) (τ : Fin m → Fin l)
    (e : Binding.Expression B n)
    → Relation.TreeRel _＝_
        (Binding.rename B τ (Binding.rename B ρ e))
        (Binding.rename B (λ k → τ (ρ k)) e)
  rename-compose-rel ρ τ e =
    Relation.rel-compose (λ p q → p ∙ q)
      (Relation.map-compose-rel
        (λ d i → Binding.lift B d ρ i) (λ d i → Binding.lift B d τ i) e)
      (Relation.map-cong
        (λ d i → Binding.lift B d τ (Binding.lift B d ρ i))
        (λ d i → Binding.lift B d (λ k → τ (ρ k)) i)
        (λ {d} {x} p →
          lift-compose d ρ τ x ∙
            ap (Binding.lift B d (λ k → τ (ρ k))) p)
        (Relation.rel-refl (λ x → refl) e))

  ----------------------------------------------------------------------
  -- Substituting variables

  -- The replacement of a variable by itself, on a split variable.
  identity-cases :
    {n : ℕ} (d : ℕ) (s : Fin d ⊎ Fin n)
    → cases (λ j → Tree.hole (j ↑ˡ n))
        (λ k → Binding.under B n d (Tree.hole k)) s
      ＝ Tree.hole (join-at d n s)
  identity-cases d (inl j) = refl
  identity-cases d (inr k) = refl

  substitute-identity-rel :
    {n : ℕ} (e : Binding.Expression B n)
    → Relation.TreeRel _＝_ (Binding.substitute B n (λ i → Tree.hole i) e) e
  substitute-identity-rel {n} e =
    Relation.rel-compose (λ p q → p ∙ q)
      (Substitution.bind-cong
        (Binding.replacement B n (λ i → Tree.hole i))
        (λ d i → Tree.hole i)
        (λ {d} {x} {y} p →
          equal-related
            (identity-cases d (split-at d n x) ∙
              ap Tree.hole (join-at-split-at d n x ∙ p)))
        (Relation.rel-refl (λ x → refl) e))
      (Substitution.bind-right-unit-rel e)

  -- Renaming a variable, against substituting its renamed variable.
  renaming-cases :
    {n m : ℕ} (d : ℕ) (ρ : Fin n → Fin m) (s : Fin d ⊎ Fin n)
    → Tree.hole (cases (λ j → j ↑ˡ m) (λ k → d ↑ʳ ρ k) s)
      ＝ cases (λ j → Tree.hole (j ↑ˡ m))
          (λ k → Binding.under B m d (Tree.hole (ρ k))) s
  renaming-cases d ρ (inl j) = refl
  renaming-cases d ρ (inr k) = refl

  rename-substitute-rel :
    {n m : ℕ} (ρ : Fin n → Fin m) (e : Binding.Expression B n)
    → Relation.TreeRel _＝_
        (Binding.rename B ρ e)
        (Binding.substitute B m (λ i → Tree.hole (ρ i)) e)
  rename-substitute-rel {n} {m} ρ e =
    map-bind-rel
      (λ d i → Binding.lift B d ρ i)
      (Binding.replacement B m (λ i → Tree.hole (ρ i)))
      (λ d i → equal-related (renaming-cases d ρ (split-at d n i)))
      e
