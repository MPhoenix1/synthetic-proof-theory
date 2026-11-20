{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module SPT.Cubical.Foundation.Tree.Binding.Lifting where

-- Substitutions lifted over binders, and the premises of binders under
-- substitution. A substitution lifted over d binders keeps the d bound
-- variables and replaces the others by their expressions weakened past the
-- binders (`lifted`). Reading a premise under its d binders commutes with
-- substitution, the premise taking the lifted substitution
-- (`bound-substitute-rel`, `bound-substituted`). The proof is the induction
-- of Composition's `under-substitute-rel` with `bound` in place of `under`:
-- at nodes through LaxTranslation.Functoriality's `bind-transport` and
-- `tree-rel-equality-transport`; at a variable bound inside the premise or
-- by its binders both sides are the same variable, by the numbers of
-- `rebound` (`inner-case`, `binder-case`); at a free variable its
-- expression is moved under all the binders at once on one side, and on the
-- other weakened past the premise's binders, moved under the inner ones and
-- read under the premise's (`free-case`). These agree by Moving's
-- `moving-compose-rel`, since moving under binders commutes with renaming
-- (`under-rename-rel`, from Laws' `map-bind-rel` and Composition's
-- `under-substitute-rel`) and reading a weakened tree under binders is
-- moving it under them (`bound-weakened-rel`, `moved-weakened-rel`). For
-- any signature, every tree is related to itself (`identical`), and lax
-- translation keeps the structural relation and fuses with map, which is no
-- lax translation (`lax-related`, `lax-map-rel`). Further: renaming,
-- reading under binders and substitution keep the relation
-- (`rename-related`, `bound-related`, `substitute-related`); moving under
-- no binders is the identity (`under-zero-rel`); pointwise related
-- substitutions give related results (`substitute-pointwise-rel`); lifting
-- twice over one binder is lifting over two (`lifted-twice`); and the
-- lifted substitution takes a weakened expression to the weakened
-- substituted one (`weaken-substituted`). All as TreeRel _＝_, with no
-- extensionality.

open import SPT.Cubical.Base
open import SPT.Cubical.Foundation.Nat.Identifications using
  (ℕ-identifications-agree)
import SPT.Cubical.Foundation.Signature.Sum as Sig
import SPT.Cubical.Foundation.Signature.LaxTranslation as Lax
import SPT.Cubical.Foundation.Tree as Tree
import SPT.Cubical.Foundation.Tree.LaxTranslation as LaxTree
import SPT.Cubical.Foundation.Tree.LaxTranslation.Functoriality as Functoriality
import SPT.Cubical.Foundation.Tree.Map as Map
import SPT.Cubical.Foundation.Tree.Relation as Relation
import SPT.Cubical.Foundation.Tree.Substitution as Substitution
import SPT.Cubical.Foundation.Tree.Binding as Binding
import SPT.Cubical.Foundation.Tree.Binding.Composition as Composition
import SPT.Cubical.Foundation.Tree.Binding.Laws as Laws
import SPT.Cubical.Foundation.Tree.Binding.Moving as Moving
import SPT.Cubical.Foundation.Tree.Binding.Shift as Shift
import SPT.Cubical.Foundation.Tree.Binding.Transport as Transport

------------------------------------------------------------------------
-- Any signature

-- Every tree is related to itself.
identical :
  {ℓj ℓo ℓp ℓx : Level} {Σ : Tree.Signature ℓj ℓo ℓp}
  {X : Tree.Judgment Σ → Set ℓx} {j : Tree.Judgment Σ}
  (t : Tree.Tree Σ X j) → Relation.TreeRel _＝_ t t
identical t = Relation.rel-refl (λ x → refl) t

-- Lax translation keeps the structural relation.
lax-related :
  {ℓj₁ ℓo₁ ℓp₁ ℓj₂ ℓo₂ ℓp₂ ℓx ℓy : Level}
  {SourceJudgment : Set ℓj₁} {TargetJudgment : Set ℓj₂}
  {on-judgment : SourceJudgment → TargetJudgment}
  {source : Sig.Signature-Over SourceJudgment ℓo₁ ℓp₁}
  {target : Sig.Signature-Over TargetJudgment ℓo₂ ℓp₂}
  (translation : Lax.Lax-Signature-Translation on-judgment source target)
  {X : SourceJudgment → Set ℓx} (Y : TargetJudgment → Set ℓy)
  (on-hole : (j : SourceJudgment) → X j → Y (on-judgment j))
  {j : SourceJudgment} {t u : Tree.Tree (Sig.to-signature source) X j}
  → Relation.TreeRel _＝_ t u
  → Relation.TreeRel _＝_
      (LaxTree.map-lax-tree translation Y on-hole t)
      (LaxTree.map-lax-tree translation Y on-hole u)
lax-related translation Y on-hole (Relation.hole-rel refl) =
  Relation.hole-rel refl
lax-related translation Y on-hole (Relation.node-rel {o = o} related) =
  Relation.node-rel
    (λ q →
      Functoriality.tree-rel-equality-transport
        (Lax.lax-boundary-coherence translation o q)
        (lax-related translation Y on-hole
          (related (Lax.project-lax-position translation o q))))

-- Lax translation after map is the lax translation of the
-- composite hole action.
lax-map-rel :
  {ℓj₁ ℓo₁ ℓp₁ ℓj₂ ℓo₂ ℓp₂ ℓx ℓy ℓz : Level}
  {SourceJudgment : Set ℓj₁} {TargetJudgment : Set ℓj₂}
  {on-judgment : SourceJudgment → TargetJudgment}
  {source : Sig.Signature-Over SourceJudgment ℓo₁ ℓp₁}
  {target : Sig.Signature-Over TargetJudgment ℓo₂ ℓp₂}
  (translation : Lax.Lax-Signature-Translation on-judgment source target)
  {X : SourceJudgment → Set ℓx} {Y : SourceJudgment → Set ℓy}
  (Z : TargetJudgment → Set ℓz)
  (f : (j : SourceJudgment) → X j → Y j)
  (on-hole : (j : SourceJudgment) → Y j → Z (on-judgment j))
  {j : SourceJudgment} (t : Tree.Tree (Sig.to-signature source) X j)
  → Relation.TreeRel _＝_
      (LaxTree.map-lax-tree translation Z on-hole
        (Map.map f t))
      (LaxTree.map-lax-tree translation Z
        (λ i x → on-hole i (f i x)) t)
lax-map-rel translation Z f on-hole (Tree.hole x) = Relation.hole-rel refl
lax-map-rel translation Z f on-hole (Tree.node o child) =
  Relation.node-rel
    (λ q →
      Functoriality.tree-rel-equality-transport
        (Lax.lax-boundary-coherence translation o q)
        (lax-map-rel translation Z f on-hole
          (child (Lax.project-lax-position translation o q))))

-- Shifting past no binders keeps every number.
shifted-zero : (c x : ℕ) → Shift.shifted c 0 x ＝ x
shifted-zero c x =
  cases (Shift.shifted-below 0) (Shift.shifted-above 0) (Shift.decide x c)

------------------------------------------------------------------------
-- Binding signatures

module _ {ℓo ℓp : Level} (B : Binding.Binding ℓo ℓp) where

  open Binding.Binding B

  -- σ lifted over d binders: the d bound variables stay, and the others
  -- are replaced by their expressions weakened past the binders.
  lifted :
    {n : ℕ} (m d : ℕ) → (Fin n → Binding.Expression B m) → Fin (d + n)
    → Binding.Expression B (d + m)
  lifted {n} m d σ i =
    cases (λ j → Tree.hole (j ↑ˡ m))
      (λ k → Binding.rename B (λ y → d ↑ʳ y) (σ k)) (split-at d n i)

  ----------------------------------------------------------------------
  -- Keeping the structural relation

  rename-related :
    {n m : ℕ} (ρ : Fin n → Fin m) {e e′ : Binding.Expression B n}
    → Relation.TreeRel _＝_ e e′
    → Relation.TreeRel _＝_
        (Binding.rename B ρ e) (Binding.rename B ρ e′)
  rename-related ρ related =
    Relation.map-cong
      (λ d i → Binding.lift B d ρ i) (λ d i → Binding.lift B d ρ i)
      (λ {d} q → ap (λ i → Binding.lift B d ρ i) q) related

  bound-related :
    (m d : ℕ) {e e′ : Binding.Expression B (d + m)}
    → Relation.TreeRel _＝_ e e′
    → Relation.TreeRel _＝_
        (Binding.bound B m d e) (Binding.bound B m d e′)
  bound-related m d related =
    lax-related (Binding.shift B d) (Binding.Variable m)
      (Binding.rebound B m d) related

  substitute-related :
    {n : ℕ} (m : ℕ) (σ : Fin n → Binding.Expression B m)
    {e e′ : Binding.Expression B n}
    → Relation.TreeRel _＝_ e e′
    → Relation.TreeRel _＝_
        (Binding.substitute B m σ e) (Binding.substitute B m σ e′)
  substitute-related m σ related =
    Substitution.bind-cong (Binding.replacement B m σ)
      (Binding.replacement B m σ)
      (λ {c} {x} {y} q →
        Laws.equal-related (ap (Binding.replacement B m σ c) q))
      related

  ----------------------------------------------------------------------
  -- The numbers of variables read under binders

  -- Reading under binders keeps every number.
  to-ℕ-rebound :
    (m d c : ℕ) (x : Binding.Variable (d + m) c)
    → to-ℕ (Binding.rebound B m d c x) ＝ to-ℕ x
  to-ℕ-rebound m d c x = Shift.to-ℕ-transport (λ j → j) (+-assoc c d m ⁻¹) x

  -- A variable bound inside the premise.
  rebound-inner :
    (m d c : ℕ) (j : Fin c)
    → Binding.rebound B m d c (j ↑ˡ (d + m)) ＝ (j ↑ˡ d) ↑ˡ m
  rebound-inner m d c j =
    to-ℕ-is-injective
      (to-ℕ-rebound m d c (j ↑ˡ (d + m)) ∙
        (to-ℕ-↑ˡ j (d + m) ∙
          (to-ℕ-↑ˡ (j ↑ˡ d) m ∙ to-ℕ-↑ˡ j d) ⁻¹))

  -- A variable bound by the premise's binders.
  rebound-binder :
    (m d c : ℕ) (i : Fin d)
    → Binding.rebound B m d c (c ↑ʳ (i ↑ˡ m)) ＝ (c ↑ʳ i) ↑ˡ m
  rebound-binder m d c i =
    to-ℕ-is-injective
      (to-ℕ-rebound m d c (c ↑ʳ (i ↑ˡ m)) ∙
        (to-ℕ-↑ʳ c (i ↑ˡ m) ∙
          (ap (λ x → c + x) (to-ℕ-↑ˡ i m) ∙
            (to-ℕ-↑ˡ (c ↑ʳ i) m ∙ to-ℕ-↑ʳ c i) ⁻¹)))

  -- A free variable.
  rebound-free :
    (m d c : ℕ) (k : Fin m)
    → Binding.rebound B m d c (c ↑ʳ (d ↑ʳ k)) ＝ (c + d) ↑ʳ k
  rebound-free m d c k =
    to-ℕ-is-injective
      (to-ℕ-rebound m d c (c ↑ʳ (d ↑ʳ k)) ∙
        (to-ℕ-↑ʳ c (d ↑ʳ k) ∙
          (ap (λ x → c + x) (to-ℕ-↑ʳ d k) ∙
            (+-assoc c d (to-ℕ k) ⁻¹ ∙
              to-ℕ-↑ʳ (c + d) k ⁻¹))))

  ----------------------------------------------------------------------
  -- Moving, renaming and reading under binders

  -- Moving under binders commutes with renaming.
  under-rename-rel :
    {m l : ℕ} (ρ : Fin m → Fin l) (c : ℕ) (s : Binding.Expression B m)
    → Relation.TreeRel _＝_
        (Binding.under B l c (Binding.rename B ρ s))
        (Map.map (λ c′ i → Binding.lift B c′ ρ i)
          (Binding.under B m c s))
  under-rename-rel {m} {l} ρ c s =
    Relation.rel-compose _∙_
      (lax-related (Binding.shift B c) (Binding.Variable l)
        (Binding.moved B l c) (Laws.rename-substitute-rel B ρ s))
      (Relation.rel-compose _∙_
        (Relation.rel-sym _⁻¹
          (Composition.under-substitute-rel B (λ i → Tree.hole (ρ i)) c s))
        (Relation.rel-sym _⁻¹
          (Laws.map-bind-rel (λ c′ i → Binding.lift B c′ ρ i)
            (Binding.replacement B l (λ i → Tree.hole (ρ i)))
            (λ c′ i →
              Laws.equal-related
                (Laws.renaming-cases B c′ ρ (split-at c′ m i)))
            (Binding.under B m c s))))

  -- Reading a tree weakened past d variables under d binders is moving it
  -- under them.
  bound-weakened-rel :
    (m d : ℕ) {c : ℕ}
      (u : Tree.Tree (Sig.to-signature (Binding.over B)) (Binding.Variable m) c)
    → Relation.TreeRel _＝_
        (LaxTree.map-lax-tree (Binding.shift B d) (Binding.Variable m)
          (Binding.rebound B m d)
          (Map.map (λ c′ i → Binding.lift B c′ (λ y → d ↑ʳ y) i)
            u))
        (LaxTree.map-lax-tree (Binding.shift B d) (Binding.Variable m)
          (Binding.moved B m d) u)
  bound-weakened-rel m d u =
    lax-map-rel (Binding.shift B d) (Binding.Variable m)
      (λ c′ i → Binding.lift B c′ (λ y → d ↑ʳ y) i)
      (Binding.rebound B m d) u

  -- An expression moved under c + d binders at once, and weakened past d
  -- variables, moved under c binders and read under d.
  moved-weakened-rel :
    (m d c : ℕ) (s : Binding.Expression B m)
    → Relation.TreeRel _＝_
        (Binding.under B m (c + d) s)
        (LaxTree.map-lax-tree (Binding.shift B d) (Binding.Variable m)
          (Binding.rebound B m d)
          (Binding.under B (d + m) c (Binding.rename B (λ y → d ↑ʳ y) s)))
  moved-weakened-rel m d c s =
    Relation.rel-compose _∙_
      (Relation.rel-sym _⁻¹ (Moving.moving-compose-rel B c d s))
      (Relation.rel-compose _∙_
        (Relation.rel-sym _⁻¹
          (bound-weakened-rel m d (Binding.under B m c s)))
        (lax-related (Binding.shift B d) (Binding.Variable m)
          (Binding.rebound B m d)
          (Relation.rel-sym _⁻¹
            (under-rename-rel (λ y → d ↑ʳ y) c s))))

  ----------------------------------------------------------------------
  -- Reading a premise under its binders commutes with substitution

  -- A variable bound inside the premise: the same variable on both sides.
  inner-case :
    {n : ℕ} (m : ℕ) (σ : Fin n → Binding.Expression B m) (d c : ℕ)
    (j : Fin c)
    → Binding.replacement B m σ (c + d)
        (Binding.rebound B n d c (j ↑ˡ (d + n)))
      ＝ LaxTree.map-lax-tree (Binding.shift B d) (Binding.Variable m)
        (Binding.rebound B m d)
          (Binding.replacement B (d + m) (lifted m d σ) c (j ↑ˡ (d + n)))
  inner-case {n} m σ d c j =
    ap (Binding.replacement B m σ (c + d)) (rebound-inner n d c j) ∙
      (ap
          (cases (λ i → Tree.hole (i ↑ˡ m))
            (λ k → Binding.under B m (c + d) (σ k)))
          (split-at-↑ˡ (c + d) (j ↑ˡ d) n) ∙
        (ap
              (LaxTree.map-lax-tree (Binding.shift B d)
                (Binding.Variable m)
                (Binding.rebound B m d))
              (ap
                (cases (λ i → Tree.hole (i ↑ˡ (d + m)))
                  (λ k → Binding.under B (d + m) c (lifted m d σ k)))
                (split-at-↑ˡ c j (d + n))) ∙
            ap Tree.hole (rebound-inner m d c j)) ⁻¹)

  -- A variable bound by the premise's binders: the same variable.
  binder-case :
    {n : ℕ} (m : ℕ) (σ : Fin n → Binding.Expression B m) (d c : ℕ)
    (i : Fin d)
    → Binding.replacement B m σ (c + d)
        (Binding.rebound B n d c (c ↑ʳ (i ↑ˡ n)))
      ＝ LaxTree.map-lax-tree (Binding.shift B d) (Binding.Variable m)
        (Binding.rebound B m d)
          (Binding.replacement B (d + m) (lifted m d σ) c
            (c ↑ʳ (i ↑ˡ n)))
  binder-case {n} m σ d c i =
    ap (Binding.replacement B m σ (c + d)) (rebound-binder n d c i) ∙
      (ap
          (cases (λ j → Tree.hole (j ↑ˡ m))
            (λ k → Binding.under B m (c + d) (σ k)))
          (split-at-↑ˡ (c + d) (c ↑ʳ i) n) ∙
        (ap
              (LaxTree.map-lax-tree (Binding.shift B d)
                (Binding.Variable m)
                (Binding.rebound B m d))
              (ap
                (cases (λ j → Tree.hole (j ↑ˡ (d + m)))
                  (λ k → Binding.under B (d + m) c (lifted m d σ k)))
                (split-at-↑ʳ c (d + n) (i ↑ˡ n))) ∙
            (ap
                (λ y →
                  LaxTree.map-lax-tree (Binding.shift B d)
                    (Binding.Variable m)
                    (Binding.rebound B m d) (Binding.under B (d + m) c y))
                (ap
                  (cases (λ j → Tree.hole (j ↑ˡ m))
                    (λ k → Binding.rename B (λ y → d ↑ʳ y) (σ k)))
                  (split-at-↑ˡ d i n)) ∙
              ap Tree.hole (rebound-binder m d c i))) ⁻¹)

  -- A free variable: its expression moved under all the binders at once,
  -- or weakened, moved under the inner binders and read under the
  -- premise's.
  free-case :
    {n : ℕ} (m : ℕ) (σ : Fin n → Binding.Expression B m) (d c : ℕ)
    (k : Fin n)
    → Relation.TreeRel _＝_
        (Binding.replacement B m σ (c + d)
          (Binding.rebound B n d c (c ↑ʳ (d ↑ʳ k))))
        (LaxTree.map-lax-tree (Binding.shift B d) (Binding.Variable m)
          (Binding.rebound B m d)
          (Binding.replacement B (d + m) (lifted m d σ) c
            (c ↑ʳ (d ↑ʳ k))))
  free-case {n} m σ d c k =
    Laws.related-by
      (ap (Binding.replacement B m σ (c + d)) (rebound-free n d c k) ∙
        ap
          (cases (λ j → Tree.hole (j ↑ˡ m))
            (λ k′ → Binding.under B m (c + d) (σ k′)))
          (split-at-↑ʳ (c + d) n k))
      (Laws.related-to
        (ap
            (LaxTree.map-lax-tree (Binding.shift B d) (Binding.Variable m)
              (Binding.rebound B m d))
            (ap
              (cases (λ j → Tree.hole (j ↑ˡ (d + m)))
                (λ y → Binding.under B (d + m) c (lifted m d σ y)))
              (split-at-↑ʳ c (d + n) (d ↑ʳ k))) ∙
          ap
            (λ y →
              LaxTree.map-lax-tree (Binding.shift B d)
                (Binding.Variable m)
                (Binding.rebound B m d) (Binding.under B (d + m) c y))
            (ap
              (cases (λ j → Tree.hole (j ↑ˡ m)) (λ k′ →
                  Binding.rename B (λ y → d ↑ʳ y) (σ k′)))
              (split-at-↑ʳ d n k)))
        (moved-weakened-rel m d c (σ k)))

  -- A variable outside the premise's inner binders, by its kind.
  premise-cases :
    {n : ℕ} (m : ℕ) (σ : Fin n → Binding.Expression B m) (d c : ℕ)
    (s : Fin d ⊎ Fin n)
    → Relation.TreeRel _＝_
        (Binding.replacement B m σ (c + d)
          (Binding.rebound B n d c (c ↑ʳ join-at d n s)))
        (LaxTree.map-lax-tree (Binding.shift B d) (Binding.Variable m)
          (Binding.rebound B m d)
          (Binding.replacement B (d + m) (lifted m d σ) c
            (c ↑ʳ join-at d n s)))
  premise-cases m σ d c (inl i) =
    Laws.equal-related (binder-case m σ d c i)
  premise-cases m σ d c (inr k) = free-case m σ d c k

  -- Every variable of the premise, by its kind.
  variable-cases :
    {n : ℕ} (m : ℕ) (σ : Fin n → Binding.Expression B m) (d c : ℕ)
    (s : Fin c ⊎ Fin (d + n))
    → Relation.TreeRel _＝_
        (Binding.replacement B m σ (c + d)
          (Binding.rebound B n d c (join-at c (d + n) s)))
        (LaxTree.map-lax-tree (Binding.shift B d) (Binding.Variable m)
          (Binding.rebound B m d)
          (Binding.replacement B (d + m) (lifted m d σ) c
            (join-at c (d + n) s)))
  variable-cases m σ d c (inl j) =
    Laws.equal-related (inner-case m σ d c j)
  variable-cases {n} m σ d c (inr y) =
    transport
      (λ z →
        Relation.TreeRel _＝_
          (Binding.replacement B m σ (c + d)
            (Binding.rebound B n d c (c ↑ʳ z)))
          (LaxTree.map-lax-tree (Binding.shift B d) (Binding.Variable m)
            (Binding.rebound B m d)
            (Binding.replacement B (d + m) (lifted m d σ) c (c ↑ʳ z))))
      (join-at-split-at d n y)
      (premise-cases m σ d c (split-at d n y))

  bound-substitute-rel :
    {n : ℕ} (m : ℕ) (σ : Fin n → Binding.Expression B m) (d : ℕ)
    {c : ℕ} (t : Tree.Tree (Sig.to-signature (Binding.over B))
      (Binding.Variable (d + n)) c)
    → Relation.TreeRel _＝_
        (Substitution.bind (Binding.replacement B m σ)
          (LaxTree.map-lax-tree (Binding.shift B d) (Binding.Variable n)
            (Binding.rebound B n d) t))
        (LaxTree.map-lax-tree (Binding.shift B d) (Binding.Variable m)
          (Binding.rebound B m d)
          (Substitution.bind (Binding.replacement B (d + m) (lifted m d σ))
            t))
  bound-substitute-rel {n} m σ d {c} (Tree.hole x) =
    transport
      (λ y →
        Relation.TreeRel _＝_
          (Binding.replacement B m σ (c + d) (Binding.rebound B n d c y))
          (LaxTree.map-lax-tree (Binding.shift B d) (Binding.Variable m)
            (Binding.rebound B m d)
            (Binding.replacement B (d + m) (lifted m d σ) c y)))
      (join-at-split-at c (d + n) x)
      (variable-cases m σ d c (split-at c (d + n) x))
  bound-substitute-rel {n} m σ d {c} (Tree.node o child) =
    Relation.node-rel
      (λ p →
        Laws.related-by
          (Functoriality.bind-transport (Binding.replacement B m σ)
            (+-assoc (depth o p) c d)
            (LaxTree.map-lax-tree (Binding.shift B d) (Binding.Variable n)
              (Binding.rebound B n d)
              (child p)))
          (Functoriality.tree-rel-equality-transport (+-assoc (depth o p) c d)
            (bound-substitute-rel m σ d (child p))))

  -- A premise under d binders, substituted, from its substitution by the
  -- lifted substitution.
  bound-substituted :
    {n : ℕ} (m : ℕ) (σ : Fin n → Binding.Expression B m) (d : ℕ)
    (e : Binding.Expression B (d + n)) (e′ : Binding.Expression B (d + m))
    → Relation.TreeRel _＝_
        (Binding.substitute B (d + m) (lifted m d σ) e) e′
    → Relation.TreeRel _＝_
        (Substitution.bind (Binding.replacement B m σ)
          (Binding.bound B n d e))
        (Binding.bound B m d e′)
  bound-substituted m σ d e e′ related =
    Relation.rel-compose _∙_ (bound-substitute-rel m σ d e)
      (bound-related m d related)

  ----------------------------------------------------------------------
  -- Moving under no binders

  -- A variable moved under no binders keeps its number.
  moved-zero :
    (m c : ℕ) (x : Binding.Variable m c)
    → Binding.moved B m 0 c x
      ＝ transport (Binding.Variable m) (+-zero-right c ⁻¹) x
  moved-zero m c x =
    to-ℕ-is-injective
      (Shift.to-ℕ-moved B 0 c x ∙
        (shifted-zero c (to-ℕ x) ∙
          Shift.to-ℕ-transport (λ j → j + m) (+-zero-right c ⁻¹) x ⁻¹))

  under-zero-at :
    (m : ℕ) {c : ℕ}
      (t : Tree.Tree (Sig.to-signature (Binding.over B)) (Binding.Variable m) c)
    → Relation.TreeRel _＝_
        (LaxTree.map-lax-tree (Binding.shift B 0) (Binding.Variable m)
          (Binding.moved B m 0) t)
        (transport
          (Tree.Tree (Sig.to-signature (Binding.over B)) (Binding.Variable m))
            (+-zero-right c ⁻¹) t)
  under-zero-at m {c} (Tree.hole x) =
    Laws.related-to
      (Transport.transport-hole B (+-zero-right c ⁻¹) x)
      (Laws.equal-related (ap Tree.hole (moved-zero m c x)))
  under-zero-at m {c} (Tree.node o child) =
    Laws.related-to
      (Transport.transport-node B (+-zero-right c ⁻¹) o child)
      (Relation.node-rel
        (λ p →
          let q₁ = +-assoc (depth o p) c 0
              q₂ = +-zero-right (depth o p + c) ⁻¹
              q₃ = ap (λ i → depth o p + i) (+-zero-right c ⁻¹)
          in Laws.related-to
               (ap
                 (λ q → transport
                   (Tree.Tree (Sig.to-signature (Binding.over B))
                     (Binding.Variable m)) q (child p))
                   (ℕ-identifications-agree q₃ (q₂ ∙ q₁)) ∙
                 transport-∙
                   (Tree.Tree (Sig.to-signature (Binding.over B))
                     (Binding.Variable m)) q₂ q₁ (child p))
               (Functoriality.tree-rel-equality-transport q₁
                 (under-zero-at m (child p)))))

  -- Moving under no binders is the identity.
  under-zero-rel :
    (m : ℕ) (e : Binding.Expression B m)
    → Relation.TreeRel _＝_ (Binding.under B m 0 e) e
  under-zero-rel m e = under-zero-at m e

  ----------------------------------------------------------------------
  -- Pointwise related substitutions

  -- The replacements of pointwise related substitutions, on a split
  -- variable.
  replacement-related :
    {n : ℕ} (m : ℕ) (σ τ : Fin n → Binding.Expression B m)
    → ((i : Fin n) → Relation.TreeRel _＝_ (σ i) (τ i))
    → (c : ℕ) (s : Fin c ⊎ Fin n)
    → Relation.TreeRel _＝_
        (cases (λ j → Tree.hole (j ↑ˡ m)) (λ k → Binding.under B m c (σ k)) s)
        (cases (λ j → Tree.hole (j ↑ˡ m)) (λ k → Binding.under B m c (τ k)) s)
  replacement-related m σ τ related c (inl j) = Relation.hole-rel refl
  replacement-related m σ τ related c (inr k) =
    lax-related (Binding.shift B c) (Binding.Variable m)
      (Binding.moved B m c) (related k)

  substitute-pointwise-rel :
    {n : ℕ} (m : ℕ) (σ τ : Fin n → Binding.Expression B m)
    → ((i : Fin n) → Relation.TreeRel _＝_ (σ i) (τ i))
    → (e : Binding.Expression B n)
    → Relation.TreeRel _＝_
        (Binding.substitute B m σ e) (Binding.substitute B m τ e)
  substitute-pointwise-rel {n} m σ τ related e =
    Substitution.bind-cong (Binding.replacement B m σ)
      (Binding.replacement B m τ)
      (λ {c} {x} {y} q →
        transport
          (λ z →
            Relation.TreeRel _＝_ (Binding.replacement B m σ c x)
              (Binding.replacement B m τ c z))
          q (replacement-related m σ τ related c (split-at c n x)))
      (identical e)

  ----------------------------------------------------------------------
  -- Lifting twice, and weakening

  -- Lifting over one binder twice is lifting over two.
  lifted-twice :
    {n : ℕ} (m : ℕ) (σ : Fin n → Binding.Expression B m)
    (i : Fin (2 + n))
    → Relation.TreeRel _＝_
        (lifted m 2 σ i) (lifted (suc m) 1 (lifted m 1 σ) i)
  lifted-twice m σ fzero = identical (Tree.hole fzero)
  lifted-twice m σ (fsuc fzero) =
    identical (Tree.hole (fsuc fzero))
  lifted-twice m σ (fsuc (fsuc k)) =
    Relation.rel-sym _⁻¹
      (Laws.rename-compose-rel B (λ y → 1 ↑ʳ y) (λ y → 1 ↑ʳ y)
        (σ k))

  -- The lifted substitution takes a weakened expression to the weakened
  -- substituted one.
  weaken-substituted :
    {n : ℕ} (m : ℕ) (σ : Fin n → Binding.Expression B m)
    (e : Binding.Expression B n)
    → Relation.TreeRel _＝_
        (Binding.substitute B (suc m) (lifted m 1 σ)
          (Binding.rename B fsuc e))
        (Binding.rename B fsuc (Binding.substitute B m σ e))
  weaken-substituted m σ e =
    Relation.rel-compose _∙_
      (substitute-related (suc m) (lifted m 1 σ)
        (Laws.rename-substitute-rel B fsuc e))
      (Relation.rel-compose _∙_
        (Composition.substitute-compose-rel B
          (λ i → Tree.hole (fsuc i)) (lifted m 1 σ) e)
        (Relation.rel-compose _∙_
          (substitute-pointwise-rel (suc m)
            (λ i →
              Binding.substitute B (suc m) (lifted m 1 σ)
                (Tree.hole (fsuc i)))
            (λ i → Binding.rename B fsuc (σ i))
            (λ i → under-zero-rel (suc m) (Binding.rename B fsuc (σ i)))
            e)
          (Relation.rel-sym _⁻¹
            (Relation.rel-compose _∙_
              (Laws.rename-substitute-rel B fsuc
                (Binding.substitute B m σ e))
              (Relation.rel-compose _∙_
                (Composition.substitute-compose-rel B σ
                  (λ i → Tree.hole (fsuc i)) e)
                (substitute-pointwise-rel (suc m)
                  (λ i →
                    Binding.substitute B (suc m)
                      (λ j → Tree.hole (fsuc j)) (σ i))
                  (λ i → Binding.rename B fsuc (σ i))
                  (λ i →
                    Relation.rel-sym _⁻¹
                      (Laws.rename-substitute-rel B fsuc (σ i)))
                  e))))))
