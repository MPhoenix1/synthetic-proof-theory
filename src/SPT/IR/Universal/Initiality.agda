{-# OPTIONS --safe --without-K #-}

module SPT.IR.Universal.Initiality where

-- Pointwise initiality of the native induction of IR.Universal, the
-- universal type of Dybjer–Setzer descriptions, with no extensionality. A
-- valuation satisfying a lax law is related to induction at every element
-- (`Lax`, `ind-unique-rel`). Instances: the fundamental theorem for related
-- methods (`ind-rel`), uniqueness for congruent methods (`ind-unique`) and
-- fusion along a map of motives (`ind-fusion`). At δ the hypotheses are one
-- function on the child map, so extensionality for families over the
-- arities makes every method congruent (`congruent`).
--
-- Relational uniqueness is Foundation.Tree.Fold.Initiality's
-- `induction-unique-rel` at the derivations of the elements
-- (IR.Universal.Derivation), with the native induction's value kept in the
-- relation; the other laws are its instances, as there.

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)
open import SPT.Foundation.Tree using (History)
import SPT.Foundation.Tree.Fold.Initiality as Trees

open import SPT.IR.Universal using
  (U; Args; box; intro; value; Hyp; Method; ind; calls)
open import SPT.IR.Universal.Derivation using
  (positions; child; signature; derivation; tabulate)
open import SPT.IR.Description using (Desc; ι; σ; δ)

------------------------------------------------------------------------
-- Hypotheses of a valuation

-- A valuation gives, at a δ, the function of its values on the child map,
-- and nothing at the end of a description. Induction gives its own
-- hypotheses as `calls`; the two agree at every child.

module _
  {s d ν : Level} {D : Set d} (γ : Desc {s = s} D) (P : U γ → Set ν)
  where

  values :
    ((u : U γ) → P u) → (ε : Desc {s = s} D) (a : Args ε (U γ) (value γ))
    → Hyp ε (U γ) (value γ) P a
  values v (ι e) (box a) = lift ⋆
  values v (σ A H) (box (a , b)) = values v (H a) b
  values v (δ A H) (box (f , b)) =
    ((λ x → v (f x)) , values v (H (λ x → value γ (f x))) b)

------------------------------------------------------------------------
-- Related hypotheses

-- A relation between the values of two motives lifts to their hypotheses
-- at an argument: at a δ, related at every child of the map.

module _
  {s d ν μ ρ : Level} {D : Set d} (γ : Desc {s = s} D)
  (Q : U γ → Set μ) (P : U γ → Set ν)
  (C : (u : U γ) → Q u → P u → Set ρ)
  where

  Lifted :
    (ε : Desc {s = s} D) (a : Args ε (U γ) (value γ))
    → Hyp ε (U γ) (value γ) Q a → Hyp ε (U γ) (value γ) P a
    → Set (s ⊔ ρ)
  Lifted (ι e) (box a) h k = Lift (s ⊔ ρ) 𝟙
  Lifted (σ A H) (box (a , b)) h k = Lifted (H a) b h k
  Lifted (δ A H) (box (f , b)) (h , h′) (k , k′) =
    Σ ((x : A) → C (f x) (h x) (k x))
      (λ _ → Lifted (H (λ x → value γ (f x))) b h′ k′)

------------------------------------------------------------------------
-- Relational uniqueness

-- The lax law of a valuation v for methods m: at every introduction, the
-- methods at any hypotheses related to v at the children are related to
-- v at the introduced element. No reflexivity, transitivity or congruence
-- is asked. The proof is Foundation.Tree.Fold.Initiality's at the
-- derivations, for the relation of v to induction (`Relates`). At a node,
-- the relatedness at the positions, tabulated, is the lifted relation
-- between the values of v and the calls of induction
-- (`related-hypotheses`), where the law applies (`related-node`).

module _
  {s d ν μ ρ : Level} {D : Set d} (γ : Desc {s = s} D)
  (Q : U γ → Set μ) (P : U γ → Set ν)
  (C : (u : U γ) → Q u → P u → Set ρ)
  where

  Lax : ((u : U γ) → Q u) → Method γ P → Set (s ⊔ ν ⊔ ρ)
  Lax v m =
    (a : Args γ (U γ) (value γ)) (k : Hyp γ (U γ) (value γ) P a)
    → Lifted γ Q P C γ a (values γ Q v γ a) k
    → C (intro a) (v (intro a)) (m a k)

module _
  {s d ν μ ρ : Level} {D : Set d} (γ : Desc {s = s} D)
  (Q : U γ → Set μ) (P : U γ → Set ν)
  (C : (u : U γ) → Q u → P u → Set ρ)
  (v : (u : U γ) → Q u) (m : Method γ P)
  where

  Relates : U γ → Set ρ
  Relates u = C u (v u) (ind γ P m u)

  related-hypotheses :
    (ε : Desc {s = s} D) (a : Args ε (U γ) (value γ))
    → Hyp ε (U γ) (value γ) Relates a
    → Lifted γ Q P C ε a (values γ Q v ε a) (calls γ P m ε a)
  related-hypotheses (ι e) (box a) h = h
  related-hypotheses (σ A H) (box (a , b)) h = related-hypotheses (H a) b h
  related-hypotheses (δ A H) (box (f , b)) (h , h′) =
    (h , related-hypotheses (H (λ x → value γ (f x))) b h′)

module _
  {s d ν μ ρ : Level} {D : Set d} (γ : Desc {s = s} D)
  (Q : U γ → Set μ) (P : U γ → Set ν)
  (C : (u : U γ) → Q u → P u → Set ρ)
  (v : (u : U γ) → Q u) (m : Method γ P) (law : Lax γ Q P C v m)
  where

  related-node :
    {u : U γ} (o : 𝟙)
    (xs : (p : positions γ u) → History (signature γ) (child γ u p))
    (k : (p : positions γ u) → 𝟙)
    → ((p : positions γ u) → Relates γ Q P C v m (child γ u p))
    → Relates γ Q P C v m u
  related-node {intro a} o xs k r =
    law a (calls γ P m γ a)
      (related-hypotheses γ Q P C v m γ a
        (tabulate γ (Relates γ Q P C v m) γ a r))

  ind-unique-rel : (u : U γ) → C u (v u) (ind γ P m u)
  ind-unique-rel u =
    Trees.induction-unique-rel
      (λ (w : U γ) (t : History (signature γ) w) → Q w)
      (λ (w : U γ) (t : History (signature γ) w) → 𝟙)
      (λ (w : U γ) (t : History (signature γ) w) (q : Q w) (x : 𝟙)
        → C w q (ind γ P m w))
      (λ {w} t → v w)
      (λ ())
      (λ o xs k → ⋆)
      (record { at-hole = λ (); at-node = related-node })
      (derivation γ u)

------------------------------------------------------------------------
-- The fundamental theorem

-- Methods related at related hypotheses have related inductions. The
-- values of an induction are its calls at every child, so a relation
-- lifted at the one is lifted at the other.

module _
  {s d ν μ ρ : Level} {D : Set d} (γ : Desc {s = s} D)
  (Q : U γ → Set μ) (P : U γ → Set ν)
  (C : (u : U γ) → Q u → P u → Set ρ) (n : Method γ Q)
  where

  values-to-calls :
    (ε : Desc {s = s} D) (a : Args ε (U γ) (value γ))
    (k : Hyp ε (U γ) (value γ) P a)
    → Lifted γ Q P C ε a (values γ Q (ind γ Q n) ε a) k
    → Lifted γ Q P C ε a (calls γ Q n ε a) k
  values-to-calls (ι e) (box a) k r = r
  values-to-calls (σ A H) (box (a , b)) k r = values-to-calls (H a) b k r
  values-to-calls (δ A H) (box (f , b)) (k , k′) (r , r′) =
    (r , values-to-calls (H (λ x → value γ (f x))) b k′ r′)

module _
  {s d ν μ ρ : Level} {D : Set d} (γ : Desc {s = s} D)
  (Q : U γ → Set μ) (P : U γ → Set ν)
  (C : (u : U γ) → Q u → P u → Set ρ) (n : Method γ Q) (m : Method γ P)
  where

  Relational : Set (s ⊔ ν ⊔ μ ⊔ ρ)
  Relational =
    (a : Args γ (U γ) (value γ))
    (h : Hyp γ (U γ) (value γ) Q a) (k : Hyp γ (U γ) (value γ) P a)
    → Lifted γ Q P C γ a h k → C (intro a) (n a h) (m a k)

  ind-rel : Relational → (u : U γ) → C u (ind γ Q n u) (ind γ P m u)
  ind-rel related =
    ind-unique-rel γ Q P C (ind γ Q n) m
      ( λ a k r →
          related a (calls γ Q n γ a) k
            (values-to-calls γ Q P C n γ a k r))

------------------------------------------------------------------------
-- Uniqueness

-- Methods are congruent when hypotheses agreeing at every child give the
-- same value; at a δ the agreement is pointwise on the child map, so this
-- is a genuine hypothesis there. A valuation satisfying the computation
-- equations of congruent methods is their induction at every element, and
-- induction satisfies them.

module _
  {s d ν : Level} {D : Set d} (γ : Desc {s = s} D) (P : U γ → Set ν)
  where

  Identical : (u : U γ) → P u → P u → Set ν
  Identical u x y = x ＝ y

  Congruent : Method γ P → Set (s ⊔ ν)
  Congruent m =
    (a : Args γ (U γ) (value γ)) (h k : Hyp γ (U γ) (value γ) P a)
    → Lifted γ P P Identical γ a h k → m a h ＝ m a k

  Homomorphic : ((u : U γ) → P u) → Method γ P → Set (s ⊔ ν)
  Homomorphic v m =
    (a : Args γ (U γ) (value γ)) → v (intro a) ＝ m a (values γ P v γ a)

  calls-agree :
    (m : Method γ P) (ε : Desc {s = s} D) (a : Args ε (U γ) (value γ))
    → Lifted γ P P Identical ε a
        (calls γ P m ε a) (values γ P (ind γ P m) ε a)
  calls-agree m (ι e) (box a) = lift ⋆
  calls-agree m (σ A H) (box (a , b)) = calls-agree m (H a) b
  calls-agree m (δ A H) (box (f , b)) =
    ((λ x → refl) , calls-agree m (H (λ x → value γ (f x))) b)

  ind-unique :
    (v : (u : U γ) → P u) (m : Method γ P) → Congruent m → Homomorphic v m
    → (u : U γ) → v u ＝ ind γ P m u
  ind-unique v m congruence equations =
    ind-unique-rel γ P P Identical v m
      ( λ a k r → equations a ∙ congruence a (values γ P v γ a) k r)

  ind-homomorphic : (m : Method γ P) → Congruent m → Homomorphic (ind γ P m) m
  ind-homomorphic m congruence a =
    congruence a (calls γ P m γ a) (values γ P (ind γ P m) γ a)
      (calls-agree m γ a)

------------------------------------------------------------------------
-- Congruence under extensionality

-- Hypotheses agreeing at every child are identical when the families over
-- the arities are extensional, so every method is congruent.
-- Extensionality is used at δ only, on the function of child values.

module _
  {s d ν : Level} {D : Set d}
  (extensionality : (A : Set s) (Y : A → Set ν) → FunExt A Y)
  (γ : Desc {s = s} D) (P : U γ → Set ν)
  where

  agreement :
    (ε : Desc {s = s} D) (a : Args ε (U γ) (value γ))
    (h k : Hyp ε (U γ) (value γ) P a)
    → Lifted γ P P (Identical γ P) ε a h k → h ＝ k
  agreement (ι e) (box a) h k r = refl
  agreement (σ A H) (box (a , b)) h k r = agreement (H a) b h k r
  agreement (δ A H) (box (f , b)) (h , h′) (k , k′) (r , r′) =
    ap₂ (λ x y → (x , y))
      (extensionality A (λ x → P (f x)) h k r)
      (agreement (H (λ x → value γ (f x))) b h′ k′ r′)

  congruent : (m : Method γ P) → Congruent γ P m
  congruent m a h k r = ap (m a) (agreement γ a h k r)

------------------------------------------------------------------------
-- Fusion

-- A map of motives carries hypotheses along (`mapped`). When it carries
-- the methods of one motive to congruent methods of the other at mapped
-- hypotheses, the image of induction is the other induction: the two are
-- related by the graph of the map.

module _
  {s d ν ν′ : Level} {D : Set d} (γ : Desc {s = s} D)
  (P : U γ → Set ν) (P′ : U γ → Set ν′) (f : (u : U γ) → P u → P′ u)
  where

  mapped :
    (ε : Desc {s = s} D) (a : Args ε (U γ) (value γ))
    → Hyp ε (U γ) (value γ) P a → Hyp ε (U γ) (value γ) P′ a
  mapped (ι e) (box a) h = lift ⋆
  mapped (σ A H) (box (a , b)) h = mapped (H a) b h
  mapped (δ A H) (box (g , b)) (h , h′) =
    ((λ x → f (g x) (h x)) , mapped (H (λ x → value γ (g x))) b h′)

  Graph : (u : U γ) → P u → P′ u → Set ν′
  Graph u x y = f u x ＝ y

  graph-agreement :
    (ε : Desc {s = s} D) (a : Args ε (U γ) (value γ))
    (h : Hyp ε (U γ) (value γ) P a) (k : Hyp ε (U γ) (value γ) P′ a)
    → Lifted γ P P′ Graph ε a h k
    → Lifted γ P′ P′ (Identical γ P′) ε a (mapped ε a h) k
  graph-agreement (ι e) (box a) h k r = r
  graph-agreement (σ A H) (box (a , b)) h k r =
    graph-agreement (H a) b h k r
  graph-agreement (δ A H) (box (g , b)) (h , h′) (k , k′) (r , r′) =
    (r , graph-agreement (H (λ x → value γ (g x))) b h′ k′ r′)

  Carries : Method γ P → Method γ P′ → Set (s ⊔ ν ⊔ ν′)
  Carries m m′ =
    (a : Args γ (U γ) (value γ)) (h : Hyp γ (U γ) (value γ) P a)
    → f (intro a) (m a h) ＝ m′ a (mapped γ a h)

  ind-fusion :
    (m : Method γ P) (m′ : Method γ P′) → Congruent γ P′ m′ → Carries m m′
    → (u : U γ) → f u (ind γ P m u) ＝ ind γ P′ m′ u
  ind-fusion m m′ congruence carries =
    ind-unique-rel γ P P′ Graph (ind γ P m) m′
      ( λ a k r →
          carries a (calls γ P m γ a)
          ∙ congruence a (mapped γ a (calls γ P m γ a)) k
              (graph-agreement γ a (calls γ P m γ a) k
                (values-to-calls γ P P′ Graph m γ a k r)))
