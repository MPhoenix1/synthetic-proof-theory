{-# OPTIONS --safe --without-K #-}

module SPT.IR.Indexed.Initiality where

-- Pointwise initiality of the native induction of IR.Indexed, with no
-- extensionality. A valuation satisfying a lax law is related to induction
-- at every element (`Lax`, `ind-unique-rel`); the law asks nothing of the
-- relation. Instances: the fundamental theorem for related methods
-- (`ind-rel`), uniqueness for congruent methods (`ind-unique`), and fusion
-- along a map of motives (`ind-fusion`). Under extensionality for the
-- arities at the motive's level every method is congruent (`congruent`).
--
-- Relational uniqueness is Foundation.Tree.Fold.Initiality's
-- `induction-unique-rel` at the derivations of the elements
-- (IR.Indexed.Derivation), with the native induction's value kept in the
-- relation; the other laws are its instances, as there.

open import SPT.Base
open import SPT.Foundation.Tree using (History)
import SPT.Foundation.Tree.Fold.Initiality as Trees

open import SPT.IR.Indexed using
  (U; Args; intro; info; Hyp; Method; ind; calls)
open import SPT.IR.Indexed.Derivation using
  (positions; child; signature; derivation; tabulate)
open import SPT.IR.Polynomial using
  (Poly; var; con; sigma; pi; Scheme; shape; Extensionality)

------------------------------------------------------------------------
-- Hypotheses of a valuation

-- A valuation gives a hypothesis at every recursive child of an argument:
-- its value there. Induction gives its own hypotheses as `calls`; they
-- agree with its values child by child, but they are a different term at
-- a variable code.

module _
  {ℓ κ ν : Level} (s : Scheme ℓ κ)
  (P : (i : Scheme.Index s) → U s i → Set ν)
  where

  values :
    ((i : Scheme.Index s) (u : U s i) → P i u)
    → {X : Set (ℓ ⊔ κ)} (p : Poly ℓ κ (Scheme.Data s) X) (a : Args s p)
    → Hyp s P p a
  values v (var i) a = lift (v i a)
  values v (con A) a = lift ⋆
  values v (sigma p q) (a , b) =
    (values v p a , values v (q (info s p a)) b)
  values v (pi A p) f = λ x → values v (p x) (f x)

------------------------------------------------------------------------
-- Related hypotheses

-- A relation between the values of two motives lifts to their hypotheses
-- at an argument: related at every recursive child, nothing asked at a
-- constant, componentwise at a sum and pointwise at a product.

module _
  {ℓ κ ν μ γ : Level} (s : Scheme ℓ κ)
  (Q : (i : Scheme.Index s) → U s i → Set μ)
  (P : (i : Scheme.Index s) → U s i → Set ν)
  (C : (i : Scheme.Index s) (u : U s i) → Q i u → P i u → Set γ)
  where

  Lifted :
    {X : Set (ℓ ⊔ κ)} (p : Poly ℓ κ (Scheme.Data s) X) (a : Args s p)
    → Hyp s Q p a → Hyp s P p a → Set (ℓ ⊔ γ)
  Lifted (var i) a h k = Lift ℓ (C i a (lower h) (lower k))
  Lifted (con A) a h k = Lift (ℓ ⊔ γ) 𝟙
  Lifted (sigma p q) (a , b) (h , h′) (k , k′) =
    Σ (Lifted p a h k) (λ _ → Lifted (q (info s p a)) b h′ k′)
  Lifted (pi A p) f h k = (x : A) → Lifted (p x) (f x) (h x) (k x)

------------------------------------------------------------------------
-- Relational uniqueness

-- The lax law of a valuation v for methods m: at every introduction, the
-- methods at any hypotheses related to v at the children are related to
-- v at the introduced element. It asks for no reflexivity, transitivity
-- or congruence. The proof is Foundation.Tree.Fold.Initiality's at the
-- derivations, for the relation of v to induction (`Relates`). At a node,
-- the relatedness at the positions, tabulated, is the lifted relation
-- between the values of v and the calls of induction
-- (`related-hypotheses`), where the law applies (`related-node`), with
-- nothing transported.

module _
  {ℓ κ ν μ γ : Level} (s : Scheme ℓ κ)
  (Q : (i : Scheme.Index s) → U s i → Set μ)
  (P : (i : Scheme.Index s) → U s i → Set ν)
  (C : (i : Scheme.Index s) (u : U s i) → Q i u → P i u → Set γ)
  where

  Lax :
    ((i : Scheme.Index s) (u : U s i) → Q i u) → Method s P
    → Set (ℓ ⊔ ν ⊔ γ)
  Lax v m =
    (i : Scheme.Index s) (a : Args s (shape (Scheme.rule s i)))
    (k : Hyp s P (shape (Scheme.rule s i)) a)
    → Lifted s Q P C (shape (Scheme.rule s i)) a
        (values s Q v (shape (Scheme.rule s i)) a) k
    → C i (intro a) (v i (intro a)) (m i a k)

module _
  {ℓ κ ν μ γ : Level} (s : Scheme ℓ κ)
  (Q : (i : Scheme.Index s) → U s i → Set μ)
  (P : (i : Scheme.Index s) → U s i → Set ν)
  (C : (i : Scheme.Index s) (u : U s i) → Q i u → P i u → Set γ)
  (v : (i : Scheme.Index s) (u : U s i) → Q i u) (m : Method s P)
  where

  Relates : (i : Scheme.Index s) → U s i → Set γ
  Relates i u = C i u (v i u) (ind s P m i u)

  related-hypotheses :
    {X : Set (ℓ ⊔ κ)} (p : Poly ℓ κ (Scheme.Data s) X) (a : Args s p)
    → Hyp s Relates p a
    → Lifted s Q P C p a (values s Q v p a) (calls s P m p a)
  related-hypotheses (var i) a h = h
  related-hypotheses (con A) a h = h
  related-hypotheses (sigma p q) (a , b) (h , h′) =
    (related-hypotheses p a h , related-hypotheses (q (info s p a)) b h′)
  related-hypotheses (pi A p) f h =
    λ x → related-hypotheses (p x) (f x) (h x)

module _
  {ℓ κ ν μ γ : Level} (s : Scheme ℓ κ)
  (Q : (i : Scheme.Index s) → U s i → Set μ)
  (P : (i : Scheme.Index s) → U s i → Set ν)
  (C : (i : Scheme.Index s) (u : U s i) → Q i u → P i u → Set γ)
  (v : (i : Scheme.Index s) (u : U s i) → Q i u) (m : Method s P)
  (law : Lax s Q P C v m)
  where

  related-node :
    {j : Σ (Scheme.Index s) (U s)} (o : 𝟙)
    (xs : (z : positions s j) → History (signature s) (child s j z))
    (k : (z : positions s j) → 𝟙)
    → ( (z : positions s j)
        → Relates s Q P C v m (pr₁ (child s j z)) (pr₂ (child s j z)))
    → Relates s Q P C v m (pr₁ j) (pr₂ j)
  related-node {i , intro a} o xs k r =
    law i a (calls s P m (shape (Scheme.rule s i)) a)
      (related-hypotheses s Q P C v m (shape (Scheme.rule s i)) a
        (tabulate s (Relates s Q P C v m) (shape (Scheme.rule s i)) a r))

  ind-unique-rel :
    (i : Scheme.Index s) (u : U s i) → C i u (v i u) (ind s P m i u)
  ind-unique-rel i u =
    Trees.induction-unique-rel
      (λ (j : Σ (Scheme.Index s) (U s)) (t : History (signature s) j)
        → Q (pr₁ j) (pr₂ j))
      (λ (j : Σ (Scheme.Index s) (U s)) (t : History (signature s) j) → 𝟙)
      (λ (j : Σ (Scheme.Index s) (U s)) (t : History (signature s) j)
         (q : Q (pr₁ j) (pr₂ j)) (x : 𝟙)
        → C (pr₁ j) (pr₂ j) q (ind s P m (pr₁ j) (pr₂ j)))
      (λ {j} t → v (pr₁ j) (pr₂ j))
      (λ ())
      (λ o xs k → ⋆)
      (record { at-hole = λ (); at-node = related-node })
      (derivation s i u)

------------------------------------------------------------------------
-- The fundamental theorem

-- Methods related at related hypotheses have related inductions. The
-- values of an induction are its calls at every child, so a relation
-- lifted at the one is lifted at the other.

module _
  {ℓ κ ν μ γ : Level} (s : Scheme ℓ κ)
  (Q : (i : Scheme.Index s) → U s i → Set μ)
  (P : (i : Scheme.Index s) → U s i → Set ν)
  (C : (i : Scheme.Index s) (u : U s i) → Q i u → P i u → Set γ)
  (n : Method s Q)
  where

  values-to-calls :
    {X : Set (ℓ ⊔ κ)} (p : Poly ℓ κ (Scheme.Data s) X) (a : Args s p)
    (k : Hyp s P p a)
    → Lifted s Q P C p a (values s Q (ind s Q n) p a) k
    → Lifted s Q P C p a (calls s Q n p a) k
  values-to-calls (var i) a k r = r
  values-to-calls (con A) a k r = r
  values-to-calls (sigma p q) (a , b) (k , k′) (r , r′) =
    ( values-to-calls p a k r
    , values-to-calls (q (info s p a)) b k′ r′)
  values-to-calls (pi A p) f k r =
    λ x → values-to-calls (p x) (f x) (k x) (r x)

module _
  {ℓ κ ν μ γ : Level} (s : Scheme ℓ κ)
  (Q : (i : Scheme.Index s) → U s i → Set μ)
  (P : (i : Scheme.Index s) → U s i → Set ν)
  (C : (i : Scheme.Index s) (u : U s i) → Q i u → P i u → Set γ)
  (n : Method s Q) (m : Method s P)
  where

  Relational : Set (ℓ ⊔ ν ⊔ μ ⊔ γ)
  Relational =
    (i : Scheme.Index s) (a : Args s (shape (Scheme.rule s i)))
    (h : Hyp s Q (shape (Scheme.rule s i)) a)
    (k : Hyp s P (shape (Scheme.rule s i)) a)
    → Lifted s Q P C (shape (Scheme.rule s i)) a h k
    → C i (intro a) (n i a h) (m i a k)

  ind-rel :
    Relational → (i : Scheme.Index s) (u : U s i)
    → C i u (ind s Q n i u) (ind s P m i u)
  ind-rel related =
    ind-unique-rel s Q P C (ind s Q n) m
      ( λ i a k r →
          related i a (calls s Q n (shape (Scheme.rule s i)) a) k
            (values-to-calls s Q P C n (shape (Scheme.rule s i)) a k r))

------------------------------------------------------------------------
-- Uniqueness

-- Methods are congruent when hypotheses agreeing at every child give the
-- same value; at a product the agreement is pointwise, so this is a
-- genuine hypothesis there. A valuation satisfying the computation
-- equations of congruent methods is their induction at every element, and
-- induction satisfies them.

module _
  {ℓ κ ν : Level} (s : Scheme ℓ κ)
  (P : (i : Scheme.Index s) → U s i → Set ν)
  where

  Identical : (i : Scheme.Index s) (u : U s i) → P i u → P i u → Set ν
  Identical i u x y = x ＝ y

  Congruent : Method s P → Set (ℓ ⊔ ν)
  Congruent m =
    (i : Scheme.Index s) (a : Args s (shape (Scheme.rule s i)))
    (h k : Hyp s P (shape (Scheme.rule s i)) a)
    → Lifted s P P Identical (shape (Scheme.rule s i)) a h k
    → m i a h ＝ m i a k

  Homomorphic :
    ((i : Scheme.Index s) (u : U s i) → P i u) → Method s P → Set (ℓ ⊔ ν)
  Homomorphic v m =
    (i : Scheme.Index s) (a : Args s (shape (Scheme.rule s i)))
    → v i (intro a) ＝ m i a (values s P v (shape (Scheme.rule s i)) a)

  calls-agree :
    (m : Method s P) {X : Set (ℓ ⊔ κ)} (p : Poly ℓ κ (Scheme.Data s) X)
    (a : Args s p)
    → Lifted s P P Identical p a
        (calls s P m p a) (values s P (ind s P m) p a)
  calls-agree m (var i) a = lift refl
  calls-agree m (con A) a = lift ⋆
  calls-agree m (sigma p q) (a , b) =
    (calls-agree m p a , calls-agree m (q (info s p a)) b)
  calls-agree m (pi A p) f = λ x → calls-agree m (p x) (f x)

  ind-unique :
    (v : (i : Scheme.Index s) (u : U s i) → P i u) (m : Method s P)
    → Congruent m → Homomorphic v m
    → (i : Scheme.Index s) (u : U s i) → v i u ＝ ind s P m i u
  ind-unique v m congruence equations =
    ind-unique-rel s P P Identical v m
      ( λ i a k r →
          equations i a
          ∙ congruence i a (values s P v (shape (Scheme.rule s i)) a) k r)

  ind-homomorphic :
    (m : Method s P) → Congruent m → Homomorphic (ind s P m) m
  ind-homomorphic m congruence i a =
    congruence i a (calls s P m (shape (Scheme.rule s i)) a)
      (values s P (ind s P m) (shape (Scheme.rule s i)) a)
      (calls-agree m (shape (Scheme.rule s i)) a)

------------------------------------------------------------------------
-- Congruence under extensionality

-- Hypotheses agreeing at every child are identical when the families of
-- hypotheses over the arities are extensional, so every method is
-- congruent. Extensionality is used at products only.

module _
  {ℓ κ ν : Level} (extensionality : Extensionality ℓ ν) (s : Scheme ℓ κ)
  (P : (i : Scheme.Index s) → U s i → Set ν)
  where

  agreement :
    {X : Set (ℓ ⊔ κ)} (p : Poly ℓ κ (Scheme.Data s) X) (a : Args s p)
    (h k : Hyp s P p a) → Lifted s P P (Identical s P) p a h k → h ＝ k
  agreement (var i) a h k r = ap lift (lower r)
  agreement (con A) a h k r = refl
  agreement (sigma p q) (a , b) (h , h′) (k , k′) (r , r′) =
    ap₂ (λ x y → (x , y))
      (agreement p a h k r) (agreement (q (info s p a)) b h′ k′ r′)
  agreement (pi A p) f h k r =
    extensionality A (λ x → Hyp s P (p x) (f x)) h k
      (λ x → agreement (p x) (f x) (h x) (k x) (r x))

  congruent : (m : Method s P) → Congruent s P m
  congruent m i a h k r =
    ap (m i a) (agreement (shape (Scheme.rule s i)) a h k r)

------------------------------------------------------------------------
-- Fusion

-- A map of motives carries hypotheses along (`mapped`). When it carries
-- the methods of one motive to congruent methods of the other at mapped
-- hypotheses, the image of induction is the other induction: the two are
-- related by the graph of the map.

module _
  {ℓ κ ν ν′ : Level} (s : Scheme ℓ κ)
  (P : (i : Scheme.Index s) → U s i → Set ν)
  (P′ : (i : Scheme.Index s) → U s i → Set ν′)
  (f : (i : Scheme.Index s) (u : U s i) → P i u → P′ i u)
  where

  mapped :
    {X : Set (ℓ ⊔ κ)} (p : Poly ℓ κ (Scheme.Data s) X) (a : Args s p)
    → Hyp s P p a → Hyp s P′ p a
  mapped (var i) a h = lift (f i a (lower h))
  mapped (con A) a h = lift ⋆
  mapped (sigma p q) (a , b) (h , h′) =
    (mapped p a h , mapped (q (info s p a)) b h′)
  mapped (pi A p) g h = λ x → mapped (p x) (g x) (h x)

  Graph : (i : Scheme.Index s) (u : U s i) → P i u → P′ i u → Set ν′
  Graph i u x y = f i u x ＝ y

  graph-agreement :
    {X : Set (ℓ ⊔ κ)} (p : Poly ℓ κ (Scheme.Data s) X) (a : Args s p)
    (h : Hyp s P p a) (k : Hyp s P′ p a)
    → Lifted s P P′ Graph p a h k
    → Lifted s P′ P′ (Identical s P′) p a (mapped p a h) k
  graph-agreement (var i) a h k r = r
  graph-agreement (con A) a h k r = r
  graph-agreement (sigma p q) (a , b) (h , h′) (k , k′) (r , r′) =
    ( graph-agreement p a h k r
    , graph-agreement (q (info s p a)) b h′ k′ r′)
  graph-agreement (pi A p) g h k r =
    λ x → graph-agreement (p x) (g x) (h x) (k x) (r x)

  Carries : Method s P → Method s P′ → Set (ℓ ⊔ ν ⊔ ν′)
  Carries m m′ =
    (i : Scheme.Index s) (a : Args s (shape (Scheme.rule s i)))
    (h : Hyp s P (shape (Scheme.rule s i)) a)
    → f i (intro a) (m i a h)
      ＝ m′ i a (mapped (shape (Scheme.rule s i)) a h)

  ind-fusion :
    (m : Method s P) (m′ : Method s P′) → Congruent s P′ m′ → Carries m m′
    → (i : Scheme.Index s) (u : U s i)
    → f i u (ind s P m i u) ＝ ind s P′ m′ i u
  ind-fusion m m′ congruence carries =
    ind-unique-rel s P P′ Graph (ind s P m) m′
      ( λ i a k r →
          carries i a (calls s P m (shape (Scheme.rule s i)) a)
          ∙ congruence i a
              (mapped (shape (Scheme.rule s i)) a
                (calls s P m (shape (Scheme.rule s i)) a))
              k
              (graph-agreement (shape (Scheme.rule s i)) a
                (calls s P m (shape (Scheme.rule s i)) a) k
                (values-to-calls s P P′ Graph m
                  (shape (Scheme.rule s i)) a k r)))
