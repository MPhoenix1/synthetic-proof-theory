{-# OPTIONS --safe --without-K #-}

module SPT.IR.Indexed where

-- One induction–recursive family for all schemes of indexed polynomial
-- induction–recursion, over the codes of SPT.IR.Polynomial: the
-- carriers `U s i` and their readouts `value s i`, defined together with
-- the arguments of every code over them (`Args`) and their information
-- (`info`). Arguments are ordinary dependent sums and products with the
-- children themselves at recursive inputs. One datatype over the roots of
-- the scheme (`Root`, `Node`) carries the recursion, so safe Agda accepts
-- it at a variable code. With no extensionality, by refl:
--
--   value s i (intro a) = output (rule i) (info s (shape (rule i)) a)
--   ind s P m i (intro a) = m i a (calls s P m (shape (rule i)) a)
--   root s i (intro a) = a,     intro (root s i u) = u.

open import SPT.Base

open import SPT.IR.Polynomial using
  (Poly; var; con; sigma; pi; Family; Scheme; Info; shape; output)

------------------------------------------------------------------------
-- Roots

-- A root of a scheme is an index or a code with its information. At an
-- index the code is the shape of its rule.

module _
  {ℓ κ : Level} (s : Scheme ℓ κ)
  where

  Root : Set (lsuc (ℓ ⊔ κ))
  Root = Scheme.Index s ⊎ Σ (Set (ℓ ⊔ κ)) (Poly ℓ κ (Scheme.Data s))

  information : Root → Set (ℓ ⊔ κ)
  information (inl i) = Info (Scheme.rule s i)
  information (inr (X , p)) = X

  polynomial : (r : Root) → Poly ℓ κ (Scheme.Data s) (information r)
  polynomial (inl i) = shape (Scheme.rule s i)
  polynomial (inr (X , p)) = p

------------------------------------------------------------------------
-- The universal family and its readouts

-- Mathematical shape:
--
--   intro : Args s (polynomial s r) → Node s r,     U s i = Node s (inl i)
--   Args (var i) = U s i,     Args (con A) = A
--   Args (sigma p q) = Σ (a : Args p). Args (q (info p a))
--   Args (pi A p) = Π (a : A). Args (p a).
--
-- A node at a code wraps an argument only so that the information can
-- recurse through it: `traverse` wraps each part again, and `value`
-- passes its own node on unchanged.

module _
  {ℓ κ : Level} (s : Scheme ℓ κ)
  where

  mutual
    data Node (r : Root s) : Set ℓ where
      intro : Args (polynomial s r) → Node r

    U : Scheme.Index s → Set ℓ
    U i = Node (inl i)

    Args : {X : Set (ℓ ⊔ κ)} → Poly ℓ κ (Scheme.Data s) X → Set ℓ
    Args (var i) = U i
    Args (con A) = A
    Args (sigma p q) = Σ (Args p) (λ a → Args (q (info p a)))
    Args (pi A p) = (a : A) → Args (p a)

    info : {X : Set (ℓ ⊔ κ)} (p : Poly ℓ κ (Scheme.Data s) X) → Args p → X
    info p a = traverse p (intro a)

    value : (i : Scheme.Index s) → U i → Scheme.Data s i
    value i (intro a) =
      output (Scheme.rule s i) (traverse (shape (Scheme.rule s i)) (intro a))

    -- The information of a node at a code, recursing as the code does.
    traverse :
      {X : Set (ℓ ⊔ κ)} (p : Poly ℓ κ (Scheme.Data s) X)
      → Node (inr (X , p)) → X
    traverse (var i) (intro a) = value i a
    traverse (con A) (intro a) = lift a
    traverse (sigma p q) (intro (a , b)) =
      traverse p (intro a) , traverse (q (traverse p (intro a))) (intro b)
    traverse (pi A p) (intro f) = λ a → traverse (p a) (intro (f a))

  output-β :
    (i : Scheme.Index s) (a : Args (shape (Scheme.rule s i)))
    → value i (intro a)
      ＝ output (Scheme.rule s i) (info (shape (Scheme.rule s i)) a)
  output-β i a = refl

------------------------------------------------------------------------
-- Information at open parts

-- The information of a sum reads the continuation at its first part's
-- own information, and that of a product is the function of its parts'
-- information, both by refl at variable parts.

module _
  {ℓ κ : Level} (s : Scheme ℓ κ)
  where

  info-sigma :
    {X : Set (ℓ ⊔ κ)} {Y : X → Set (ℓ ⊔ κ)}
    (p : Poly ℓ κ (Scheme.Data s) X)
    (q : (x : X) → Poly ℓ κ (Scheme.Data s) (Y x))
    (a : Args s p) (b : Args s (q (info s p a)))
    → info s (sigma p q) (a , b) ＝ (info s p a , info s (q (info s p a)) b)
  info-sigma p q a b = refl

  info-pi :
    (A : Set ℓ) {Y : A → Set (ℓ ⊔ κ)}
    (p : (a : A) → Poly ℓ κ (Scheme.Data s) (Y a)) (f : Args s (pi A p))
    → info s (pi A p) f ＝ (λ a → info s (p a) (f a))
  info-pi A p f = refl

------------------------------------------------------------------------
-- Induction

-- A hypothesis holds at every recursive child of an argument; a sum reads
-- its continuation at its first part's information. Induction recurses
-- as the information does, through nodes at the codes.

module _
  {ℓ κ ν : Level} (s : Scheme ℓ κ)
  (P : (i : Scheme.Index s) → U s i → Set ν)
  where

  Hyp :
    {X : Set (ℓ ⊔ κ)} (p : Poly ℓ κ (Scheme.Data s) X) → Args s p
    → Set (ℓ ⊔ ν)
  Hyp (var i) a = Lift ℓ (P i a)
  Hyp (con A) a = Lift (ℓ ⊔ ν) 𝟙
  Hyp (sigma p q) (a , b) = Σ (Hyp p a) (λ _ → Hyp (q (info s p a)) b)
  Hyp (pi A p) f = (a : A) → Hyp (p a) (f a)

  Method : Set (ℓ ⊔ ν)
  Method =
    (i : Scheme.Index s) (a : Args s (shape (Scheme.rule s i)))
    → Hyp (shape (Scheme.rule s i)) a → P i (intro a)

  -- The argument a node at a code wraps.
  argument :
    {X : Set (ℓ ⊔ κ)} (p : Poly ℓ κ (Scheme.Data s) X)
    → Node s (inr (X , p)) → Args s p
  argument p (intro a) = a

  mutual
    ind : Method → (i : Scheme.Index s) (u : U s i) → P i u
    ind m i (intro a) = m i a (descend m (shape (Scheme.rule s i)) (intro a))

    -- The hypotheses at the recursive children of a node at a code.
    descend :
      Method → {X : Set (ℓ ⊔ κ)} (p : Poly ℓ κ (Scheme.Data s) X)
      (a : Node s (inr (X , p))) → Hyp p (argument p a)
    descend m (var i) (intro a) = lift (ind m i a)
    descend m (con A) (intro a) = lift ⋆
    descend m (sigma p q) (intro (a , b)) =
      descend m p (intro a) , descend m (q (info s p a)) (intro b)
    descend m (pi A p) (intro f) = λ a → descend m (p a) (intro (f a))

  calls :
    Method → {X : Set (ℓ ⊔ κ)} (p : Poly ℓ κ (Scheme.Data s) X)
    (a : Args s p) → Hyp p a
  calls m p a = descend m p (intro a)

  ind-β :
    (m : Method) (i : Scheme.Index s) (a : Args s (shape (Scheme.rule s i)))
    → ind m i (intro a) ＝ m i a (calls m (shape (Scheme.rule s i)) a)
  ind-β m i a = refl

------------------------------------------------------------------------
-- Root recovery

-- Induction into the arguments themselves returns each node's argument,
-- so introduction is an isomorphism at every index.

module _
  {ℓ κ : Level} (s : Scheme ℓ κ)
  where

  root : (i : Scheme.Index s) → U s i → Args s (shape (Scheme.rule s i))
  root = ind s (λ i _ → Args s (shape (Scheme.rule s i))) (λ i a _ → a)

  root-β :
    (i : Scheme.Index s) (a : Args s (shape (Scheme.rule s i)))
    → root i (intro a) ＝ a
  root-β i a = refl

  section :
    (i : Scheme.Index s) (u : U s i) → _＝_ {A = U s i} (intro (root i u)) u
  section i (intro a) = refl

------------------------------------------------------------------------
-- The universal family

-- The carriers with their readouts, as a family of
-- SPT.IR.Polynomial. Indexed.Comparison compares its ordinary
-- arguments with the arguments above.

family : {ℓ κ : Level} (s : Scheme ℓ κ) → Family ℓ κ (Scheme.Data s)
family s = record { carrier = U s ; readout = value s }
