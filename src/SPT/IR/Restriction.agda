{-# OPTIONS --safe --without-K #-}

module SPT.IR.Restriction where

-- Recursive inputs of shapes, and shapes over the restriction of an
-- indexed family (K , value) to a family Q over K: the pairs (k , q) with
-- q : Q k, decoded through K. The positions of a shape are the arities of
-- its δ nodes, with the point chosen at each (`Position`, `input`). An
-- argument over the restriction has heads over (K , value) with the same
-- output (`heads`, `heads-β`) and a point of Q at each input of its heads
-- (`children`); its inputs are those (`transfer`, `transfer-β`). It splits
-- into a layer, an argument over (K , value) with a point of Q at each
-- input (`Layer`, `split`), and layers join back (`join`, `join-split`,
-- `heads-join`, `position-join`, `input-join`); splitting a join gives the
-- layer back under extensionality over positions (`points`,
-- `children-points`, `points-η`, `split-join`). Generated is this at the
-- derivations, Mahlo.DS.Univalent.Construction at a generation.

open import SPT.Base
open import SPT.Foundation.Extensionality using (FunExt)

open import SPT.IR.Description using
  (DS; ι; σ; δ; Indexed; carrier; index; indexed; Shape; Mark)

------------------------------------------------------------------------
-- Recursive inputs of a shape

-- The positions of a shape are the arities of its δ nodes; the input at a
-- position is the point of the carrier chosen there.

Position :
  {s κ d e : Level} {D : Set d} {E : Set e} (S : DS {s = s} D E)
  (Z : Indexed κ D) → Shape S Z → Set s
Position {s} (ι e) Z _ = Lift s 𝟘
Position (σ A H) Z (a , z) = Position (H a) Z z
Position (δ A H) Z (f , z) = A ⊎ Position (H (λ x → index Z (f x))) Z z

input :
  {s κ d e : Level} {D : Set d} {E : Set e} (S : DS {s = s} D E)
  (Z : Indexed κ D) (z : Shape S Z) → Position S Z z → carrier Z
input (ι e) Z _ (lift ())
input (σ A H) Z (a , z) p = input (H a) Z z p
input (δ A H) Z (f , z) (inl x) = f x
input (δ A H) Z (f , z) (inr p) = input (H (λ x → index Z (f x))) Z z p

------------------------------------------------------------------------
-- Heads and children

-- The heads forget the points of Q; the decodings agree by computation,
-- since the restriction decodes through K. The positions of an argument
-- are those of its heads, and its input at a position is the head there
-- with its child.

module _
  {s κ q d : Level} {D : Set d} {K : Set κ} (value : K → D)
  (Q : K → Set q)
  where

  heads :
    {e : Level} {E : Set e} (S : DS {s = s} D E)
    → Shape S (indexed (Σ K Q) (λ w → value (pr₁ w)))
    → Shape S (indexed K value)
  heads (ι x) _ = lift ⋆
  heads (σ A H) (a , z) = a , heads (H a) z
  heads (δ A H) (f , z) =
    (λ x → pr₁ (f x)) , heads (H (λ x → value (pr₁ (f x)))) z

  children :
    {e : Level} {E : Set e} (S : DS {s = s} D E)
    (z : Shape S (indexed (Σ K Q) (λ w → value (pr₁ w))))
    (p : Position S (indexed K value) (heads S z))
    → Q (input S (indexed K value) (heads S z) p)
  children (ι x) _ (lift ())
  children (σ A H) (a , z) p = children (H a) z p
  children (δ A H) (f , z) (inl x) = pr₂ (f x)
  children (δ A H) (f , z) (inr p) =
    children (H (λ x → value (pr₁ (f x)))) z p

  heads-β :
    {e : Level} {E : Set e} (S : DS {s = s} D E)
    (z : Shape S (indexed (Σ K Q) (λ w → value (pr₁ w))))
    → Mark S (indexed K value) (heads S z)
      ＝ Mark S (indexed (Σ K Q) (λ w → value (pr₁ w))) z
  heads-β (ι x) _ = refl
  heads-β (σ A H) (a , z) = heads-β (H a) z
  heads-β (δ A H) (f , z) = heads-β (H (λ x → value (pr₁ (f x)))) z

  transfer :
    {e ν : Level} {E : Set e} (P : Σ K Q → Set ν) (S : DS {s = s} D E)
    (z : Shape S (indexed (Σ K Q) (λ w → value (pr₁ w))))
    → ((p : Position S (indexed K value) (heads S z))
      → P (input S (indexed K value) (heads S z) p , children S z p))
    → (p : Position S (indexed (Σ K Q) (λ w → value (pr₁ w))) z)
    → P (input S (indexed (Σ K Q) (λ w → value (pr₁ w))) z p)
  transfer P (ι x) z h (lift ())
  transfer P (σ A H) (a , z) h p = transfer P (H a) z h p
  transfer P (δ A H) (f , z) h (inl x) = h (inl x)
  transfer P (δ A H) (f , z) h (inr p) =
    transfer P (H (λ x → value (pr₁ (f x)))) z (λ q → h (inr q)) p

  transfer-β :
    {e ν : Level} {E : Set e} (P : Σ K Q → Set ν) (F : (w : Σ K Q) → P w)
    (S : DS {s = s} D E)
    (z : Shape S (indexed (Σ K Q) (λ w → value (pr₁ w))))
    (p : Position S (indexed (Σ K Q) (λ w → value (pr₁ w))) z)
    → transfer P S z
        (λ q → F (input S (indexed K value) (heads S z) q , children S z q))
        p
      ＝ F (input S (indexed (Σ K Q) (λ w → value (pr₁ w))) z p)
  transfer-β P F (ι x) z (lift ())
  transfer-β P F (σ A H) (a , z) p = transfer-β P F (H a) z p
  transfer-β P F (δ A H) (f , z) (inl x) = refl
  transfer-β P F (δ A H) (f , z) (inr p) =
    transfer-β P F (H (λ x → value (pr₁ (f x)))) z p

------------------------------------------------------------------------
-- Layers, splitting and joining

-- A layer is an argument over (K , value) with a point of Q at each of
-- its inputs. A join pairs each input with its point; its heads are the
-- layer's argument, its inputs that argument's inputs with their points,
-- and joining a split gives the argument back, all by induction on the
-- description with no extensionality.

  Layer : {e : Level} {E : Set e} → DS {s = s} D E → Set (s ⊔ κ ⊔ q)
  Layer S =
    Σ (Shape S (indexed K value))
      (λ a → (p : Position S (indexed K value) a)
        → Q (input S (indexed K value) a p))

  split :
    {e : Level} {E : Set e} (S : DS {s = s} D E)
    → Shape S (indexed (Σ K Q) (λ w → value (pr₁ w))) → Layer S
  split S z = heads S z , children S z

  join :
    {e : Level} {E : Set e} (S : DS {s = s} D E)
    → Layer S → Shape S (indexed (Σ K Q) (λ w → value (pr₁ w)))
  join (ι x) l = lift ⋆
  join (σ A H) ((x , a) , qs) = x , join (H x) (a , qs)
  join (δ A H) ((f , a) , qs) =
    (λ x → f x , qs (inl x)) ,
    join (H (λ x → value (f x))) (a , (λ p → qs (inr p)))

  join-split :
    {e : Level} {E : Set e} (S : DS {s = s} D E)
    (z : Shape S (indexed (Σ K Q) (λ w → value (pr₁ w))))
    → join S (split S z) ＝ z
  join-split (ι x) z = refl
  join-split (σ A H) (a , z) = ap (λ w → a , w) (join-split (H a) z)
  join-split (δ A H) (f , z) =
    ap (λ w → f , w) (join-split (H (λ x → value (pr₁ (f x)))) z)

  heads-join :
    {e : Level} {E : Set e} (S : DS {s = s} D E) (l : Layer S)
    → heads S (join S l) ＝ pr₁ l
  heads-join (ι x) l = refl
  heads-join (σ A H) ((x , a) , qs) =
    ap (λ b → x , b) (heads-join (H x) (a , qs))
  heads-join (δ A H) ((f , a) , qs) =
    ap (λ b → f , b)
      (heads-join (H (λ x → value (f x))) (a , (λ p → qs (inr p))))

  position-join :
    {e : Level} {E : Set e} (S : DS {s = s} D E) (l : Layer S)
    → Position S (indexed (Σ K Q) (λ w → value (pr₁ w))) (join S l)
    → Position S (indexed K value) (pr₁ l)
  position-join (ι x) l (lift ())
  position-join (σ A H) ((x , a) , qs) p = position-join (H x) (a , qs) p
  position-join (δ A H) ((f , a) , qs) (inl x) = inl x
  position-join (δ A H) ((f , a) , qs) (inr p) =
    inr
      (position-join (H (λ x → value (f x))) (a , (λ p′ → qs (inr p′))) p)

  input-join :
    {e : Level} {E : Set e} (S : DS {s = s} D E) (l : Layer S)
    (p : Position S (indexed (Σ K Q) (λ w → value (pr₁ w))) (join S l))
    → input S (indexed (Σ K Q) (λ w → value (pr₁ w))) (join S l) p
      ＝ ( input S (indexed K value) (pr₁ l) (position-join S l p)
         , pr₂ l (position-join S l p))
  input-join (ι x) l (lift ())
  input-join (σ A H) ((x , a) , qs) p = input-join (H x) (a , qs) p
  input-join (δ A H) ((f , a) , qs) (inl x) = refl
  input-join (δ A H) ((f , a) , qs) (inr p) =
    input-join (H (λ x → value (f x))) (a , (λ p′ → qs (inr p′))) p

------------------------------------------------------------------------
-- Splitting a join

-- The points of a δ layer over f, assembled from xs at the arity and ys
-- after it, are the children of the joined argument, and a layer's own
-- points reassemble to themselves. Extensionality for families over
-- positions then gives split (join l) ＝ l.

  points :
    {e : Level} {E : Set e}
    (A : Set s) (H : (A → D) → DS {s = s} D E) (f : A → K)
    (b : Shape (H (λ x → value (f x))) (indexed K value))
    → ((x : A) → Q (f x))
    → ((p : Position (H (λ x → value (f x))) (indexed K value) b)
      → Q (input (H (λ x → value (f x))) (indexed K value) b p))
    → (p : Position (δ A H) (indexed K value) (f , b))
    → Q (input (δ A H) (indexed K value) (f , b) p)
  points A H f b xs ys (inl x) = xs x
  points A H f b xs ys (inr p) = ys p

  children-points :
    {e : Level} {E : Set e}
    (A : Set s) (H : (A → D) → DS {s = s} D E) (f : A → K)
    (xs : (x : A) → Q (f x))
    (J : Shape (H (λ x → value (f x)))
      (indexed (Σ K Q) (λ w → value (pr₁ w))))
    (p : Position (δ A H) (indexed K value)
      (f , heads (H (λ x → value (f x))) J))
    → children (δ A H) ((λ x → f x , xs x) , J) p
      ＝ points A H f (heads (H (λ x → value (f x))) J) xs
          (children (H (λ x → value (f x))) J) p
  children-points A H f xs J (inl x) = refl
  children-points A H f xs J (inr p) = refl

  points-η :
    {e : Level} {E : Set e}
    (A : Set s) (H : (A → D) → DS {s = s} D E) (f : A → K)
    (a : Shape (H (λ x → value (f x))) (indexed K value))
    (xs : (p : Position (δ A H) (indexed K value) (f , a))
      → Q (input (δ A H) (indexed K value) (f , a) p))
    (p : Position (δ A H) (indexed K value) (f , a))
    → points A H f a (λ x → xs (inl x)) (λ r → xs (inr r)) p ＝ xs p
  points-η A H f a xs (inl x) = refl
  points-η A H f a xs (inr r) = refl

  split-join :
    {e : Level} {E : Set e}
    → ((A : Set s) (Y : A → Set q) → FunExt A Y)
    → (S : DS {s = s} D E) (l : Layer S) → split S (join S l) ＝ l
  split-join extensionality (ι x) (a , xs) =
    ap (λ h → lift ⋆ , h)
      (extensionality (Lift s 𝟘)
        (λ p → Q (input (ι x) (indexed K value) (lift ⋆) p))
        (children (ι x) (lift ⋆)) xs
        (λ p → 𝟘-elim (lower p)))
  split-join extensionality (σ A H) ((x , a) , xs) =
    ap (λ l → (x , pr₁ l) , pr₂ l) (split-join extensionality (H x) (a , xs))
  split-join extensionality (δ A H) ((f , a) , xs) =
    let first = λ (x : A) → xs (inl x)
        rest =
          λ (p : Position (H (λ x → value (f x))) (indexed K value) a)
            → xs (inr p)
        J = join (H (λ x → value (f x))) (a , rest)
    in
    ap (λ h → (f , heads (H (λ x → value (f x))) J) , h)
      (extensionality
        (Position (δ A H) (indexed K value)
          (f , heads (H (λ x → value (f x))) J))
        (λ p → Q
          (input (δ A H) (indexed K value)
            (f , heads (H (λ x → value (f x))) J) p))
        (children (δ A H) ((λ x → f x , first x) , J))
        (points A H f (heads (H (λ x → value (f x))) J) first
          (children (H (λ x → value (f x))) J))
        (children-points A H f first J))
    ∙ ap (λ l → (f , pr₁ l) , points A H f (pr₁ l) first (pr₂ l))
        (split-join extensionality (H (λ x → value (f x))) (a , rest))
    ∙ ap (λ h → (f , a) , h)
        (extensionality
          (Position (δ A H) (indexed K value) (f , a))
          (λ p → Q (input (δ A H) (indexed K value) (f , a) p))
          (points A H f a first rest) xs
          (points-η A H f a xs))
